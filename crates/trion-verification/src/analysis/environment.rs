//! The environment of a specification: who controls what each actor does,
//! and each response that the system cannot give because it would have to
//! come before something that the environment decides.

use trion_language::SpecRef;
use trion_language::reading::{ConstraintKind, Model};
use trion_solver::{Atom, Formula};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

/// A guarantee that the system cannot keep against every behaviour of the environment.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Unrealizable {
    pub statement: SpecRef,
    pub message: String,
}

/// Who controls what each actor does.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct Control {
    pub environment: BTreeSet<String>,
    pub system: BTreeSet<String>,
}

fn actor_of(key: &str) -> Option<&str> {
    key.split_once('|').map(|(actor, _)| actor)
}

/// The action behind each event: `Event(user send message)` is the action `user|send message`.
pub(super) fn event_actions(model: &Model) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for axiom in &model.background {
        if let Formula::Implies(action, event) = axiom {
            if let (Formula::Atom(Atom::Act { key }), Formula::Atom(Atom::Event { key: text })) = (&**action, &**event) {
                out.insert(text.clone(), key.clone());
            }
        }
    }
    out
}

/// Decides who controls each actor.
///
/// A declaration decides first. Otherwise an actor that a statement obliges
/// to act is part of the system, and an actor whose action another statement
/// waits for, and that no statement obliges to act, is part of the environment.
pub(super) fn control(set: &trion_language::document::SpecSet, model: &Model, lex: &trion_language::reading::Lexicon) -> Control {
    use trion_language::syntax::ast::{ClauseBody, NpGroup};
    let mut out = Control::default();
    let mut obliged = BTreeSet::new();
    let mut awaited = BTreeSet::new();
    for c in model.constraints.iter().filter(|c| c.kind == ConstraintKind::Spec) {
        c.guarantee.atoms(true, &mut |atom, positive| {
            if let (Atom::Act { key }, true) = (atom, positive) {
                obliged.extend(actor_of(key).map(str::to_string));
            }
        });
    }
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let scoped = lex.in_document(doc);
        for decl in &doc.controls {
            let actor = scoped.resolve(&scoped.canon(&decl.name));
            if decl.by == "environment" {
                out.environment.insert(actor);
            } else {
                out.system.insert(actor);
            }
        }
        for spec in &doc.specs {
            let frames = &spec.sentence.frames;
            let clauses = frames.states.iter().map(|f| &f.clause).chain(frames.trigger.iter().map(|t| &t.clause)).flat_map(|g| &g.items);
            for clause in clauses.filter(|c| matches!(c.body, ClauseBody::Verbal { .. })) {
                let subjects: Vec<&trion_language::syntax::ast::Np> = match &clause.subject {
                    NpGroup::Single(np) => vec![np],
                    NpGroup::Coordinated { items, .. } => items.iter().collect(),
                };
                awaited.extend(subjects.into_iter().map(|np| trion_language::reading::subject_key(np, &scoped)));
            }
        }
    }
    // A declaration reaches the term of the same name in each namespace that
    // uses the declaring namespace, unless that namespace declares its own.
    let local = |actor: &str| actor.rsplit("::").next().unwrap_or(actor).to_string();
    let owner = |actor: &str| actor.rsplit_once("::").map_or(String::new(), |(ns, _)| ns.to_string());
    let mut uses: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut declared: Vec<(String, String, bool)> = Vec::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        uses.entry(doc.namespace.clone()).or_default().extend(doc.imports.iter().map(|i| i.namespace.clone()));
        let scoped = lex.in_document(doc);
        declared.extend(doc.controls.iter().map(|decl| (doc.namespace.clone(), local(&scoped.canon(&decl.name)), decl.by == "environment")));
    }
    let inherited: Vec<(String, bool)> = obliged
        .iter()
        .chain(&awaited)
        .filter(|actor| !out.environment.contains(*actor) && !out.system.contains(*actor))
        .filter_map(|actor| {
            let reachable = uses.get(&owner(actor));
            declared.iter().find(|(namespace, name, _)| *name == local(actor) && reachable.is_some_and(|r| r.contains(namespace))).map(|(_, _, by_environment)| (actor.clone(), *by_environment))
        })
        .collect();
    for (actor, by_environment) in inherited {
        if by_environment {
            out.environment.insert(actor);
        } else {
            out.system.insert(actor);
        }
    }
    for actor in obliged {
        if !out.environment.contains(&actor) {
            out.system.insert(actor);
        }
    }
    for actor in awaited {
        if !out.system.contains(&actor) {
            out.environment.insert(actor);
        }
    }
    out
}

/// For each action of the environment that has an event: the event occurs
/// only when the action is done. The model states the other direction.
pub(super) fn environment_events(model: &Model, control: &Control) -> Vec<Formula> {
    event_actions(model)
        .into_iter()
        .filter(|(_, action)| actor_of(action).is_some_and(|a| control.environment.contains(a)))
        .map(|(event, action)| Formula::implies(Formula::Atom(Atom::Event { key: event }), Formula::Atom(Atom::Act { key: action })))
        .collect()
}

/// Finds each response that must be complete before something the
/// environment decides: the system would need to know what has not happened.
pub(super) fn unrealizable(model: &Model, control: &Control) -> Vec<Unrealizable> {
    let mut out = Vec::new();
    for obligation in &model.temporal {
        for response in &obligation.responses {
            for reference in response.references.iter().filter(|r| r.relation == "before" && r.related_kind == "event") {
                let event = reference.related.trim_start_matches("Event(").trim_end_matches(')');
                // Only an actor that the environment is known to control makes the order impossible to keep.
                let Some(actor) = control.environment.iter().find(|a| event.starts_with(&format!("{a} "))) else { continue };
                let name = actor.rsplit("::").next().unwrap_or(actor);
                out.push(Unrealizable {
                    statement: obligation.statement.clone(),
                    message: format!("`{}` requires a response before `{event}`, and the environment decides when `{name}` acts: whatever moment the system chooses, the environment can act before it, so no system keeps this guarantee; require the response after an event that the system observes", obligation.statement.id),
                });
            }
        }
    }
    out
}

/// What a specification says about its environment.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct Findings {
    pub control: Control,
    pub unrealizable: Vec<Unrealizable>,
}

