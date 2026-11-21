//! The environment of a specification: who controls what each actor does.

use trion_language::reading::{ConstraintKind, Model};
use trion_language::SpecRef;
use trion_solver::{Atom, Formula};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

/// Who controls what each actor does.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct Control {
    pub environment: BTreeSet<String>,
    pub system: BTreeSet<String>,
    /// The terms that a declaration gives to the environment. A situation
    /// fixes each of them; an actor that is only inferred to belong to the
    /// environment has no such standing.
    #[serde(skip)]
    pub declared_environment: BTreeSet<String>,
    /// The actors that a declaration gives to the system. Only what these
    /// actors do is the system's by responsibility: a condition about it is
    /// a condition inside the guarantee. An actor that is only inferred to
    /// belong to the system has no such standing, and a condition about it
    /// is read as the situation shows it.
    #[serde(skip)]
    pub declared_system: BTreeSet<String>,
    #[serde(skip)]
    pub(super) system_individual_types: BTreeSet<String>,
    #[serde(skip)]
    pub(super) conflicting_carriers: BTreeMap<String, Vec<SpecRef>>,
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

/// The actors of the system of a document that declares none: each actor
/// whose action, or a measure of it, a statement with normative force
/// speaks about, unless the environment controls it.
/// The actors of the system: those that the document declares, or, where
/// it declares none, those whose actions its requirements speak about.
pub(super) fn system_actors(model: &Model, control: &Control, described: &dyn Fn(&trion_language::reading::Constraint) -> bool) -> BTreeSet<String> {
    if control.declared_system.is_empty() { undeclared_system(model, control, described) } else { control.declared_system.clone() }
}

/// Whether a statement constrains what only the environment is responsible
/// for: each action that its guarantee speaks about is done by an actor
/// that is not the system's, and it speaks about one. Such a statement is
/// an assumption, normative or not (AGENTS.md, rule 2).
pub(super) fn of_environment(constraint: &trion_language::reading::Constraint, actors: &BTreeSet<String>) -> bool {
    let (mut acts, mut foreign) = (0, true);
    constraint.guarantee.atoms(true, &mut |atom, _| {
        if let trion_solver::Atom::Act { key } | trion_solver::Atom::Forbid { key } | trion_solver::Atom::Discouraged { key } = atom {
            let key = key.strip_prefix("disposed to ").unwrap_or(key);
            if let Some((actor, _)) = key.split_once('|') {
                acts += 1;
                foreign &= !actors.contains(actor);
            }
        }
    });
    acts > 0 && foreign
}

pub(super) fn undeclared_system(model: &Model, control: &Control, described: &dyn Fn(&trion_language::reading::Constraint) -> bool) -> BTreeSet<String> {
    let mut actors = BTreeSet::new();
    for c in model.constraints.iter().filter(|c| matches!(c.kind, ConstraintKind::Spec | ConstraintKind::Permission)) {
        c.guarantee.atoms(true, &mut |atom, _| {
            for symbol in atom.symbols() {
                actors.extend(actor_of(symbol).map(str::to_string));
            }
        });
    }
    // The holder of a state that a requirement requires, and not only
    // reads in a condition, is the system's as well: `The room type shall be
    // secret` makes the room type something that the system keeps.
    for c in model.constraints.iter().filter(|c| matches!(c.kind, ConstraintKind::Spec) && !described(c)) {
        required_states(&c.guarantee, &mut actors);
    }
    actors.retain(|actor| !control.environment.contains(actor));
    actors
}

/// The attributes of the states that a guarantee requires: those that it
/// asserts or denies in every case (`shall be secret`, `shall not be
/// open`), and not those of a condition or of an alternative (`only when`
/// reads as `C ∨ forbidden`).
fn required_states(formula: &trion_solver::Formula, out: &mut BTreeSet<String>) {
    use trion_solver::{Atom, Formula};
    match formula {
        Formula::Atom(Atom::Val { attr, .. }) => {
            out.insert(attr.clone());
        }
        Formula::Not(inner) if matches!(**inner, Formula::Atom(Atom::Val { .. })) => required_states(inner, out),
        Formula::And(parts) => parts.iter().for_each(|part| required_states(part, out)),
        Formula::Implies(_, then) => required_states(then, out),
        _ => {}
    }
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
                out.declared_environment.insert(actor.clone());
                out.environment.insert(actor);
            } else {
                out.declared_system.insert(actor.clone());
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
    // A grounded actor keeps the declared responsibility of its carrier.
    if let Some(individuals) = &model.individuals {
        let declared_carriers: BTreeSet<_> = set.packages.iter()
            .flat_map(|package| &package.documents)

            .flat_map(|doc| {
                let scoped = lex.in_document(doc);
                doc.individuals.iter().map(move |decl| scoped.resolve(&scoped.canon(&decl.name)))
            })
            .collect();
        let carriers: BTreeMap<&str, &str> = individuals.types.iter()
            .map(|(name, carrier)| (name.as_str(), carrier.as_str()))
            .collect();
        let mut boundaries = BTreeMap::<&str, Vec<(bool, SpecRef)>>::new();
        for doc in set.packages.iter().flat_map(|p| &p.documents) {
            let scoped = lex.in_document(doc);
            for decl in &doc.controls {
                let name = scoped.resolve(&scoped.canon(&decl.name));
                if let Some(&carrier) = carriers.get(name.as_str()).filter(|_| declared_carriers.contains(&name)) {
                    let at = SpecRef::point(&decl.file, decl.line, &format!("{} {}", decl.by, decl.name));
                    let environment = decl.by == "environment";
                    boundaries.entry(carrier).or_default().push((environment, at));
                    if !environment {
                        out.system_individual_types.insert(name);
                    }
                }
            }
        }
        for (carrier, declarations) in boundaries {
            let environment = declarations[0].0;
            if declarations.iter().any(|(by_environment, _)| *by_environment != environment) {
                out.conflicting_carriers.insert(carrier.to_string(), declarations.into_iter().map(|(_, at)| at).collect());
                continue;
            }
            let by = if environment {
                (&mut out.declared_environment, &mut out.environment)
            } else {
                (&mut out.declared_system, &mut out.system)
            };
            for slot in 1..=individuals.scope {
                let actor = format!("{carrier}#{slot}");
                by.0.insert(actor.clone());
                by.1.insert(actor);
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
            out.declared_system.insert(actor.clone());
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

/// The terms that the system is responsible for: each action of an actor
/// that a declaration gives to the system, each event of such an action,
/// and each attribute of such an actor. A term that a declaration gives to
/// the environment is not one.
pub(super) fn system_terms(model: &Model, control: &Control, events: &BTreeMap<String, String>, given: &BTreeSet<String>) -> BTreeSet<String> {
    let mut symbols: BTreeSet<String> = BTreeSet::new();
    for constraint in &model.constraints {
        for formula in [&constraint.assume, &constraint.guarantee] {
            formula.atoms(true, &mut |atom, _| symbols.extend(atom.symbols().into_iter().map(str::to_string)));
        }
    }
    for axiom in &model.background {
        axiom.atoms(true, &mut |atom, _| symbols.extend(atom.symbols().into_iter().map(str::to_string)));
    }
    let of_system = |actor: &str| control.declared_system.contains(actor) && !control.declared_environment.contains(actor);
    let owned = |name: &str| control.declared_system.iter().any(|actor| of_system(actor) && (name == actor || name.starts_with(&format!("{actor} "))));
    symbols
        .into_iter()
        .filter(|symbol| !given.contains(symbol))
        .filter(|symbol| match actor_of(symbol) {
            Some(actor) => of_system(actor),
            None => events.get(symbol).and_then(|action| actor_of(action)).map_or_else(|| owned(symbol), of_system),
        })
        .collect()
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

