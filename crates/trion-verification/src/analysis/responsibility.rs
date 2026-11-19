//! Who answers for what: the statements of a set as their authors wrote
//! them (a requirement, a recommendation or a description), and the terms
//! that the environment fixes and that the system is responsible for.

use super::*;

/// The statements of a set, by the reference of the model that points at them.
pub(super) struct Authored<'a> {
    specs: Vec<(&'a Spec, &'a Document, String)>,
}

impl<'a> Authored<'a> {
    pub(super) fn new(set: &'a SpecSet, lex: &'a Lexicon) -> Self {
        let mut specs = Vec::new();
        for pkg in &set.packages {
            for doc in &pkg.documents {
                for spec in &doc.specs {
                    let display = if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) };
                    specs.push((spec, doc, display));
                }
            }
        }
        let _ = lex;
        Self { specs }
    }

    /// The statement a reference of the model points at or into.
    pub(super) fn owner(&self, r: &SpecRef) -> Option<(&'a Spec, &'a Document)> {
        self.specs.iter().find(|(s, _, id)| s.file == r.file && (r.id == *id || r.id.strip_prefix(id.as_str()).is_some_and(|rest| rest.starts_with('/')))).map(|(s, d, _)| (*s, *d))
    }

    /// `true` for a `should` statement: a recommendation is no hard constraint.
    pub(super) fn is_recommendation(&self, c: &Constraint) -> bool {
        c.refs.first().and_then(|r| self.owner(r)).is_some_and(|(s, _)| matches!(s.sentence.core, Core::Deontic { modal: Modal::Should, .. }))
    }

    /// `true` for a statement with no modal force: it says how things are,
    /// and no system has to make it so.
    pub(super) fn is_description(&self, c: &Constraint) -> bool {
        c.refs.first().and_then(|r| self.owner(r)).is_some_and(|(s, _)| !matches!(s.sentence.core, Core::Deontic { .. }))
    }
}

/// What the responsibility of the system and of the environment reads besides the model.
pub(super) struct Situated {
    /// The action behind each event.
    pub(super) events: BTreeMap<String, String>,
    /// The terms that the environment controls: a situation fixes them, and
    /// no response of the system changes them.
    pub(super) given: BTreeSet<String>,
    /// The terms that the system is responsible for: the actions and the
    /// events of the actors of the system. A condition about them is a
    /// condition inside the guarantee, which the system may avoid.
    pub(super) system: BTreeSet<String>,
}

impl Situated {
    pub(super) fn of(model: &Model, control: &environment::Control) -> Self {
        let mut given = control.declared_environment.clone();
        // Which individuals there are and how they are related is given: a
        // response chooses among the individuals of the domain, and makes
        // none of them one that it may choose.
        for entry in model.individuals.iter().flat_map(|individuals| &individuals.atoms) {
            if matches!(entry.fact, trion_language::reading::Fact::Kind { .. } | trion_language::reading::Fact::Related { .. }) {
                given.extend(entry.atom.symbols().into_iter().map(str::to_string));
            }
        }
        let events = environment::event_actions(model);
        let system = environment::system_terms(model, control, &events, &given);
        Self { events, given, system }
    }

    /// `true` when a formula speaks about a term of the system.
    pub(super) fn about_system(&self, formula: &Formula) -> bool {
        let mut found = false;
        formula.atoms(true, &mut |atom, _| found |= atom.symbols().into_iter().any(|symbol| self.system.contains(symbol)));
        found
    }

    /// Put a condition about the response in the guarantee. Conjuncts
    /// fixed by the situation stay in the assumption. A mixed disjunction
    /// stays together so that factoring the guard preserves its meaning.
    pub(super) fn contract(&self, guard: Formula, response: Formula, configured: &BTreeSet<String>) -> (Formula, Formula) {
        let mut conditions = vec![guard];
        let mut given = Vec::new();
        let mut internal = Vec::new();
        while let Some(condition) = conditions.pop() {
            if let Formula::And(parts) = condition {
                conditions.extend(parts.into_iter().rev());
                continue;
            }
            let mut system = false;
            condition.atoms(true, &mut |atom, _| {
                system |= !matches!(atom, trion_solver::Atom::Config { .. })
                    && atom.symbols().into_iter().any(|symbol| self.system.contains(symbol) && !configured.contains(symbol));
            });
            if system {
                internal.push(condition);
            } else {
                given.push(condition);
            }
        }
        let assumption = simplify(Formula::And(given));
        let guarantee = if internal.is_empty() {
            response
        } else {
            Formula::implies(simplify(Formula::And(internal)), response)
        };
        (assumption, guarantee)
    }
}
