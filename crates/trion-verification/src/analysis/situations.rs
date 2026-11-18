//! The situations of a specification, and whether each has a response.
//!
//! The statements without normative force say which situations can occur. A
//! specification is consistent only when, in each such situation, the
//! guarantees of the contracts whose assumptions hold can be kept together.
//! That a behaviour keeps every contract is less: a contract is kept
//! wherever its assumption does not hold.
//!
//! A situation is read at the level of the contracts: the assumption and
//! the guarantee of a statement, without the moments of a trace. Which
//! moment a response completes at, and what a deadline or an order adds,
//! belongs to one activation of a statement and is decided over the trace.
//!
//! A term is a *response term* when the guarantee of a statement with
//! normative force speaks about it: the action that the statement requires
//! or forbids, the attribute whose state it requires. Every other term is
//! named by a statement is *given*: a situation fixes it, and no response
//! changes it. Two kinds of terms go with the response by rule. The event
//! of an action is the occurrence of the action. A term that no statement
//! names is made by the reading (the time of a moment, the count of an
//! action, the time of a completion): a situation is told in the terms of
//! the statements, so it fixes none of them.
//!
//! The claim is one formula with a universal and an existential quantifier,
//! which the obligation of consistency states and `trioc` decides without
//! listing the situations: for every valuation of all terms that the descriptions
//! allow, read as what the conditions see, some valuation of the response
//! terms keeps the descriptions and the guarantee of each contract whose
//! condition holds in the first valuation. A condition can read a response
//! term, as `When the door is open` does where another statement requires
//! the door to become closed: the condition reads the term as the situation
//! shows it, and the guarantee speaks of the term as the response makes it.
//! So a response cannot escape a guarantee by making its condition false,
//! and a statement that changes what its condition reads contradicts nothing.
//!
//! A term that a declaration gives to the environment (`environment load`)
//! is given even where a guarantee speaks about it. A response may then
//! have to follow the situation: `the capacity shall be greater than the
//! load` has no constant response, and the response `capacity := load +
//! 0.001` answers every load ([`trion_solver::for_all_exists`]).

use std::collections::{BTreeMap, BTreeSet};
use trion_language::reading::Model;
use trion_solver::{Atom, Formula};

/// The mark of a term as a condition sees it, apart from what a response makes of it.
const SEEN: char = '?';

/// A formula with each response term replaced by the term as a condition sees it.
pub(crate) fn seen(formula: &Formula, response: &dyn Fn(&str) -> bool) -> Formula {
    let mark = |name: String| if response(&name) { format!("{SEEN}{name}") } else { name };
    formula.clone().map_atoms(&|atom| match atom {
        Atom::Dom { attr, value } => Atom::Dom { attr: mark(attr), value },
        Atom::Val { attr, value } => Atom::Val { attr: mark(attr), value },
        Atom::Act { key } => Atom::Act { key: mark(key) },
        Atom::Forbid { key } => Atom::Forbid { key: mark(key) },
        Atom::Discouraged { key } => Atom::Discouraged { key: mark(key) },
        Atom::Event { key } => Atom::Event { key: mark(key) },
        Atom::Config { key } => Atom::Config { key: mark(key) },
        Atom::Role { subject, role } => Atom::Role { subject: mark(subject), role },
        Atom::Num { attr, unit, cmp, n } => Atom::Num { attr: mark(attr), unit, cmp, n },
        Atom::Lin { terms, unit, cmp, n } => Atom::Lin { terms: terms.into_iter().map(|(attr, coefficient)| (mark(attr), coefficient)).collect(), unit, cmp, n },
        Atom::Before { first, second } => Atom::Before { first: mark(first), second: mark(second) },
        Atom::Rel { name, args } => Atom::Rel { name: mark(name), args },
    })
}

/// Which terms a response chooses: what a guarantee with normative force
/// speaks about, the terms of the system, and the terms that the reading
/// makes and no statement names. A term that the environment controls is
/// given whatever speaks about it.
pub(crate) struct Responsibility {
    terms: BTreeSet<String>,
    named: BTreeSet<String>,
    given: BTreeSet<String>,
    system: BTreeSet<String>,
    /// The actors of the system, where responsibility follows the actor:
    /// an action is chosen exactly when its actor is one of them, and an
    /// event exactly when it is the occurrence of such an action.
    boundary: Option<Boundary>,
}

struct Boundary {
    actors: BTreeSet<String>,
    /// The action behind each event that is the occurrence of one.
    events: BTreeMap<String, String>,
    /// Every event that the model names.
    occurrences: BTreeSet<String>,
    /// Every attribute that has states: its name begins with its holder.
    states: BTreeSet<String>,
}

impl Responsibility {
    pub(crate) fn of(model: &Model, events: &BTreeMap<String, String>, given: &BTreeSet<String>, system: &BTreeSet<String>, normative: &dyn Fn(usize) -> bool) -> Self {
        let count = model.constraints.len();
        // The response terms: what a guarantee with normative force speaks
        // about, with what the reading makes of that guarantee. `The room shall
        // be archived` requires an action, and its meaning says that the room
        // is archived then: the state of the room is part of the response.
        let stated: BTreeSet<&str> = (0..count).filter(|&i| normative(i)).filter_map(|i| model.constraints[i].refs.first()).map(|r| r.id.as_str()).collect();
        let mut terms: BTreeSet<String> = BTreeSet::new();
        for (i, c) in model.constraints.iter().enumerate() {
            if normative(i) || (c.kind.is_vocabulary() && c.refs.first().is_some_and(|r| stated.contains(r.id.as_str()))) {
                c.guarantee.atoms(true, &mut |atom, _| terms.extend(atom.symbols().into_iter().map(str::to_string)));
            }
        }
        // An event is the occurrence of its action: it is a response where the action is one.
        terms.extend(events.iter().filter(|(_, action)| terms.contains(action.as_str())).map(|(event, _)| event.clone()).collect::<Vec<_>>());
        // A situation is told in the terms of the statements. A term that no
        // statement names is made by the reading, as the count of an action is:
        // it comes with the behaviour, and no situation fixes it.
        let mut named: BTreeSet<String> = BTreeSet::new();
        for c in model.constraints.iter().filter(|c| !c.kind.is_axiom()) {
            for formula in [&c.assume, &c.guarantee] {
                formula.atoms(true, &mut |atom, _| named.extend(atom.symbols().into_iter().map(str::to_string)));
            }
        }
        Self { terms, named, given: given.clone(), system: system.clone(), boundary: None }
    }

    /// The same responsibility, with what an actor does decided by whether
    /// the actor is one of `actors`: the rule of the language that a
    /// document declares which actors are the system.
    pub(crate) fn following(mut self, model: &Model, unrolled: &[Formula], events: &BTreeMap<String, String>, actors: &BTreeSet<String>) -> Self {
        let mut occurrences = BTreeSet::new();
        let mut states = BTreeSet::new();
        let mut collect = |formula: &Formula| {
            formula.atoms(true, &mut |atom, _| match atom {
                trion_solver::Atom::Event { key } => {
                    occurrences.insert(untimed(key).to_string());
                }
                trion_solver::Atom::Val { attr, .. } | trion_solver::Atom::Dom { attr, .. } => {
                    states.insert(untimed(attr).to_string());
                }
                _ => {}
            })
        };
        for formula in model.background.iter().chain(model.constraints.iter().flat_map(|c| [&c.assume, &c.guarantee])).chain(unrolled) {
            collect(formula);
        }
        // An alias names an actor of the system as well: the reading states
        // `Act(service …) ↔ Act(API …)`, and the two actors are one.
        let mut actors = actors.clone();
        let pairs = aliased_actors(model);
        loop {
            let before = actors.len();
            for (a, b) in &pairs {
                if actors.contains(a) {
                    actors.insert(b.clone());
                }
                if actors.contains(b) {
                    actors.insert(a.clone());
                }
            }
            if actors.len() == before {
                break;
            }
        }
        self.boundary = Some(Boundary { actors, events: events.clone(), occurrences, states });
        self
    }

    /// Whose a term is when its actor decides: `Some(true)` for the system,
    /// `Some(false)` for the environment, `None` for a term without an actor.
    pub(crate) fn by_actor(&self, term: &str) -> Option<bool> {
        let boundary = self.boundary.as_ref()?;
        // The time of the first occurrence in the rest of a trace is whose the occurrence is.
        if let Some(key) = ["first completion time in the rest of ", "first occurrence time in the rest of "].iter().find_map(|prefix| term.strip_prefix(prefix)) {
            return self.by_actor(key);
        }
        // That an action was performed, as `only` reads it, is the actor's.
        if let Some(action) = term.strip_prefix("performed ") {
            return self.by_actor(action);
        }
        // A step of a flow is reached by what the system does.
        if term.starts_with("reach ") && term.contains(" in ") {
            return Some(true);
        }
        let holds = |actor: &String| term == actor || term.strip_prefix(actor.as_str()).is_some_and(|rest| rest.starts_with(' '));
        // A state is its holder's: the system's when the holder is one of its
        // actors, the environment's otherwise (the room that the system must
        // archive is the system's, the door that nothing declares is not).
        if boundary.states.contains(term) && !term.contains('|') {
            return Some(boundary.actors.iter().any(holds));
        }
        // A disposition to an action is the holder's, as the action is.
        let action = match (boundary.events.get(term), term.strip_prefix("disposed to ")) {
            (Some(action), _) => action.as_str(),
            (None, Some(action)) => action,
            // An event is told `actor verb object`, as its action is `actor|verb object`.
            (None, None) if boundary.occurrences.contains(term) => return Some(boundary.actors.iter().any(|actor| term.strip_prefix(actor.as_str()).is_some_and(|rest| rest.starts_with(' ')))),
            (None, None) => term,
        };
        let (actor, _) = action.split_once('|')?;
        Some(boundary.actors.contains(actor))
    }

    /// A term that a response chooses. A term over a trace is the term at a
    /// moment, `key@3`, and is chosen when its term is.
    pub(crate) fn response(&self, symbol: &str) -> bool {
        if symbol.starts_with(SEEN) {
            return false;
        }
        let term = untimed(symbol);
        if let Some(own) = self.by_actor(term) {
            return own && !self.given.contains(term);
        }
        !self.given.contains(term) && (self.terms.contains(term) || !self.named.contains(term) || self.system.contains(term))
    }

    /// A response term that a condition reads as the situation shows it: a
    /// term of the system is read as the response makes it, since a
    /// condition about the system is a condition inside the guarantee.
    pub(crate) fn seen_apart(&self, symbol: &str) -> bool {
        self.response(symbol) && !self.system.contains(untimed(symbol)) && self.by_actor(untimed(symbol)) != Some(true)
    }
}

/// The actors that the background says are one: each `Act(x|v) ↔ Act(y|v)`
/// that an alias of the reading states gives the pair `(x, y)`.
fn aliased_actors(model: &Model) -> Vec<(String, String)> {
    let action = |formula: &Formula| match formula {
        Formula::Atom(Atom::Act { key }) => key.split_once('|').map(|(actor, rest)| (actor.to_string(), rest.to_string())),
        _ => None,
    };
    let mut out = Vec::new();
    for axiom in &model.background {
        let Formula::And(parts) = axiom else { continue };
        let [Formula::Implies(a, b), Formula::Implies(c, d)] = parts.as_slice() else { continue };
        if a != d || b != c {
            continue;
        }
        if let (Some((x, v)), Some((y, w))) = (action(a), action(b)) {
            if v == w && x != y {
                out.push((x, y));
            }
        }
    }
    out
}

/// A term without the moment that a trace gives it: `key@3` is `key`.
fn untimed(symbol: &str) -> &str {
    match symbol.rsplit_once('@') {
        Some((term, moment)) if !moment.is_empty() && moment.chars().all(|c| c.is_ascii_digit()) => term,
        _ => symbol,
    }
}

