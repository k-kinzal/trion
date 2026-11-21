//! The formulas of the reading on a concrete behaviour.
//!
//! The reading of a set produces formulas over atoms and states the
//! contracts over a trace of moments. A behaviour τ satisfies them exactly
//! when some valuation η of what the formulas add (the status of an action,
//! the times and counts that the reading makes) satisfies them together
//! with τ:
//!
//! ```text
//! τ ⊨ S  ⟺  ∃η. (τ, η) ⊨ L(S)
//! ```
//!
//! This module decides the right side for one behaviour. It fixes each atom
//! that the reading states a fact for (`Individuals::atoms`) to what the
//! behaviour says at each moment, fixes the time of each moment, lets the
//! solver choose η, and compares the answer with the left side, which the
//! reference evaluator decides without formulas ([`crate::eval`]).
//!
//! A behaviour is complete: nothing happens after its last moment, so each
//! event and each action is fixed to false in the rest of the trace. The
//! states of the rest are left to η: the reading states them only where
//! they hold throughout the rest, and a complete behaviour has no moment
//! there.

use crate::eval::{evaluate, Evaluation};
use crate::world::{Occurrence, World};
use serde::Serialize;
use std::collections::{BTreeSet, HashMap, HashSet};
use trion_language::reading::{continues, is_count, moment_atom, moment_time, unroll_complete_in, ConstraintKind, Fact, Individuals, Model};
use trion_solver::{decide, Atom, Cmp, Formula, Status, NUMERIC_SCALE};

/// What the formulas say of a behaviour.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Generated {
    Accepted,
    Rejected,
    /// The solver did not decide within its budget.
    Unknown,
    /// The formulas hold atoms about events, actions or states that the
    /// reading states no fact for: the behaviour does not fix them.
    NotComparable { atoms: Vec<String> },
}

/// The two judgements of one behaviour.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Comparison {
    /// What the reference evaluator found.
    pub reference: Evaluation,
    /// What the formulas of the reading say.
    pub generated: Generated,
}

impl Comparison {
    /// `Some(true)` when both judgements accept the behaviour or both reject
    /// it, `Some(false)` when they differ, `None` when one is undecided.
    pub fn agree(&self) -> Option<bool> {
        match (self.reference.accepted(), &self.generated) {
            (Some(reference), Generated::Accepted) => Some(reference),
            (Some(reference), Generated::Rejected) => Some(!reference),
            _ => None,
        }
    }
}

/// What a behaviour fixes: the truth of the atoms that the reading states
/// a fact for, and the time of each moment.
pub(crate) struct Fixed {
    pub(crate) atoms: HashMap<Atom, bool>,
    /// The time of each moment, in milliseconds.
    pub(crate) times: Vec<i64>,
}

impl Fixed {
    /// The time of the moment that a quantity names, in the scale of the formulas.
    fn time(&self, attr: &str) -> Option<i128> {
        let moment: usize = attr.strip_prefix(TIME)?.parse().ok()?;
        Some(i128::from(*self.times.get(moment)?) * i128::from(NUMERIC_SCALE))
    }

    /// What the behaviour says of an atom: a fact that it fixes, or a
    /// comparison of the times of its moments.
    pub(crate) fn value(&self, atom: &Atom) -> Option<bool> {
        let holds = |sum: i128, cmp: Cmp, n: i64| {
            let n = i128::from(n);
            match cmp {
                Cmp::Eq => sum == n,
                Cmp::Ge => sum >= n,
                Cmp::Gt => sum > n,
                Cmp::Le => sum <= n,
                Cmp::Lt => sum < n,
            }
        };
        match atom {
            Atom::Num { attr, cmp, n, .. } => Some(holds(self.time(attr)?, *cmp, *n)),
            Atom::Lin { terms, cmp, n, .. } => {
                let mut sum = 0i128;
                for (attr, coefficient) in terms {
                    sum += self.time(attr)? * i128::from(*coefficient);
                }
                Some(holds(sum, *cmp, *n))
            }
            other => self.atoms.get(other).copied(),
        }
    }
}

/// What the name of the time of a moment begins with.
const TIME: &str = "time@";

/// A formula with the atoms that a behaviour fixes replaced by their values.
pub(crate) enum Reduced {
    True,
    False,
    Open(Formula),
}

/// Evaluates a formula as far as the fixed atoms decide it: what is left
/// speaks only of what the reading adds to a behaviour.
pub(crate) fn reduce(formula: &Formula, fixed: &Fixed) -> Reduced {
    match formula {
        Formula::True => Reduced::True,
        Formula::Atom(atom) => match fixed.value(atom) {
            Some(true) => Reduced::True,
            Some(false) => Reduced::False,
            None => Reduced::Open(formula.clone()),
        },
        Formula::Not(inner) => match reduce(inner, fixed) {
            Reduced::True => Reduced::False,
            Reduced::False => Reduced::True,
            Reduced::Open(left) => Reduced::Open(Formula::not(left)),
        },
        Formula::And(items) => {
            let mut left = Vec::new();
            for item in items {
                match reduce(item, fixed) {
                    Reduced::True => {}
                    Reduced::False => return Reduced::False,
                    Reduced::Open(formula) => left.push(formula),
                }
            }
            match left.len() {
                0 => Reduced::True,
                1 => Reduced::Open(left.remove(0)),
                _ => Reduced::Open(Formula::And(left)),
            }
        }
        Formula::Or(items) => {
            let mut left = Vec::new();
            for item in items {
                match reduce(item, fixed) {
                    Reduced::True => return Reduced::True,
                    Reduced::False => {}
                    Reduced::Open(formula) => left.push(formula),
                }
            }
            match left.len() {
                0 => Reduced::False,
                1 => Reduced::Open(left.remove(0)),
                _ => Reduced::Open(Formula::Or(left)),
            }
        }
        Formula::Implies(condition, consequence) => match (reduce(condition, fixed), reduce(consequence, fixed)) {
            (Reduced::False, _) | (_, Reduced::True) => Reduced::True,
            (Reduced::True, other) => other,
            (Reduced::Open(condition), Reduced::False) => Reduced::Open(Formula::not(condition)),
            (Reduced::Open(condition), Reduced::Open(consequence)) => Reduced::Open(Formula::implies(condition, consequence)),
        },
    }
}

fn occurrence_of(fact: &Fact) -> Option<Occurrence> {
    match fact {
        Fact::Occurs { verb, particle, actor, object, roles } => Some(Occurrence { verb: verb.clone(), particle: particle.clone(), actor: actor.clone(), object: object.clone(), roles: roles.clone() }),
        _ => None,
    }
}

/// The name of an atom of a trace without its moment.
fn base(name: &str) -> &str {
    name.rsplit_once('@').map_or(name, |(base, _)| base)
}

/// Evaluates formulas on what a behaviour fixes, and what a formula that
/// is left as one literal fixes in turn: the count of the first
/// activations decides the count of the next, so a formula that defines an
/// atom by decided ones decides it. The formulas that are left speak only
/// of what the reading adds to the behaviour; `None` when one is false.
pub(crate) fn reduce_all(formulas: Vec<Formula>, fixed: &mut Fixed) -> Option<Vec<Formula>> {
    let mut left = formulas;
    loop {
        let mut decided = false;
        let mut next: Vec<Formula> = Vec::new();
        for formula in &left {
            let mut open = match reduce(formula, fixed) {
                Reduced::True => continue,
                Reduced::False => return None,
                Reduced::Open(formula) => vec![formula],
            };
            while let Some(formula) = open.pop() {
                // One literal decides its atom; two that decide it both ways cannot both hold.
                let literal = match formula {
                    Formula::And(items) => {
                        open.extend(items);
                        continue;
                    }
                    // A comparison of quantities is decided by the arithmetic, with the others.
                    Formula::Atom(Atom::Num { .. } | Atom::Lin { .. }) => {
                        next.push(formula);
                        continue;
                    }
                    Formula::Atom(atom) => (atom, true),
                    Formula::Not(inner) if matches!(*inner, Formula::Atom(Atom::Num { .. } | Atom::Lin { .. })) => {
                        next.push(Formula::Not(inner));
                        continue;
                    }
                    Formula::Not(inner) if matches!(*inner, Formula::Atom(_)) => match *inner {
                        Formula::Atom(atom) => (atom, false),
                        _ => continue,
                    },
                    other => {
                        next.push(other);
                        continue;
                    }
                };
                match fixed.value(&literal.0) {
                    Some(value) if value != literal.1 => return None,
                    Some(_) => {}
                    None => {
                        fixed.atoms.insert(literal.0, literal.1);
                        decided = true;
                    }
                }
            }
        }
        left = next;
        if !decided {
            return Some(left);
        }
    }
}

/// The formulas of one model over complete behaviours, and the atoms that
/// a behaviour fixes: those that the reading states a fact for.
pub struct Stated<'a> {
    pub(crate) model: &'a Model,
    pub(crate) individuals: &'a Individuals,
    events: HashSet<String>,
    actions: HashSet<&'a str>,
    values: HashSet<(&'a str, &'a str)>,
    relations: HashSet<&'a Atom>,
    /// `true` where advice is left out: the formulas are those of the
    /// statements that a behaviour has to keep.
    required: bool,
}

impl<'a> Stated<'a> {
    /// The formulas of a model that is read over individuals.
    pub fn of(model: &'a Model) -> Option<Self> {
        Some(Self::with(model, model.individuals.as_ref()?))
    }

    fn with(model: &'a Model, individuals: &'a Individuals) -> Self {
        let mut events: HashSet<String> = HashSet::new();
        let mut actions: HashSet<&str> = HashSet::new();
        let mut values: HashSet<(&str, &str)> = HashSet::new();
        let mut relations: HashSet<&Atom> = HashSet::new();
        for entry in &individuals.atoms {
            match &entry.atom {
                Atom::Event { key } => {
                    events.insert(key.clone());
                }
                Atom::Act { key } => {
                    actions.insert(key);
                    // An action and its event are one occurrence.
                    if matches!(entry.fact, Fact::Occurs { .. }) {
                        events.insert(key.replace('|', " "));
                    }
                }
                Atom::Val { attr, value } => {
                    values.insert((attr, value));
                }
                other => {
                    relations.insert(other);
                }
            }
        }
        Stated { model, individuals, events, actions, values, relations, required: false }
    }

    /// The same formulas without those of advice: a behaviour has to keep
    /// what is required, forbidden and described, and advice is none of it.
    pub fn required(&self) -> Stated<'a> {
        Stated { model: self.model, individuals: self.individuals, events: self.events.clone(), actions: self.actions.clone(), values: self.values.clone(), relations: self.relations.clone(), required: true }
    }

    /// `true` for a statement that advises or advises against.
    pub fn advises(&self, statement: &str) -> bool {
        let statement = statement.split('/').next().unwrap_or(statement);
        self.individuals.meanings.iter().any(|m| m.statement == statement && matches!(m.force, trion_language::reading::typed::Force::Recommendation | trion_language::reading::typed::Force::RecommendationAgainst))
    }

    /// The atoms of the formulas about events, actions or states that the
    /// reading states no fact for: a behaviour does not fix them.
    pub(crate) fn open(&self, formulas: &[Formula]) -> Vec<String> {
        // What a statement about the domain claims of the types is no fact
        // of a behaviour: no behaviour fixes it, and none has to.
        let about: HashSet<&str> = self.individuals.domain.iter().map(|fact| fact.statement.as_str()).collect();
        let mut claimed: BTreeSet<String> = BTreeSet::new();
        for constraint in self.model.constraints.iter().filter(|c| matches!(c.kind, ConstraintKind::Spec | ConstraintKind::Permission | ConstraintKind::Axiom) && c.refs.first().is_some_and(|at| about.contains(at.id.as_str()))) {
            for formula in [&constraint.assume, &constraint.guarantee] {
                formula.atoms(true, &mut |atom, _| {
                    claimed.insert(match atom {
                        Atom::Event { key } => format!("Event({key})"),
                        Atom::Act { key } => format!("Act({key})"),
                        // A value that the statement gives the type: at a
                        // moment it is the same claim.
                        Atom::Val { attr, value } | Atom::Dom { attr, value } => format!("Val({attr}, {value})"),
                        other => other.to_string(),
                    });
                });
            }
        }
        let mut open: BTreeSet<String> = BTreeSet::new();
        for formula in formulas {
            formula.atoms(true, &mut |atom, _| {
                let known = match atom {
                    Atom::Event { key } => key.starts_with("exists ") || self.events.contains(base(key)) || self.actions.contains(base(key)),
                    Atom::Act { key } => self.actions.contains(base(key)),
                    Atom::Val { attr, value } => self.values.contains(&(base(attr), value.as_str())),
                    // The atom that joins the nouns of one relation is made by the reading.
                    // A count of activations is made by the reading too.
                    Atom::Rel { name, .. } => Atom::representative_relation(name) || name.ends_with(" between") || is_count(atom) || self.relations.contains(atom),
                    _ => true,
                };
                if !known {
                    let written = match atom {
                        Atom::Event { key } => format!("Event({})", base(key)),
                        Atom::Act { key } => format!("Act({})", base(key)),
                        Atom::Val { attr, value } => format!("Val({}, {value})", base(attr)),
                        other => other.to_string(),
                    };
                    if !claimed.contains(&written) {
                        open.insert(written);
                    }
                }
            });
        }
        open.into_iter().collect()
    }

    /// The model as a behaviour is judged by it. A statement about the
    /// domain of the individuals claims something of their types, and no
    /// behaviour makes that claim true or false: the claim of its sentence is
    /// left out, and what follows from the claim over the declared
    /// individuals is kept as it stands.
    fn for_behaviours(&self) -> Model {
        let about: HashSet<&str> = self.individuals.domain.iter().map(|fact| fact.statement.as_str()).collect();
        let mut model = self.model.clone();
        for constraint in &mut model.constraints {
            if !constraint.refs.first().is_some_and(|at| about.contains(at.id.as_str()) && !self.model.domain_contracts.contains_key(&at.id)) {
                continue;
            }
            match constraint.kind {
                ConstraintKind::Carried => constraint.assume = Formula::True,
                ConstraintKind::Spec | ConstraintKind::Permission => {
                    constraint.assume = Formula::True;
                    constraint.guarantee = Formula::True;
                }
                _ => {}
            }
        }
        model
    }

    /// The formulas of the model over one behaviour of which `fixed` holds
    /// the facts: the contracts without the activations whose condition
    /// fails there.
    pub(crate) fn formulas(&self, length: usize, fixed: &Fixed) -> Vec<Formula> {
        let model = self.for_behaviours();
        let trace = unroll_complete_in(&model, length, &|atom| fixed.value(atom));
        let mut formulas: Vec<Formula> = trace.background;
        for (at, (formula, _)) in trace.groups.into_iter().enumerate() {
            let advice = self.required && model.constraints[at].refs.first().is_some_and(|reference| self.advises(&reference.id));
            if !advice {
                formulas.push(formula);
            }
        }
        formulas
    }

    /// Decides what the formulas of the model say of a behaviour.
    pub fn generated(&self, world: &World) -> Generated {
        match self.question(world) {
            Err(generated) => generated,
            Ok(left) => match decide(&left).status {
                Status::Satisfiable => Generated::Accepted,
                Status::Unsatisfiable => Generated::Rejected,
                _ => Generated::Unknown,
            },
        }
    }

    /// The question that the formulas of the model ask of a behaviour:
    /// formulas that hold together exactly when the behaviour keeps every
    /// statement. What the behaviour decides is evaluated, and what is left
    /// is the status of each action and the times and counts that the
    /// reading makes. `Err` holds a judgement without a question: the
    /// behaviour does not fix an atom of the formulas.
    pub fn question(&self, world: &World) -> Result<Vec<Formula>, Generated> {
        let individuals = self.individuals;
        let world = world.closed();
        let length = world.moments.len();
        let mut facts: HashMap<Atom, bool> = HashMap::new();
        for entry in &individuals.atoms {
            match &entry.fact {
                Fact::Kind { kind, subject } => {
                    facts.insert(entry.atom.clone(), world.is(kind, subject));
                }
                Fact::Related { relation, owner, member } => {
                    facts.insert(entry.atom.clone(), world.related(relation, owner, member));
                }
                Fact::State { subject, value } => {
                    for moment in 0..length {
                        facts.insert(moment_atom(&entry.atom, moment), world.holds(moment, subject, value));
                    }
                }
                fact @ Fact::Occurs { .. } => {
                    let occurrence = occurrence_of(fact).expect("an occurrence");
                    // An event whose action the behaviour fixes occurs exactly when the action completes.
                    let event = match &entry.atom {
                        Atom::Act { key } => Some(Atom::Event { key: key.replace('|', " ") }),
                        _ => None,
                    };
                    for moment in 0..length {
                        let occurs = world.occurs(moment, &occurrence);
                        facts.insert(moment_atom(&entry.atom, moment), occurs);
                        if let Some(event) = &event {
                            facts.insert(moment_atom(event, moment), occurs);
                        }
                    }
                    // Nothing happens after the last moment.
                    facts.insert(moment_atom(&entry.atom, length), false);
                    if let Some(event) = &event {
                        facts.insert(moment_atom(event, length), false);
                    }
                }
            }
        }
        // A behaviour is complete: it does not go on after its last moment.
        facts.insert(continues(), false);
        // A share is counted by the formulas themselves: the quantity that
        // holds it is left to η, and no count of the reference evaluator
        // enters this side.
        let mut facts = Fixed { atoms: facts, times: world.moments.iter().map(|moment| moment.time).collect() };
        let formulas = self.formulas(length, &facts);
        // An atom about a moment that no fact is stated for is not fixed by the behaviour.
        let open = self.open(&formulas);
        if !open.is_empty() {
            return Err(Generated::NotComparable { atoms: open });
        }
        // What the behaviour decides is evaluated; the solver is asked only
        // for what the reading adds: the status of each action, and the times
        // and counts that it makes.
        // A formula that the behaviour fails leaves the question `false`.
        let Some(mut left) = reduce_all(formulas, &mut facts) else { return Ok(vec![Formula::not(Formula::True)]) };
        for (moment, at) in world.moments.iter().enumerate() {
            left.push(Formula::atom(Atom::Num { attr: moment_time(moment), unit: "ms".to_string(), cmp: Cmp::Eq, n: at.time * NUMERIC_SCALE }));
        }
        Ok(left)
    }

    /// Judges one behaviour by the reference evaluator and by the formulas.
    pub fn compare(&self, world: &World) -> Comparison {
        Comparison { reference: evaluate(self.individuals, world), generated: self.generated(world) }
    }
}

/// Decides what the formulas of a model say of a behaviour.
pub fn generated(model: &Model, individuals: &Individuals, world: &World) -> Generated {
    Stated::with(model, individuals).generated(world)
}

/// Judges one behaviour by the reference evaluator and by the formulas.
pub fn compare(model: &Model, world: &World) -> Option<Comparison> {
    Some(Stated::of(model)?.compare(world))
}
