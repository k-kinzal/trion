//! The reference evaluator: whether a concrete behaviour satisfies the
//! typed meaning of a statement.
//!
//! The evaluator reads the meaning of a statement
//! ([`trion_language::reading::typed::Meaning`]) and a [`World`], and
//! decides satisfaction by the rules of `spec/semantics/core.md`. It builds
//! no formula, names no atom and asks no solver: it shares with the reading
//! that produces formulas only the data that states the meaning.
//!
//! The rules:
//!
//! - A statement holds for each assignment of its variables to individuals
//!   of their carriers that are of the named kinds and stand in the named
//!   relations.
//! - A statement with a `When` or an `If` applies at each moment at which
//!   its event occurs and its states hold (a *triggered* activation). A
//!   statement with states only applies at each moment at which they hold
//!   (a *standing* activation). A statement without a condition applies to
//!   the behaviour as a whole.
//! - After a triggered activation at moment t, a required action completes
//!   at a moment after t, within the deadline counted from the time of t
//!   (the end included), strictly after an occurrence at or after t of each
//!   event that `after` names, and strictly before each occurrence after t
//!   of each event that `before` names. A forbidden action completes at no
//!   moment after t. A required state holds at the moment after t.
//! - At a standing activation at moment t, a required action completes at
//!   t, a forbidden action does not complete at t, and a required state
//!   holds at t.
//! - Without a condition, a required action completes at some moment, a
//!   forbidden action at none, and a required state holds at each moment.
//! - An action is forbidden at each position at which a prohibition
//!   forbids it, and advised against where `should not` says so. A
//!   required action completes at a moment at which it is neither; `may`
//!   requires a position at which the action is not forbidden, `should` one
//!   at which it is not forbidden and one at which it is not advised
//!   against. The positions of a triggered activation and of a statement
//!   without a condition include the time after the last moment.

use crate::world::{Occurrence, World};
use serde::Serialize;
use std::collections::BTreeSet;
use trion_language::reading::typed::{Bounding, Choice, Condition, Count, DomainFact, DomainStatement, Force, Frame, FrameKind, Meaning, Pattern, Relation, Response, Site, Term};
use trion_language::reading::Individuals;

/// One way in which a behaviour fails a statement.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Violation {
    pub statement: String,
    /// Each variable with the individual that it names in the failing instance.
    pub binding: Vec<(String, String)>,
    /// The moment of the activation that the behaviour fails.
    pub moment: Option<usize>,
    pub what: String,
}

/// What the evaluation of a behaviour against a set of statements found.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct Evaluation {
    pub violations: Vec<Violation>,
    /// Each statement that holds a part which this evaluator does not evaluate.
    pub unevaluated: Vec<(String, String)>,
    /// Each statement that bounds a share which has no value in the
    /// behaviour: its population is empty. Such a statement is neither met
    /// nor failed, and it is not counted as met.
    pub undefined: Vec<(String, String)>,
}

impl Evaluation {
    /// `Some(true)` when the behaviour fails no statement, `Some(false)`
    /// when it fails one, and `None` when no statement fails and one of them
    /// is not evaluated. A share without a value fails nothing and is
    /// listed apart (`undefined`).
    pub fn accepted(&self) -> Option<bool> {
        match (self.violations.is_empty(), self.unevaluated.is_empty()) {
            (false, _) => Some(false),
            (true, true) => Some(true),
            (true, false) => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Position {
    At(usize),
    /// The time after the last moment.
    Beyond,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Activation {
    Triggered(usize),
    Standing(usize),
    Unconditional,
}

/// What forbids and what advises against an action, position by position.
#[derive(Default)]
struct Status {
    forbidden: BTreeSet<(Occurrence, Position)>,
    discouraged: BTreeSet<(Occurrence, Position)>,
}

struct Bound<'a> {
    meaning: &'a Meaning,
    world: &'a World,
    values: Vec<&'a str>,
}

struct Windows {
    completion: Vec<usize>,
    state: Vec<usize>,
    status: Vec<Position>,
    origin: Option<usize>,
}

impl Bound<'_> {
    fn name(&self, term: &Term) -> String {
        match term {
            Term::Variable(id) => self.values[*id as usize].to_string(),
            Term::Constant(name) => name.clone(),
            Term::Attribute { name, of } => format!("{name} of {}", self.name(of)),
        }
    }

    fn occurrence(&self, pattern: &Pattern) -> Occurrence {
        Occurrence { verb: pattern.verb.clone(), particle: pattern.particle.clone(), actor: self.name(&pattern.actor), object: pattern.object.as_ref().map(|o| self.name(o)), roles: pattern.roles.iter().map(|(marker, term)| (marker.clone(), self.name(term))).collect() }
    }

    fn related(&self, relation: &Relation) -> bool {
        self.world.related(&relation.relation, &self.name(&relation.owner), &self.name(&relation.member)) != relation.denied
    }

    fn condition(&self, condition: &Condition, moment: usize) -> Result<bool, String> {
        Ok(match condition {
            Condition::Occurs { pattern, denied } => self.world.occurs(moment, &self.occurrence(pattern)) != *denied,
            Condition::Holds { subject, value, denied } => self.world.holds(moment, &self.name(subject), value) != *denied,
            Condition::Related(relation) => self.related(relation),
            Condition::Kind { kind, subject, denied } => self.world.is(kind, &self.name(subject)) != *denied,
            Condition::Compares { text } => return Err(format!("the comparison `{text}`")),
        })
    }

    fn frame(&self, frame: &Frame, moment: usize) -> Result<bool, String> {
        let mut held = Vec::new();
        for condition in &frame.conditions {
            held.push(self.condition(condition, moment)?);
        }
        Ok(if frame.any { held.iter().any(|h| *h) } else { held.iter().all(|h| *h) })
    }

    /// The activations of the statement for this assignment.
    fn activations(&self) -> Result<Vec<Activation>, String> {
        let of_a_moment = |c: &Condition| matches!(c, Condition::Occurs { .. } | Condition::Holds { .. } | Condition::Compares { .. });
        let meaning = self.meaning;
        // The individuals are of the named kinds and stand in the named
        // relations. What the response chooses is chosen for an activation.
        let chosen = |term: &Term| matches!(term, Term::Variable(id) if self.values[*id as usize] == NOT_CHOSEN);
        if !meaning.variables.iter().filter(|v| self.values[v.id as usize] != NOT_CHOSEN).all(|v| self.world.is(&v.noun, self.values[v.id as usize])) || !meaning.restrictions.iter().filter(|r| !chosen(&r.owner) && !chosen(&r.member)).all(|r| self.related(r)) {
            return Ok(Vec::new());
        }
        let triggered = meaning.frames.iter().any(|f| matches!(f.kind, FrameKind::When | FrameKind::If));
        let conditional = meaning.frames.iter().any(|f| f.conditions.iter().any(of_a_moment));
        let excepted = meaning.exception.as_ref().is_some_and(of_a_moment);
        let applies = |moment: usize| -> Result<bool, String> {
            for frame in &meaning.frames {
                if !self.frame(frame, moment)? {
                    return Ok(false);
                }
            }
            match &meaning.exception {
                Some(exception) => Ok(!self.condition(exception, moment)?),
                None => Ok(true),
            }
        };
        if !conditional && !excepted {
            return Ok(if applies(0)? { vec![Activation::Unconditional] } else { Vec::new() });
        }
        let mut found = Vec::new();
        for moment in 0..self.world.moments.len() {
            if applies(moment)? {
                found.push(if triggered { Activation::Triggered(moment) } else { Activation::Standing(moment) });
            }
        }
        // An exception alone leaves a statement without a moment of its own:
        // it applies to the behaviour where the exception fails somewhere.
        if !conditional {
            found.truncate(1);
            return Ok(found.into_iter().map(|_| Activation::Unconditional).collect());
        }
        Ok(found)
    }

    fn windows(&self, activation: Activation) -> Windows {
        let n = self.world.moments.len();
        match activation {
            Activation::Triggered(t) => Windows { completion: (t + 1..n).collect(), state: (t + 1..n).take(1).collect(), status: (t + 1..n).map(Position::At).chain([Position::Beyond]).collect(), origin: Some(t) },
            Activation::Standing(t) => Windows { completion: vec![t], state: vec![t], status: vec![Position::At(t)], origin: None },
            Activation::Unconditional => Windows { completion: (0..n).collect(), state: (0..n).collect(), status: (0..n).map(Position::At).chain([Position::Beyond]).collect(), origin: None },
        }
    }

    /// The first moment at which an occurrence of an event belongs to an
    /// activation: the moment of the trigger for the event that opens the
    /// activation, the next moment for every other event, and the first
    /// moment of the behaviour without a trigger.
    fn belongs_from(&self, event: &Pattern, origin: Option<usize>) -> usize {
        let Some(moment) = origin else { return 0 };
        let opens = self.meaning.frames.iter().filter(|f| matches!(f.kind, FrameKind::When | FrameKind::If)).flat_map(|f| &f.conditions).any(|c| matches!(c, Condition::Occurs { pattern, denied: false } if pattern == event));
        if opens {
            moment
        } else {
            moment + 1
        }
    }

    /// The positions at which a prohibition or advice against an action
    /// speaks of its action. An order restricts them: `before E` forbids
    /// until E has occurred (a completion at the moment of E is not before
    /// it), and `after E` forbids from the moment after an occurrence of E.
    fn restricted(&self, activation: Activation, after: &[Pattern], before: &[Pattern]) -> Result<Vec<Position>, String> {
        let windows = self.windows(activation);
        if after.is_empty() && before.is_empty() {
            return Ok(windows.status);
        }
        if matches!(activation, Activation::Standing(_)) {
            return Err("an order on a prohibition that applies during a state".to_string());
        }
        let n = self.world.moments.len();
        let occurred = |event: &Pattern, moments: std::ops::Range<usize>| moments.into_iter().any(|m| self.world.occurs(m, &self.occurrence(event)));
        Ok(windows
            .status
            .into_iter()
            .filter(|position| {
                let end = match position {
                    Position::At(m) => *m,
                    Position::Beyond => n,
                };
                before.iter().any(|event| !occurred(event, self.belongs_from(event, windows.origin)..(end + 1).min(n))) || after.iter().any(|event| occurred(event, self.belongs_from(event, windows.origin)..end))
            })
            .collect())
    }

    /// What the response fails of one activation, when it fails.
    fn response(&self, response: &Response, activation: Activation, status: &Status) -> Result<Option<String>, String> {
        let windows = self.windows(activation);
        let world = self.world;
        let state = |subject: &Term, value: &str, denied: bool| -> Option<String> {
            let subject = self.name(subject);
            windows.state.iter().find(|&&m| world.holds(m, &subject, value) == denied).map(|m| format!("`{subject}` is {}`{value}` at moment {m}", if denied { "" } else { "not " }))
        };
        Ok(match (self.meaning.force, response) {
            (Force::Obligation, Response::Action { pattern, deadline, after, before }) => {
                let occurrence = self.occurrence(pattern);
                let fits = |moment: usize| -> bool {
                    if !world.occurs(moment, &occurrence) {
                        return false;
                    }
                    if status.forbidden.contains(&(occurrence.clone(), Position::At(moment))) || status.discouraged.contains(&(occurrence.clone(), Position::At(moment))) {
                        return false;
                    }
                    if let (Some(deadline), Some(origin)) = (deadline, windows.origin) {
                        // The end of the deadline is included.
                        if (world.moments[moment].time - world.moments[origin].time) * 1000 > deadline.thousandths {
                            return false;
                        }
                    }
                    let follows = after.iter().all(|event| (self.belongs_from(event, windows.origin)..moment).any(|m| world.occurs(m, &self.occurrence(event))));
                    let from = windows.origin.map_or(0, |t| t + 1);
                    let precedes = before.iter().all(|event| (from..=moment.min(world.moments.len() - 1)).all(|m| !world.occurs(m, &self.occurrence(event))));
                    follows && precedes
                };
                if deadline.is_some() && windows.origin.is_none() {
                    return Err("a deadline without an occurrence that it is counted from".to_string());
                }
                (!windows.completion.iter().any(|&m| fits(m))).then(|| format!("no completion of `{}` that the statement admits", occurrence.describe()))
            }
            (Force::Prohibition, Response::Action { pattern, after, before, .. }) => {
                let occurrence = self.occurrence(pattern);
                let forbidden = self.restricted(activation, after, before)?;
                windows.completion.iter().find(|&&m| forbidden.contains(&Position::At(m)) && world.occurs(m, &occurrence)).map(|m| format!("`{}` completes at moment {m}", occurrence.describe()))
            }
            (Force::Permission, Response::Action { pattern, .. }) => {
                let occurrence = self.occurrence(pattern);
                windows.status.iter().all(|p| status.forbidden.contains(&(occurrence.clone(), *p))).then(|| format!("`{}` is permitted and forbidden at each position", occurrence.describe()))
            }
            (Force::Recommendation, Response::Action { pattern, .. }) => {
                let occurrence = self.occurrence(pattern);
                let forbidden = windows.status.iter().all(|p| status.forbidden.contains(&(occurrence.clone(), *p)));
                let discouraged = windows.status.iter().all(|p| status.discouraged.contains(&(occurrence.clone(), *p)));
                (forbidden || discouraged).then(|| format!("`{}` is advised and {} at each position", occurrence.describe(), if forbidden { "forbidden" } else { "advised against" }))
            }
            // Advice against an action says where the action is advised against, and no behaviour fails it.
            (Force::RecommendationAgainst, Response::Action { .. }) => None,
            (Force::Description | Force::Obligation, Response::State { subject, value, denied }) => state(subject, value, *denied),
            (Force::Prohibition, Response::State { subject, value, denied }) => state(subject, value, !*denied),
            (Force::Description, Response::Values { subject, values }) => {
                let subject = self.name(subject);
                windows.state.iter().find_map(|&m| {
                    let held: Vec<&str> = world.moments[m].states.iter().filter(|(s, _)| *s == subject).map(|(_, v)| v.as_str()).collect();
                    if let Some(other) = held.iter().find(|v| !values.iter().any(|listed| listed == *v)) {
                        return Some(format!("`{subject}` is `{other}` at moment {m}, which the enumeration does not list"));
                    }
                    // The subject is in one of the listed states: in none of them, the enumeration fails.
                    (held.len() != 1).then(|| format!("`{subject}` has {} of the listed states at moment {m}", held.len()))
                })
            }
            (Force::Description, Response::Related(relation)) => (!self.related(relation)).then(|| format!("{}`{}`({}, {})", if relation.denied { "" } else { "not " }, relation.relation, self.name(&relation.owner), self.name(&relation.member))),
            (Force::Description, Response::Kind { kind, subject, denied }) => (self.world.is(kind, &self.name(subject)) == *denied).then(|| format!("`{}` is {}a `{kind}`", self.name(subject), if *denied { "" } else { "not " })),
            (_, Response::Bound { text }) => return Err(format!("the bound `{text}`")),
            (force, other) => return Err(format!("a response of the form {other:?} under the force {force:?}")),
        })
    }
}

/// The name that stands at the place of a variable without an individual:
/// one that the response chooses, before it is chosen.
const NOT_CHOSEN: &str = "";

/// Each assignment of the variables of a statement to the individuals of
/// their carriers. A variable that the response chooses has no individual
/// in it: the statement holds for each of these assignments when some
/// individual meets the response ([`choices`]).
fn assignments<'a>(meaning: &Meaning, world: &'a World) -> Vec<Vec<&'a str>> {
    let mut all: Vec<Vec<&str>> = vec![Vec::new()];
    for variable in &meaning.variables {
        let individuals = if variable.site == Site::Chosen { vec![NOT_CHOSEN] } else { world.of_carrier(&variable.carrier) };
        all = all.into_iter().flat_map(|done| individuals.iter().map(move |i| done.iter().copied().chain(std::iter::once(*i)).collect())).collect();
    }
    all.retain(|values| different(meaning, values));
    all
}

/// Two variables of one noun name different individuals: `a member` and
/// `a second member` are two members.
fn different(meaning: &Meaning, values: &[&str]) -> bool {
    meaning.variables.iter().enumerate().all(|(at, first)| meaning.variables[at + 1..].iter().all(|second| first.noun != second.noun || values[first.id as usize] == NOT_CHOSEN || values[first.id as usize] != values[second.id as usize]))
}

/// The assignments that give an individual to each variable that the
/// response chooses, beside what `values` assigns: each individual of the
/// carrier that is of the named kind and stands in the named relations.
fn choices<'a>(meaning: &'a Meaning, world: &'a World, values: &[&'a str]) -> Vec<Vec<&'a str>> {
    let mut all: Vec<Vec<&str>> = vec![values.to_vec()];
    for variable in meaning.variables.iter().filter(|v| v.site == Site::Chosen) {
        let individuals = world.of_carrier(&variable.carrier);
        all = all
            .into_iter()
            .flat_map(|done| {
                individuals.iter().map(move |i| {
                    let mut next = done.clone();
                    next[variable.id as usize] = *i;
                    next
                })
            })
            .collect();
    }
    all.retain(|values| {
        let bound = Bound { meaning, world, values: values.clone() };
        different(meaning, values) && meaning.variables.iter().all(|v| world.is(&v.noun, values[v.id as usize])) && meaning.restrictions.iter().all(|r| bound.related(r))
    });
    all
}

/// The positions at which the prohibitions forbid an action and at which
/// `should not` advises against it.
fn status_of(meanings: &[Meaning], world: &World) -> Status {
    let mut status = Status::default();
    for meaning in meanings.iter().filter(|m| matches!(m.force, Force::Prohibition | Force::RecommendationAgainst)) {
        for values in assignments(meaning, world) {
            let bound = Bound { meaning, world, values };
            let Ok(activations) = bound.activations() else { continue };
            for activation in activations {
                for response in &meaning.responses {
                    let Response::Action { pattern, after, before, .. } = response else { continue };
                    let Ok(forbidden) = bound.restricted(activation, after, before) else { continue };
                    let occurrence = bound.occurrence(pattern);
                    let positions = forbidden.iter().map(|p| (occurrence.clone(), *p));
                    if meaning.force == Force::Prohibition {
                        status.forbidden.extend(positions);
                    } else {
                        status.discouraged.extend(positions);
                    }
                }
            }
        }
    }
    status
}

fn counts(found: usize, count: Count) -> bool {
    match count {
        Count::AtLeast(n) => found >= n as usize,
        Count::AtMost(n) => found <= n as usize,
        Count::Exactly(n) => found == n as usize,
    }
}

/// What a behaviour fails of a statement about the domain, when it fails.
fn domain(statement: &DomainStatement, world: &World) -> Result<Option<String>, String> {
    let individuals: Vec<&str> = world.individuals.keys().map(String::as_str).collect();
    let of_kind = |kind: &str| -> Vec<&str> { individuals.iter().copied().filter(|i| world.is(kind, i)).collect() };
    let members = |relation: &str, owner: &str| individuals.iter().filter(|m| world.related(relation, owner, m)).count();
    Ok(match &statement.fact {
        DomainFact::Related { each: true, kind, relation, count, .. } | DomainFact::Counted { kind, relation, count, .. } => of_kind(kind).into_iter().find(|x| !counts(members(relation, x), *count)).map(|x| format!("`{x}` has {} `{relation}`", members(relation, x))),
        DomainFact::Related { each: false, kind, relation, count, .. } => (!of_kind(kind).into_iter().any(|x| counts(members(relation, x), *count))).then(|| format!("no `{kind}` has the stated number of `{relation}`")),
        DomainFact::Included { narrow, wide, denied, .. } => world.relations.iter().filter(|(r, _, _)| r == narrow).find(|(_, owner, member)| world.related(wide, owner, member) == *denied).map(|(_, owner, member)| format!("`{member}` is a `{narrow}` of `{owner}` and is {}a `{wide}` of it", if *denied { "" } else { "not " })),
        DomainFact::Distinct { relation, kind, .. } => {
            let owners = of_kind(kind);
            world.relations.iter().filter(|(r, owner, _)| r == relation && owners.contains(&owner.as_str())).find_map(|(_, owner, member)| owners.iter().find(|other| **other != owner.as_str() && world.related(relation, other, member)).map(|other| format!("`{owner}` and `{other}` have the same `{relation}` `{member}`")))
        }
        DomainFact::Populated { kind, count } => (!counts(of_kind(kind).len(), *count)).then(|| format!("there are {} `{kind}`", of_kind(kind).len())),
        DomainFact::Kind { narrow, wide, both, denied } => individuals.iter().copied().find_map(|x| {
            let (a, b) = (world.is(narrow, x), world.is(wide, x));
            match (denied, both) {
                (true, _) => (a && b).then(|| format!("`{x}` is a `{narrow}` and a `{wide}`")),
                (false, true) => (a != b).then(|| format!("`{x}` is one of `{narrow}` and `{wide}` and not the other")),
                (false, false) => (a && !b).then(|| format!("`{x}` is a `{narrow}` and no `{wide}`")),
            }
        }),
        DomainFact::Same { first, second, .. } => {
            let one_way = |a: &str, b: &str| world.relations.iter().filter(|(r, _, _)| r == a).find(|(_, owner, member)| !world.related(b, owner, member)).map(|(_, owner, member)| format!("`{member}` is the `{a}` of `{owner}` and not its `{b}`"));
            one_way(first, second).or_else(|| one_way(second, first))
        }
        DomainFact::Defined { narrow, wide, relation, count, .. } => of_kind(wide).into_iter().find(|x| counts(members(relation, x), *count) && !world.is(narrow, x)).map(|x| format!("`{x}` is a `{wide}` with the stated number of `{relation}` and no `{narrow}`")),
        DomainFact::Unevaluated => return Err("a total, a part of a quantity or a condition on an individual".to_string()),
    })
}

/// How many activations a statement that bounds a share has in a
/// behaviour, and how many of them its response answers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct Counted {
    pub answered: usize,
    pub population: usize,
}

/// Counts the activations of a statement and those that its responses
/// answer. `Err` names a part that this evaluator does not evaluate.
fn counted(meaning: &Meaning, world: &World, status: &Status) -> Result<Counted, String> {
    let mut found = Counted { answered: 0, population: 0 };
    for values in assignments(meaning, world) {
        let bound = Bound { meaning, world, values };
        for activation in bound.activations()? {
            found.population += 1;
            let mut answered = true;
            for response in &meaning.responses {
                answered &= bound.response(response, activation, status)?.is_none();
            }
            found.answered += usize::from(answered);
        }
    }
    Ok(found)
}

/// The count of each statement that bounds a share, in a behaviour taken
/// with what its facts imply.
pub fn shares(individuals: &Individuals, world: &World) -> Vec<(String, Result<Counted, String>)> {
    let world = world.closed();
    let status = status_of(&individuals.meanings, &world);
    individuals.meanings.iter().filter(|m| m.share.is_some()).map(|m| (m.statement.clone(), counted(m, &world, &status))).collect()
}

/// The mark of a statement whose share is not defined in a behaviour.
pub const EMPTY_POPULATION: &str = "a share of an empty population";

/// Evaluates one statement on a behaviour, given what the prohibitions of
/// the whole set forbid.
fn statement(meaning: &Meaning, world: &World, status: &Status, out: &mut Evaluation) {
    if let Some(share) = &meaning.share {
        match counted(meaning, world, status) {
            Err(part) => out.unevaluated.push((meaning.statement.clone(), part)),
            // The share of nothing is not defined: an empty population is no population that meets a bound.
            Ok(Counted { population: 0, .. }) => out.undefined.push((meaning.statement.clone(), format!("{EMPTY_POPULATION}: no activation of the statement is in the behaviour, and the share of `{}` has no value", share.population))),
            Ok(Counted { answered, population }) => {
                // answered / population against the bound, in whole numbers.
                // A lower bound counts the activations that the response
                // meets as a requirement; an upper bound counts each
                // activation whose action completes as the statement says,
                // whatever forbids it or advises against it.
                let completed = match counted(meaning, world, &Status::default()) {
                    Ok(counted) => counted.answered,
                    Err(part) => {
                        out.unevaluated.push((meaning.statement.clone(), part));
                        return;
                    }
                };
                let right = i128::from(share.thousandths) * population as i128;
                let (left, above) = (answered as i128 * 100_000, completed as i128 * 100_000);
                let met = match share.bounding {
                    Bounding::AtLeast => left >= right,
                    Bounding::AtMost => above <= right,
                    Bounding::MoreThan => left > right,
                    Bounding::LessThan => above < right,
                    Bounding::Exactly => left >= right && above <= right,
                };
                let answered = if matches!(share.bounding, Bounding::AtMost | Bounding::LessThan) { completed } else { answered };
                if !met {
                    out.violations.push(Violation { statement: meaning.statement.clone(), binding: Vec::new(), moment: None, what: format!("{answered} of {population} `{}` are answered, which does not meet the bound", share.population) });
                }
            }
        }
        return;
    }
    for values in assignments(meaning, world) {
        let bound = Bound { meaning, world, values };
        let binding = || meaning.variables.iter().filter(|v| v.site != Site::Chosen).map(|v| (v.key.clone(), bound.values[v.id as usize].to_string())).collect::<Vec<_>>();
        let chooses = meaning.variables.iter().any(|v| v.site == Site::Chosen);
        let activations = match bound.activations() {
            Ok(activations) => activations,
            Err(part) => {
                out.unevaluated.push((meaning.statement.clone(), part));
                return;
            }
        };
        for activation in activations {
            // The failures of the responses for one assignment.
            let judged = |bound: &Bound| -> Result<(bool, Vec<Option<String>>), String> {
                let mut failures = Vec::new();
                for response in &meaning.responses {
                    failures.push(bound.response(response, activation, status)?);
                }
                let failed = match meaning.choice {
                    Choice::Either => failures.iter().all(Option::is_some),
                    Choice::One | Choice::Each => failures.iter().any(Option::is_some),
                };
                Ok((failed, failures))
            };
            let judgement = if chooses {
                // Some individual that the response may choose meets the response.
                let mut all: Vec<Option<String>> = Vec::new();
                let mut met = false;
                let mut unevaluated = None;
                for values in choices(meaning, world, &bound.values) {
                    match judged(&Bound { meaning, world, values }) {
                        Ok((false, _)) => met = true,
                        Ok((true, failures)) => all.extend(failures),
                        Err(part) => unevaluated = Some(part),
                    }
                }
                match (met, unevaluated) {
                    (true, _) => Ok((false, Vec::new())),
                    (false, Some(part)) => Err(part),
                    (false, None) if all.is_empty() => Ok((true, vec![Some("no individual of the domain is one that the response may choose".to_string())])),
                    (false, None) => {
                        all.dedup();
                        Ok((true, vec![Some(format!("no individual that the response may choose meets it: {}", all.into_iter().flatten().collect::<Vec<_>>().join("; ")))]))
                    }
                }
            } else {
                judged(&bound)
            };
            let (failed, failures) = match judgement {
                Ok(judgement) => judgement,
                Err(part) => {
                    out.unevaluated.push((meaning.statement.clone(), part));
                    return;
                }
            };
            if failed {
                let moment = match activation {
                    Activation::Triggered(t) | Activation::Standing(t) => Some(t),
                    Activation::Unconditional => None,
                };
                out.violations.push(Violation { statement: meaning.statement.clone(), binding: binding(), moment, what: failures.into_iter().flatten().collect::<Vec<_>>().join("; ") });
            }
        }
    }
}

/// Evaluates a behaviour against the typed statements of a set. The world
/// is taken with what its facts imply ([`World::closed`]).
pub fn evaluate(individuals: &Individuals, world: &World) -> Evaluation {
    let world = world.closed();
    let mut out = Evaluation::default();
    for outside in &individuals.outside {
        out.unevaluated.push((outside.statement.id.clone(), format!("`{}`, which no rule reads over individuals", outside.construct)));
    }
    for fact in &individuals.domain {
        match domain(fact, &world) {
            Ok(Some(what)) => out.violations.push(Violation { statement: fact.statement.clone(), binding: Vec::new(), moment: None, what }),
            Ok(None) => {}
            Err(part) => out.unevaluated.push((fact.statement.clone(), part)),
        }
    }
    let status = status_of(&individuals.meanings, &world);
    for meaning in &individuals.meanings {
        statement(meaning, &world, &status, &mut out);
    }
    out
}
