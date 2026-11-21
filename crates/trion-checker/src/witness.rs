//! A behaviour that keeps every contract, as a concrete behaviour.
//!
//! The claim that a behaviour keeps every contract rests on a model of the
//! formulas of the reading. A model of formulas is no behaviour: it gives
//! truth values to atoms. This module asks for a model that is a complete
//! behaviour (nothing happens after the last moment, and each moment has a
//! time), writes it down as a behaviour with the table of atoms of the
//! reading, and gives it to the reference evaluator. A behaviour that the
//! formulas accept and the meaning of the statements refuses shows that
//! the reading differs from the meaning; a behaviour that both accept is
//! the evidence of the claim, in the terms of the statements.

use crate::compare::{reduce_all, Fixed, Stated};
use crate::eval::{evaluate, Evaluation};
use crate::world::{Moment, Occurrence, World};
use serde::Serialize;
use std::collections::{BTreeMap, HashMap};
use trion_language::reading::{continues, moment_atom, moment_time, unroll_complete, Fact, Individuals, Model};
use trion_solver::{Atom, Cmp, Formula, Prover, Status, NUMERIC_SCALE};

/// What the search for a concrete behaviour found.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case", tag = "result")]
pub enum Witnessed {
    /// A complete behaviour that the formulas accept, with what the
    /// reference evaluator says of it.
    Behaviour {
        world: World,
        /// The time between two moments, in milliseconds.
        spacing: i64,
        /// `true` when a statement applies at the first moment of the
        /// behaviour by an event, or by a state where no statement names an event.
        applies: bool,
        evaluation: Evaluation,
    },
    /// No complete behaviour of the moments of the trace keeps every
    /// contract at one of the spacings that were tried.
    None { tried: Vec<i64> },
    /// The solver did not decide.
    Unknown,
}

fn occurrence_of(fact: &Fact) -> Option<Occurrence> {
    match fact {
        Fact::Occurs { verb, particle, actor, object, roles } => Some(Occurrence { verb: verb.clone(), particle: particle.clone(), actor: actor.clone(), object: object.clone(), roles: roles.clone() }),
        _ => None,
    }
}

/// The most questions that the search asks to leave occurrences out of a behaviour.
const MOST_LEFT_OUT: usize = 96;

/// The spacings of the moments that are tried, in milliseconds: one second
/// first, then shorter and longer ones for deadlines of other sizes.
const SPACINGS: [i64; 5] = [1000, 100, 1, 60_000, 3_600_000];

/// Looks for a complete behaviour of `length` moments that the formulas of
/// the model accept, and judges it by the reference evaluator.
pub fn witness(model: &Model, individuals: &Individuals, length: usize) -> Witnessed {
    let length = length.max(2);
    let trace = unroll_complete(model, length);
    let mut formulas: Vec<Formula> = trace.background.clone();
    formulas.extend(trace.groups.iter().map(|(formula, _)| formula.clone()));
    // A complete behaviour: nothing happens in the rest, and the behaviour does not go on.
    formulas.push(Formula::not(Formula::atom(continues())));
    for entry in &individuals.atoms {
        if matches!(entry.fact, Fact::Occurs { .. }) {
            formulas.push(Formula::not(Formula::atom(moment_atom(&entry.atom, length))));
            if let Atom::Act { key } = &entry.atom {
                formulas.push(Formula::not(Formula::atom(moment_atom(&Atom::Event { key: key.replace('|', " ") }, length))));
            }
        }
    }
    // A statement applies at the first moment, where one can.
    // The condition is one that an occurrence meets: a condition of kinds
    // and relations alone holds in a behaviour in which nothing happens.
    let with = |wanted: &dyn Fn(&Atom) -> bool| -> Vec<Formula> {
        trace
            .groups
            .iter()
            .filter_map(|(_, condition)| condition.clone())
            .filter(|condition| {
                let mut found = false;
                condition.atoms(true, &mut |atom, positive| found |= positive && wanted(atom));
                found
            })
            .collect()
    };
    let mut conditions = with(&|atom| matches!(atom, Atom::Event { .. }));
    if conditions.is_empty() {
        conditions = with(&|atom| matches!(atom, Atom::Val { .. }));
    }
    let mut tried = Vec::new();
    let mut undecided = false;
    for applies in [true, false] {
        if applies && conditions.is_empty() {
            continue;
        }
        for spacing in SPACINGS {
            let mut query = formulas.clone();
            if applies {
                query.push(Formula::Or(conditions.clone()));
            }
            for moment in 0..length {
                query.push(Formula::atom(Atom::Num { attr: moment_time(moment), unit: "ms".to_string(), cmp: Cmp::Eq, n: spacing * moment as i64 * NUMERIC_SCALE }));
            }
            let mut prover = Prover::default();
            let mut ids: Vec<usize> = query.iter().map(|formula| prover.add(formula)).collect();
            let answer = prover.decide(&ids);
            match (answer.status, answer.witness()) {
                (Status::Satisfiable, Some(found)) => {
                    // A behaviour with as little in it as the contracts
                    // allow: each occurrence of the model is left out where
                    // a model without it exists. What is left is needed by
                    // a statement, so a response that the formulas take for
                    // another one is not hidden behind an occurrence that
                    // nothing asked for.
                    let mut atoms = found.atoms();
                    let occurrences: Vec<Atom> = individuals.atoms.iter().filter(|entry| matches!(entry.fact, Fact::Occurs { .. })).flat_map(|entry| (0..length).map(move |moment| moment_atom(&entry.atom, moment))).collect();
                    // The occurrences are left out in groups: a group that
                    // cannot be left out as a whole is halved, down to the
                    // single occurrence that a statement needs. An
                    // occurrence that the model at hand does not hold is
                    // left out without a question.
                    let mut open: Vec<Vec<Atom>> = vec![occurrences];
                    let mut asked = 0;
                    while let Some(group) = open.pop() {
                        let mut held: Vec<Atom> = Vec::new();
                        for atom in group {
                            if atoms.get(&atom).copied().unwrap_or(false) {
                                held.push(atom);
                            } else {
                                ids.push(prover.add(&Formula::not(Formula::atom(atom))));
                            }
                        }
                        if held.is_empty() || asked == MOST_LEFT_OUT {
                            continue;
                        }
                        asked += 1;
                        let before = ids.len();
                        for atom in &held {
                            ids.push(prover.add(&Formula::not(Formula::atom(atom.clone()))));
                        }
                        let fewer = prover.decide(&ids);
                        match (fewer.status, fewer.witness()) {
                            (Status::Satisfiable, Some(found)) => atoms = found.atoms(),
                            _ => {
                                ids.truncate(before);
                                if held.len() > 1 {
                                    let later = held.split_off(held.len() / 2);
                                    open.push(later);
                                    open.push(held);
                                }
                            }
                        }
                    }
                    let world = behaviour(individuals, &atoms, length, spacing);
                    let evaluation = evaluate(individuals, &world);
                    return Witnessed::Behaviour { world, spacing, applies, evaluation };
                }
                (Status::Unsatisfiable, _) => {
                    if !applies {
                        tried.push(spacing);
                    }
                }
                _ => undecided = true,
            }
        }
    }
    if undecided {
        Witnessed::Unknown
    } else {
        Witnessed::None { tried }
    }
}

/// The behaviour that a model of the formulas stands for: each atom of the
/// table of the reading that the model makes true, as its fact.
fn behaviour(individuals: &Individuals, model: &BTreeMap<Atom, bool>, length: usize, spacing: i64) -> World {
    let holds = |atom: &Atom| model.get(atom).copied().unwrap_or(false);
    let mut world = World { explicit_membership_carriers: individuals.explicit_membership_carriers.clone(), moments: (0..length).map(|moment| Moment { time: spacing * moment as i64, ..Default::default() }).collect(), ..Default::default() };
    for entry in &individuals.atoms {
        match &entry.fact {
            Fact::Kind { kind, subject } => {
                if holds(&entry.atom) {
                    world.kinds.insert((kind.clone(), subject.clone()));
                    // An individual is an individual of the carrier that its name bears.
                    if let Some((noun, _)) = subject.split_once('#') {
                        if noun == kind || world.explicit_membership_carriers.contains(noun) {
                            world.individuals.insert(subject.clone(), noun.to_string());
                        }
                    }
                }
            }
            Fact::Related { relation, owner, member } => {
                if holds(&entry.atom) {
                    world.relations.insert((relation.clone(), owner.clone(), member.clone()));
                }
            }
            Fact::State { subject, value } => {
                for moment in 0..length {
                    if holds(&moment_atom(&entry.atom, moment)) {
                        world.moments[moment].states.insert((subject.clone(), value.clone()));
                    }
                }
            }
            fact @ Fact::Occurs { .. } => {
                let Some(occurrence) = occurrence_of(fact) else { continue };
                for moment in 0..length {
                    if holds(&moment_atom(&entry.atom, moment)) {
                        world.moments[moment].occurrences.insert(occurrence.clone());
                    }
                }
            }
        }
    }
    world
}

/// What the search for a response to a situation found.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case", tag = "result")]
pub enum Responded {
    /// The formulas give a response, and the behaviour with that response
    /// is judged by the reference evaluator.
    Response { world: World, evaluation: Evaluation },
    /// The statements without normative force exclude the situation.
    Excluded,
    /// The formulas give no response within the moments of the situation
    /// and one moment after them.
    None,
    /// The solver did not decide, or the formulas hold atoms that the
    /// situation does not fix.
    Unknown,
}

/// The situation of a behaviour: the behaviour without the occurrences that
/// the statements require, forbid or permit (`is_response`). Beside each
/// of its moments stands one more, `later` milliseconds after it, at which
/// a response to that moment can lie: the moments of a scenario are those
/// at which something is stated, and a response that was taken out may
/// have been the only thing stated at its moment.
pub fn situation(world: &World, is_response: &dyn Fn(&Occurrence) -> bool, later: i64) -> World {
    let closed = world.closed();
    let times: std::collections::BTreeSet<i64> = closed.moments.iter().flat_map(|moment| [moment.time, moment.time + later]).collect();
    let mut situation = World { moments: Vec::new(), ..closed.clone() };
    for time in times {
        // The states of the last stated moment hold on; what happens, happens at its own moment.
        let states = closed.moments.iter().filter(|moment| moment.time <= time).next_back().map(|moment| moment.states.clone()).unwrap_or_default();
        let occurrences = closed.moments.iter().filter(|moment| moment.time == time).flat_map(|moment| moment.occurrences.iter().filter(|occurrence| !is_response(occurrence)).cloned()).collect();
        situation.moments.push(Moment { time, states, occurrences });
    }
    situation
}

/// Asks the formulas of the model for a response to a situation: the
/// occurrences that `is_response` names are left to the solver at each
/// moment, and everything else is as the situation says. The behaviour
/// with the response that the solver gives is judged by the reference
/// evaluator.
///
/// A situation that the reference evaluator already refuses without a
/// response from the statements without normative force is excluded: the
/// claim about situations speaks of those that can occur.
pub fn respond(stated: &Stated, situation: &World, is_response: &dyn Fn(&Occurrence) -> bool) -> Responded {
    let individuals = stated.individuals;
    // What the domain and the descriptions say of the situation alone.
    let alone = evaluate(individuals, situation);
    let descriptive: Vec<&str> = individuals.domain.iter().map(|fact| fact.statement.as_str()).chain(individuals.meanings.iter().filter(|m| m.force == trion_language::reading::typed::Force::Description).map(|m| m.statement.as_str())).collect();
    if alone.violations.iter().any(|violation| descriptive.contains(&violation.statement.as_str())) {
        return Responded::Excluded;
    }
    let length = situation.moments.len();
    // What the situation fixes, and the occurrences that are left to the response.
    let mut fixed: HashMap<Atom, bool> = HashMap::new();
    let mut tied: Vec<Formula> = Vec::new();
    let mut open: Vec<(Atom, Occurrence)> = Vec::new();
    fixed.insert(continues(), false);
    for entry in &individuals.atoms {
        match &entry.fact {
            Fact::Kind { kind, subject } => {
                fixed.insert(entry.atom.clone(), situation.is(kind, subject));
            }
            Fact::Related { relation, owner, member } => {
                fixed.insert(entry.atom.clone(), situation.related(relation, owner, member));
            }
            Fact::State { subject, value } => {
                for moment in 0..length {
                    fixed.insert(moment_atom(&entry.atom, moment), situation.holds(moment, subject, value));
                }
            }
            fact @ Fact::Occurs { .. } => {
                let Some(occurrence) = occurrence_of(fact) else { continue };
                let event = |moment: usize| match &entry.atom {
                    Atom::Act { key } => Some(moment_atom(&Atom::Event { key: key.replace('|', " ") }, moment)),
                    _ => None,
                };
                // Nothing happens after the last moment.
                fixed.insert(moment_atom(&entry.atom, length), false);
                if let Some(event) = event(length) {
                    fixed.insert(event, false);
                }
                if is_response(&occurrence) {
                    // An action and its event are one occurrence.
                    for moment in 0..length {
                        if let Some(event) = event(moment) {
                            let (act, event) = (Formula::atom(moment_atom(&entry.atom, moment)), Formula::atom(event));
                            tied.push(Formula::implies(act.clone(), event.clone()));
                            tied.push(Formula::implies(event, act));
                        }
                    }
                    open.push((entry.atom.clone(), occurrence));
                    continue;
                }
                for moment in 0..length {
                    fixed.insert(moment_atom(&entry.atom, moment), situation.occurs(moment, &occurrence));
                    if let Some(event) = event(moment) {
                        fixed.insert(event, situation.occurs(moment, &occurrence));
                    }
                }
            }
        }
    }
    // What the situation decides is evaluated; the solver is asked for the response.
    let mut fixed = Fixed { atoms: fixed, times: situation.moments.iter().map(|moment| moment.time).collect() };
    // An occurrence that a formula requires by itself is decided here,
    // and with it the event of its action.
    let mut whole: Vec<Formula> = tied;
    whole.extend(stated.formulas(length, &fixed));
    let Some(mut formulas) = reduce_all(whole, &mut fixed) else { return Responded::None };
    for (moment, at) in situation.moments.iter().enumerate() {
        formulas.push(Formula::atom(Atom::Num { attr: moment_time(moment), unit: "ms".to_string(), cmp: Cmp::Eq, n: at.time * NUMERIC_SCALE }));
    }
    let mut prover = Prover::default();
    let mut ids: Vec<usize> = formulas.iter().map(|formula| prover.add(formula)).collect();
    let answer = prover.decide(&ids);
    match (answer.status, answer.witness()) {
        (Status::Satisfiable, Some(found)) => {
            // The response with as little in it as the contracts allow:
            // the occurrences are left out in groups, and a group that
            // cannot be left out as a whole is halved. An occurrence that
            // a formula requires by itself was decided before the search
            // and is part of every response.
            let mut atoms = found.atoms();
            let all: Vec<Atom> = open.iter().flat_map(|(atom, _)| (0..length).map(move |moment| moment_atom(atom, moment))).filter(|at| !fixed.atoms.contains_key(at)).collect();
            let mut groups: Vec<Vec<Atom>> = vec![all];
            let mut asked = 0;
            while let Some(group) = groups.pop() {
                let mut held: Vec<Atom> = Vec::new();
                for at in group {
                    if atoms.get(&at).copied().unwrap_or(false) {
                        held.push(at);
                    } else {
                        ids.push(prover.add(&Formula::not(Formula::atom(at))));
                    }
                }
                if held.is_empty() || asked == MOST_LEFT_OUT {
                    continue;
                }
                asked += 1;
                let before = ids.len();
                for at in &held {
                    ids.push(prover.add(&Formula::not(Formula::atom(at.clone()))));
                }
                let fewer = prover.decide(&ids);
                match (fewer.status, fewer.witness()) {
                    (Status::Satisfiable, Some(found)) => atoms = found.atoms(),
                    _ => {
                        ids.truncate(before);
                        if held.len() > 1 {
                            let later = held.split_off(held.len() / 2);
                            groups.push(later);
                            groups.push(held);
                        }
                    }
                }
            }
            let mut world = situation.clone();
            for (atom, occurrence) in &open {
                for moment in 0..length {
                    let at = moment_atom(atom, moment);
                    let occurs = fixed.atoms.get(&at).copied().unwrap_or_else(|| atoms.get(&at).copied().unwrap_or(false));
                    if occurs {
                        world.moments[moment].occurrences.insert(occurrence.clone());
                    }
                }
            }
            let evaluation = evaluate(individuals, &world);
            Responded::Response { world, evaluation }
        }
        (Status::Unsatisfiable, _) => Responded::None,
        _ => Responded::Unknown,
    }
}

/// What the search for a situation in which statements apply together found.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case", tag = "result")]
pub enum Together {
    /// The statements without normative force allow no behaviour in which
    /// the statements apply together at its first moment.
    Apart,
    /// A situation in which they apply together, and what the formulas
    /// answer to it.
    Situation { situation: World, responded: Responded },
    /// The solver did not decide.
    Unknown,
}

/// Leaves out of a model each of the named atoms that the formulas of the
/// prover do not need: in groups, halving a group that cannot be left out
/// as a whole.
fn leave_out(prover: &mut Prover, ids: &mut Vec<usize>, atoms: &mut BTreeMap<Atom, bool>, candidates: Vec<Atom>) {
    let mut groups: Vec<Vec<Atom>> = vec![candidates];
    let mut asked = 0;
    while let Some(group) = groups.pop() {
        let mut held: Vec<Atom> = Vec::new();
        for atom in group {
            if atoms.get(&atom).copied().unwrap_or(false) {
                held.push(atom);
            } else {
                ids.push(prover.add(&Formula::not(Formula::atom(atom))));
            }
        }
        if held.is_empty() || asked == MOST_LEFT_OUT {
            continue;
        }
        asked += 1;
        let before = ids.len();
        for atom in &held {
            ids.push(prover.add(&Formula::not(Formula::atom(atom.clone()))));
        }
        let fewer = prover.decide(ids);
        match (fewer.status, fewer.witness()) {
            (Status::Satisfiable, Some(found)) => *atoms = found.atoms(),
            _ => {
                ids.truncate(before);
                if held.len() > 1 {
                    let later = held.split_off(held.len() / 2);
                    groups.push(later);
                    groups.push(held);
                }
            }
        }
    }
}

/// The situations in which the statements of a package apply, one by one
/// and two by two: for each statement with a condition of a moment, and
/// for each two of them, a behaviour of two moments that the statements
/// without normative force allow and in which the conditions hold at the
/// first moment, without any occurrence that a statement requires, forbids
/// or permits. Advice is left out: a behaviour has to keep what is
/// required, forbidden and described. The formulas are asked for a response to each
/// ([`respond`]), and the reference evaluator judges the behaviour with
/// that response.
///
/// A claim that each situation has a response fails, where it fails, in a
/// situation in which statements apply together: these are the situations
/// that the statements themselves give, beside those of the scenarios.
/// The situation is found by the formulas of the statements without
/// normative force, so two statements that these formulas wrongly keep
/// apart are not examined together.
pub fn together(stated: &Stated, is_response: &dyn Fn(&Occurrence) -> bool, later: i64, most: usize) -> Vec<(Vec<String>, Together)> {
    let (model, individuals) = (stated.model, stated.individuals);
    // The first moment and three more within `later`: a response of
    // several actions in order has a moment for each.
    let length = 4;
    let later = (later / 3).max(1);
    let stated = &stated.required();
    let trace = unroll_complete(model, length);
    let statement_of = |id: &str| id.split('/').next().unwrap_or(id).to_string();
    let force_of = |statement: &str| individuals.meanings.iter().find(|m| m.statement == statement).map(|m| m.force);
    let normative = |at: usize| {
        let constraint = &model.constraints[at];
        if !matches!(constraint.kind, trion_language::reading::ConstraintKind::Spec | trion_language::reading::ConstraintKind::Permission) {
            return false;
        }
        match constraint.refs.first().and_then(|r| force_of(&statement_of(&r.id))) {
            Some(force) => force != trion_language::reading::typed::Force::Description,
            None => {
                let mut acts = false;
                constraint.guarantee.atoms(true, &mut |atom, _| acts |= matches!(atom, Atom::Act { .. } | Atom::Forbid { .. } | Atom::Discouraged { .. }));
                acts
            }
        }
    };
    // What the statements without normative force say of a behaviour of two moments.
    let mut prover = Prover::default();
    let mut base: Vec<usize> = trace.background.iter().map(|formula| prover.add(formula)).collect();
    for (at, (formula, _)) in trace.groups.iter().enumerate() {
        if !normative(at) {
            base.push(prover.add(formula));
        }
    }
    base.push(prover.add(&Formula::not(Formula::atom(continues()))));
    for moment in 0..length {
        base.push(prover.add(&Formula::atom(Atom::Num { attr: moment_time(moment), unit: "ms".to_string(), cmp: Cmp::Eq, n: later * moment as i64 * NUMERIC_SCALE })));
    }
    // Nothing happens after the last moment, and no response is in the situation.
    let mut others: Vec<Atom> = Vec::new();
    for entry in &individuals.atoms {
        let Some(occurrence) = occurrence_of(&entry.fact) else { continue };
        let event = |moment: usize| match &entry.atom {
            Atom::Act { key } => Some(moment_atom(&Atom::Event { key: key.replace('|', " ") }, moment)),
            _ => None,
        };
        for moment in 0..=length {
            let at = moment_atom(&entry.atom, moment);
            if moment == length || is_response(&occurrence) {
                base.push(prover.add(&Formula::not(Formula::atom(at))));
                if let Some(event) = event(moment) {
                    base.push(prover.add(&Formula::not(Formula::atom(event))));
                }
            } else {
                others.push(at);
            }
        }
    }
    // The condition of each statement at the first moment: one that an
    // occurrence or a state of a moment meets.
    let mut conditions: BTreeMap<String, Vec<Formula>> = BTreeMap::new();
    for (at, (_, condition)) in trace.groups.iter().enumerate() {
        let (true, Some(condition), Some(reference)) = (normative(at), condition, model.constraints[at].refs.first()) else { continue };
        let mut of_a_moment = false;
        condition.atoms(true, &mut |atom, positive| of_a_moment |= positive && matches!(atom, Atom::Event { .. } | Atom::Val { .. }));
        if of_a_moment {
            conditions.entry(statement_of(&reference.id)).or_default().push(condition.clone());
        }
    }
    let any = |formulas: &[Formula]| if formulas.len() == 1 { formulas[0].clone() } else { Formula::Or(formulas.to_vec()) };
    let names: Vec<&String> = conditions.keys().collect();
    let mut asked: Vec<Vec<&String>> = names.iter().map(|name| vec![*name]).collect();
    for (at, first) in names.iter().enumerate() {
        for second in &names[at + 1..] {
            asked.push(vec![*first, *second]);
        }
    }
    asked.truncate(most);
    let mut found = Vec::new();
    for statements in asked {
        let mut ids = base.clone();
        for statement in &statements {
            ids.push(prover.add(&any(&conditions[*statement])));
        }
        let answer = prover.decide(&ids);
        let outcome = match (answer.status, answer.witness()) {
            (Status::Satisfiable, Some(model)) => {
                let mut atoms = model.atoms();
                leave_out(&mut prover, &mut ids, &mut atoms, others.clone());
                let situation = behaviour(individuals, &atoms, length, later);
                // Advice is no part of what a response has to keep.
                let responded = match respond(stated, &situation, is_response) {
                    Responded::Response { world, mut evaluation } => {
                        evaluation.violations.retain(|violation| !stated.advises(&violation.statement));
                        Responded::Response { world, evaluation }
                    }
                    other => other,
                };
                Together::Situation { situation, responded }
            }
            (Status::Unsatisfiable, _) => Together::Apart,
            _ => Together::Unknown,
        };
        found.push((statements.into_iter().cloned().collect(), outcome));
    }
    found
}
