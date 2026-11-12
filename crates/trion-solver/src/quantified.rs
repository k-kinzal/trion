//! Whether every situation has a response.
//!
//! The question has two kinds of symbols. The *given* symbols are fixed by a
//! situation; the *chosen* symbols are what a response decides. The claim is
//!
//! > for every valuation of the given symbols that satisfies the premises,
//! > some valuation of the chosen symbols satisfies the conclusions.
//!
//! This is a formula with one alternation of quantifiers, and it is decided
//! here without listing the situations:
//!
//! - *Miniscoping.* Conclusions that share no chosen symbol are answered
//!   apart: `∃r₁r₂. (φ₁(r₁) ∧ φ₂(r₂))` is `∃r₁. φ₁(r₁) ∧ ∃r₂. φ₂(r₂)`. A
//!   conclusion without a chosen symbol must follow from the premises.
//! - *Refinement by counterexamples* within each such group. A situation is
//!   sought that no response found so far answers. When the conclusions have
//!   no valuation in it, the claim fails, and the situation is the
//!   counterexample. Otherwise the valuation is a response, and every
//!   situation that this response answers is excluded from the search. When
//!   no situation is left, the responses found are a case distinction that
//!   answers every situation.
//!
//! The search ends for symbols with finitely many values. A chosen quantity
//! that must follow a given quantity has no finite case distinction; the
//! search then ends at its bound with [`ForAll::Open`].

use crate::certificate::Status;
use crate::formula::{Atom, Cmp, Formula};
use crate::instance::Instance;
use std::collections::{BTreeMap, BTreeSet};

/// The most responses that are sought for one group of conclusions.
const RESPONSES: usize = 4096;
/// The most responses that are sought where a chosen quantity is compared
/// with a given one: a response that must follow the given quantity is
/// found by no number of them.
const FOLLOWING: usize = 64;

/// What the search established. Every list of numbers names formulas of the instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ForAll {
    /// Every situation has a response. Each query is refuted: the premises
    /// together with, for each response that was found, the denial that
    /// this response answers the situation; or the premises with the denial
    /// of a conclusion that needs no response.
    Holds { refuted: Vec<Vec<usize>> },
    /// Situations without a response, one for each group of conclusions
    /// that has one.
    Fails { situations: Vec<Unanswered> },
    /// The search ended without either answer.
    Open { reason: String },
}

/// A situation without a response. `given` fixes given symbols: the
/// premises hold with it, and the `conclusions` cannot hold with it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unanswered {
    pub given: Vec<usize>,
    pub conclusions: Vec<usize>,
}

fn falsity() -> Formula {
    Formula::Not(Box::new(Formula::True))
}

fn is_false(formula: &Formula) -> bool {
    matches!(formula, Formula::Not(inner) if **inner == Formula::True)
}

fn compare(value: i128, cmp: Cmp, n: i128) -> bool {
    match cmp {
        Cmp::Eq => value == n,
        Cmp::Ge => value >= n,
        Cmp::Le => value <= n,
        Cmp::Gt => value > n,
        Cmp::Lt => value < n,
    }
}

/// A formula with each chosen symbol replaced by its value in a response.
/// What is left speaks about given symbols only. `None` when the response
/// does not tell a value that the formula needs.
fn answered(formula: &Formula, chosen: &dyn Fn(&str) -> bool, atoms: &BTreeMap<Atom, bool>, quantities: &BTreeMap<(String, String), i64>) -> Option<Formula> {
    let constant = |value: bool| if value { Formula::True } else { falsity() };
    Some(match formula {
        Formula::True => Formula::True,
        Formula::Atom(atom) => {
            if !atom.symbols().into_iter().any(chosen) {
                return Some(formula.clone());
            }
            match atom {
                // A comparison between a chosen and a given quantity is a comparison of the given one.
                Atom::Lin { terms, unit, cmp, n } if terms.iter().any(|(attr, _)| !chosen(attr)) => {
                    let mut bound = i128::from(*n);
                    let mut rest = Vec::new();
                    for (attr, coefficient) in terms {
                        if chosen(attr) {
                            bound -= i128::from(*coefficient) * i128::from(*quantities.get(&(attr.clone(), unit.clone()))?);
                        } else {
                            rest.push((attr.clone(), *coefficient));
                        }
                    }
                    Formula::Atom(Atom::Lin { terms: rest, unit: unit.clone(), cmp: *cmp, n: i64::try_from(bound).ok()? })
                }
                Atom::Num { attr, unit, cmp, n } => match atoms.get(atom) {
                    Some(value) => constant(*value),
                    None => constant(compare(i128::from(*quantities.get(&(attr.clone(), unit.clone()))?), *cmp, i128::from(*n))),
                },
                Atom::Lin { terms, unit, cmp, n } => match atoms.get(atom) {
                    Some(value) => constant(*value),
                    None => {
                        let mut sum = 0i128;
                        for (attr, coefficient) in terms {
                            sum += i128::from(*coefficient) * i128::from(*quantities.get(&(attr.clone(), unit.clone()))?);
                        }
                        constant(compare(sum, *cmp, i128::from(*n)))
                    }
                },
                _ => constant(*atoms.get(atom)?),
            }
        }
        Formula::Not(inner) => match answered(inner, chosen, atoms, quantities)? {
            Formula::True => falsity(),
            other if is_false(&other) => Formula::True,
            other => Formula::Not(Box::new(other)),
        },
        Formula::And(items) => {
            let mut kept = Vec::new();
            for item in items {
                match answered(item, chosen, atoms, quantities)? {
                    Formula::True => {}
                    other if is_false(&other) => return Some(falsity()),
                    other => kept.push(other),
                }
            }
            match kept.len() {
                0 => Formula::True,
                1 => kept.remove(0),
                _ => Formula::And(kept),
            }
        }
        Formula::Or(items) => {
            let mut kept = Vec::new();
            for item in items {
                match answered(item, chosen, atoms, quantities)? {
                    Formula::True => return Some(Formula::True),
                    other if is_false(&other) => {}
                    other => kept.push(other),
                }
            }
            match kept.len() {
                0 => falsity(),
                1 => kept.remove(0),
                _ => Formula::Or(kept),
            }
        }
        Formula::Implies(condition, response) => match (answered(condition, chosen, atoms, quantities)?, answered(response, chosen, atoms, quantities)?) {
            (condition, _) if is_false(&condition) => Formula::True,
            (_, Formula::True) => Formula::True,
            (Formula::True, response) => response,
            (condition, response) if is_false(&response) => Formula::Not(Box::new(condition)),
            (condition, response) => Formula::Implies(Box::new(condition), Box::new(response)),
        },
    })
}

fn find(parent: &mut Vec<usize>, mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

/// Decides whether, for every valuation of the given symbols that satisfies
/// the premises, some valuation of the chosen symbols satisfies the
/// conclusions. `chosen` tells whether a symbol of an atom
/// ([`Atom::symbols`]) is chosen by a response. An atom that is no
/// comparison is chosen when one of its symbols is.
pub fn for_all_exists(instance: &Instance, premises: &[usize], conclusions: &[usize], chosen: &dyn Fn(&str) -> bool) -> ForAll {
    let formulas = instance.formulas();
    let stated: BTreeSet<String> = premises.iter().map(|&id| formulas[id].to_string()).collect();
    // The conclusions that share a chosen symbol stand in one group.
    let mut numbers: BTreeMap<String, usize> = BTreeMap::new();
    let mut parent: Vec<usize> = Vec::new();
    let mut first: Vec<Option<usize>> = Vec::new();
    for &id in conclusions {
        let mut own: Vec<usize> = Vec::new();
        formulas[id].atoms(true, &mut |atom, _| {
            for symbol in atom.symbols().into_iter().filter(|s| chosen(s)) {
                let next = numbers.len();
                let number = *numbers.entry(symbol.to_string()).or_insert(next);
                if number == parent.len() {
                    parent.push(number);
                }
                own.push(number);
            }
        });
        for pair in own.windows(2) {
            let (a, b) = (find(&mut parent, pair[0]), find(&mut parent, pair[1]));
            parent[a] = b;
        }
        first.push(own.first().copied());
    }
    let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut refuted: Vec<Vec<usize>> = Vec::new();
    let mut unanswered: Vec<Unanswered> = Vec::new();
    for (&id, symbol) in conclusions.iter().zip(&first) {
        match symbol {
            Some(symbol) => groups.entry(find(&mut parent, *symbol)).or_default().push(id),
            // A conclusion that no response decides holds in every situation.
            None if stated.contains(&formulas[id].to_string()) => {}
            None => {
                let denial = instance.add(&Formula::not(formulas[id].clone()));
                let query: Vec<usize> = premises.iter().copied().chain([denial]).collect();
                match instance.decide(&query).status {
                    Status::Unsatisfiable => refuted.push(query),
                    Status::Satisfiable => unanswered.push(Unanswered { given: vec![denial], conclusions: vec![id] }),
                    Status::Unknown => return ForAll::Open { reason: "a query ended at its bounds".to_string() },
                }
            }
        }
    }
    'groups: for members in groups.into_values() {
        // What a situation fixes for this group: its atoms and quantities without a chosen symbol.
        let mut facts: BTreeSet<Atom> = BTreeSet::new();
        let mut measures: BTreeSet<(String, String)> = BTreeSet::new();
        for &id in &members {
            formulas[id].atoms(true, &mut |atom, _| match atom {
                Atom::Num { attr, unit, .. } => {
                    if !chosen(attr) {
                        measures.insert((attr.clone(), unit.clone()));
                    }
                }
                Atom::Lin { terms, unit, .. } => measures.extend(terms.iter().filter(|(attr, _)| !chosen(attr)).map(|(attr, _)| (attr.clone(), unit.clone()))),
                other => {
                    if !other.symbols().into_iter().any(chosen) {
                        facts.insert(other.clone());
                    }
                }
            });
        }
        // A chosen quantity that is compared with a given one may have to
        // follow it: then no finite list of responses answers every situation.
        let mut follows = false;
        for &id in &members {
            formulas[id].atoms(true, &mut |atom, _| {
                if let Atom::Lin { terms, .. } = atom {
                    follows |= terms.iter().any(|(attr, _)| chosen(attr)) && terms.iter().any(|(attr, _)| !chosen(attr));
                }
            });
        }
        let limit = if follows { FOLLOWING } else { RESPONSES };
        let mut blocks: Vec<usize> = Vec::new();
        loop {
            if blocks.len() == limit {
                let reason = if follows {
                    format!("a quantity of the response is compared with a quantity of the situation, and {limit} responses do not answer every situation: the elimination of quantifiers over integers is not implemented")
                } else {
                    format!("{limit} responses do not answer every situation of one group of statements")
                };
                return ForAll::Open { reason };
            }
            let query: Vec<usize> = premises.iter().chain(&blocks).copied().collect();
            let situation = instance.decide(&query);
            match situation.status {
                Status::Unsatisfiable => {
                    refuted.push(query);
                    break;
                }
                Status::Unknown => return ForAll::Open { reason: "a query ended at its bounds".to_string() },
                Status::Satisfiable => {}
            }
            let (atoms, quantities) = situation.witness().map(|w| (w.atoms(), w.quantities())).unwrap_or_default();
            let mut given: Vec<usize> = Vec::new();
            for fact in &facts {
                let holds = atoms.get(fact).copied().unwrap_or(false);
                given.push(instance.add(&if holds { Formula::Atom(fact.clone()) } else { Formula::not(Formula::Atom(fact.clone())) }));
            }
            for (attr, unit) in &measures {
                let value = quantities.get(&(attr.clone(), unit.clone())).copied().unwrap_or(0);
                given.push(instance.add(&Formula::Atom(Atom::Num { attr: attr.clone(), unit: unit.clone(), cmp: Cmp::Eq, n: value })));
            }
            let response = instance.decide(&members.iter().chain(&given).copied().collect::<Vec<_>>());
            match response.status {
                Status::Unknown => return ForAll::Open { reason: "a query ended at its bounds".to_string() },
                Status::Unsatisfiable => {
                    // What the refutation needs: first of the conclusions, then of the situation.
                    let refutes = |conclusions: &[usize], given: &[usize]| instance.decide(&conclusions.iter().chain(given).copied().collect::<Vec<_>>()).status == Status::Unsatisfiable;
                    let mut core = members.clone();
                    let mut at = 0;
                    while at < core.len() {
                        let removed = core.remove(at);
                        if !refutes(&core, &given) {
                            core.insert(at, removed);
                            at += 1;
                        }
                    }
                    let mut at = 0;
                    while at < given.len() {
                        let removed = given.remove(at);
                        if !refutes(&core, &given) {
                            given.insert(at, removed);
                            at += 1;
                        }
                    }
                    unanswered.push(Unanswered { given, conclusions: core });
                    continue 'groups;
                }
                Status::Satisfiable => {
                    let (atoms, quantities) = response.witness().map(|w| (w.atoms(), w.quantities())).unwrap_or_default();
                    // Every situation in which this response keeps the conclusions is answered.
                    let mut parts = Vec::new();
                    for &id in &members {
                        match answered(&formulas[id], chosen, &atoms, &quantities) {
                            Some(Formula::True) => {}
                            Some(part) => parts.push(part),
                            None => return ForAll::Open { reason: "a response does not tell a value that a statement needs".to_string() },
                        }
                    }
                    let answers = if parts.iter().any(is_false) { falsity() } else { Formula::And(parts) };
                    blocks.push(instance.add(&Formula::not(answers)));
                }
            }
        }
    }
    if unanswered.is_empty() {
        ForAll::Holds { refuted }
    } else {
        ForAll::Fails { situations: unanswered }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn val(attr: &str, value: &str) -> Formula {
        Formula::Atom(Atom::Val { attr: attr.to_string(), value: value.to_string() })
    }

    fn act(key: &str) -> Formula {
        Formula::Atom(Atom::Act { key: key.to_string() })
    }

    fn decide(premises: &[Formula], conclusions: &[Formula], chosen: &[&str]) -> ForAll {
        let instance = Instance::new(&[], &[], None);
        let premises: Vec<usize> = premises.iter().map(|f| instance.add(f)).collect();
        let conclusions: Vec<usize> = conclusions.iter().map(|f| instance.add(f)).collect();
        for_all_exists(&instance, &premises, &conclusions, &|symbol| chosen.contains(&symbol))
    }

    #[test]
    fn two_conditions_that_meet_leave_no_response() {
        // Running and inspecting can hold together, and then the cooling cannot be both.
        let both = [Formula::implies(val("mode", "running"), act("cool")), Formula::implies(val("phase", "inspecting"), Formula::not(act("cool")))];
        let ForAll::Fails { situations } = decide(&[], &both, &["cool"]) else { panic!("the two statements meet") };
        assert_eq!(situations.len(), 1);
        assert_eq!((situations[0].given.len(), situations[0].conclusions.len()), (2, 2));
        // A premise that keeps the conditions apart leaves a response in every situation.
        let apart = Formula::not(Formula::And(vec![val("mode", "running"), val("phase", "inspecting")]));
        assert!(matches!(decide(&[apart], &both, &["cool"]), ForAll::Holds { .. }));
    }

    #[test]
    fn statements_that_share_no_chosen_symbol_are_answered_apart() {
        // Twenty conditions have a million situations; each statement is answered alone.
        let statements: Vec<Formula> = (0..20).map(|n| Formula::implies(val(&format!("part{n}"), "on"), act(&format!("signal{n}")))).collect();
        let chosen: Vec<String> = (0..20).map(|n| format!("signal{n}")).collect();
        let chosen: Vec<&str> = chosen.iter().map(String::as_str).collect();
        let ForAll::Holds { refuted } = decide(&[], &statements, &chosen) else { panic!("each statement has a response") };
        assert_eq!(refuted.len(), 20);
    }

    #[test]
    fn a_statement_about_what_is_given_must_follow_from_the_premises() {
        let closed = val("door", "closed");
        assert!(matches!(decide(&[], &[closed.clone()], &[]), ForAll::Fails { .. }));
        assert!(matches!(decide(&[closed.clone()], &[closed], &[]), ForAll::Holds { .. }));
    }

    #[test]
    fn a_response_may_depend_on_the_situation() {
        // The lamp follows the door: no single response answers both situations, and two do.
        let follows = [Formula::implies(val("door", "open"), act("light")), Formula::implies(Formula::not(val("door", "open")), Formula::not(act("light")))];
        let ForAll::Holds { refuted } = decide(&[], &follows, &["light"]) else { panic!("the lamp can follow the door") };
        assert_eq!(refuted.len(), 1);
    }
}
