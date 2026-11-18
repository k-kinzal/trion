//! The certificates of the solver that decides the obligations for
//! `trioc`, checked by a checker that shares no code with it.

use super::checker;
use super::common::*;
use trion_solver::{decide, Prover};
use trion_solver::{Answer, Certificate, Justification};
use trion_language::reading::unroll;
use trion_solver::{Atom, Cmp, Formula, Status};

fn event(key: &str) -> Formula {
    Formula::Atom(Atom::Event { key: key.to_string() })
}

fn num(attr: &str, cmp: Cmp, n: i64) -> Formula {
    Formula::Atom(Atom::Num { attr: attr.to_string(), unit: "s".to_string(), cmp, n })
}

fn lin(terms: &[(&str, i64)], cmp: Cmp, n: i64) -> Formula {
    Formula::Atom(Atom::Lin { terms: terms.iter().map(|(a, c)| (a.to_string(), *c)).collect(), unit: "s".to_string(), cmp, n })
}

fn not(f: Formula) -> Formula {
    Formula::not(f)
}

/// Decides the formulas and requires a certificate that the checker accepts.
fn certified(formulas: &[Formula]) -> Answer {
    let answer = decide(formulas);
    if let Err(problem) = checker::check(formulas, &answer) {
        panic!("the certificate of {:?} is rejected: {problem}\n{formulas:?}", answer.status);
    }
    answer
}

/// The pigeons of `holes + 1` in `holes` holes: unsatisfiable, and only by search.
fn pigeons(holes: usize) -> Vec<Formula> {
    let at = |p: usize, h: usize| event(&format!("p{p}h{h}"));
    let mut out = Vec::new();
    for p in 0..=holes {
        out.push(Formula::Or((0..holes).map(|h| at(p, h)).collect()));
    }
    for h in 0..holes {
        for p in 0..=holes {
            for q in p + 1..=holes {
                out.push(Formula::Or(vec![not(at(p, h)), not(at(q, h))]));
            }
        }
    }
    out
}

#[test]
fn a_boolean_answer_carries_a_certificate_that_the_checker_accepts() {
    let (a, b, c) = (event("a"), event("b"), event("c"));
    let sat = vec![Formula::implies(a.clone(), b.clone()), Formula::Or(vec![a.clone(), c.clone()]), not(b.clone())];
    assert_eq!(certified(&sat).status, Status::Satisfiable);
    let unsat = vec![Formula::implies(a.clone(), b.clone()), a.clone(), not(b.clone())];
    assert_eq!(certified(&unsat).status, Status::Unsatisfiable);
    // A refutation that needs both values of a decision.
    let both = vec![Formula::Or(vec![a.clone(), b.clone()]), Formula::Or(vec![a.clone(), not(b.clone())]), Formula::Or(vec![not(a.clone()), b.clone()]), Formula::Or(vec![not(a.clone()), not(b.clone())])];
    let answer = certified(&both);
    assert_eq!(answer.status, Status::Unsatisfiable);
    assert!(answer.refutation().is_some_and(|r| r.steps.len() > 1 && r.steps.last().is_some_and(|s| s.clause.is_empty())));
    for holes in 2..=4 {
        assert_eq!(certified(&pigeons(holes)).status, Status::Unsatisfiable, "{holes} holes");
    }
    assert_eq!(certified(&[Formula::True, Formula::And(vec![])]).status, Status::Satisfiable);
    assert_eq!(certified(&[Formula::Or(vec![])]).status, Status::Unsatisfiable);
    assert_eq!(certified(&[not(Formula::True)]).status, Status::Unsatisfiable);
}

#[test]
fn a_numeric_answer_carries_integers_or_a_linear_lemma() {
    // x ≤ 0 and x ≥ 2 cannot both hold: adding them gives 0 ≤ −2.
    let answer = certified(&[num("x", Cmp::Le, 0), num("x", Cmp::Ge, 2)]);
    assert_eq!(answer.status, Status::Unsatisfiable);
    assert!(answer.refutation().unwrap().steps.iter().any(|s| matches!(s.by, Justification::Linear(_))));
    // (x ≤ 0) ∨ (x ≥ 2) with x = 1 excluded on neither side has the solution 1.
    let answer = certified(&[not(num("x", Cmp::Le, 0)), not(num("x", Cmp::Ge, 2))]);
    assert_eq!(answer.witness().unwrap().quantities().get(&("x".to_string(), "s".to_string())), Some(&1));
    // timeout < retry, retry ≤ 5 and timeout ≥ 10 give 0 ≤ −6.
    let chain = [lin(&[("timeout", 1), ("retry", -1)], Cmp::Lt, 0), num("retry", Cmp::Le, 5), num("timeout", Cmp::Ge, 10)];
    assert_eq!(certified(&chain).status, Status::Unsatisfiable);
    // A disequality is split: 5 ≤ x ≤ 6, x ≠ 5 and x ≠ 6.
    let gap = [num("x", Cmp::Ge, 5), num("x", Cmp::Le, 6), not(num("x", Cmp::Eq, 5)), not(num("x", Cmp::Eq, 6))];
    assert_eq!(certified(&gap).status, Status::Unsatisfiable);
    let open = [num("x", Cmp::Ge, 5), num("x", Cmp::Le, 7), not(num("x", Cmp::Eq, 5)), not(num("x", Cmp::Eq, 6))];
    assert_eq!(certified(&open).witness().unwrap().quantities().get(&("x".to_string(), "s".to_string())), Some(&7));
    // The numbers decide between Boolean choices.
    let mixed = [Formula::Or(vec![num("x", Cmp::Ge, 10), event("late")]), num("x", Cmp::Lt, 3), not(event("late"))];
    assert_eq!(certified(&mixed).status, Status::Unsatisfiable);
    // 2·x = 3 has a rational solution and no integer one: no derivation of the stated form exists, so the answer stays open.
    let half = [lin(&[("x", 2)], Cmp::Eq, 3)];
    assert_eq!(certified(&half).status, Status::Unknown);
}

#[test]
fn a_damaged_certificate_is_rejected_by_the_checker() {
    let (a, b) = (event("a"), event("b"));
    let sat = vec![Formula::implies(a.clone(), b.clone()), a.clone(), num("x", Cmp::Ge, 3)];
    let answer = certified(&sat);
    let witness = answer.witness().unwrap();
    // One atom flipped.
    let mut flipped = witness.clone();
    let mut part = (*flipped.parts[0]).clone();
    part.atoms[0].1 = !part.atoms[0].1;
    flipped.parts[0] = std::sync::Arc::new(part);
    assert!(checker::check_witness(&sat, &flipped).is_err());
    // A wrong integer.
    let mut wrong = witness.clone();
    for slot in wrong.parts.iter_mut() {
        let mut part = (**slot).clone();
        for (_, value) in part.quantities.iter_mut() {
            *value = 0;
        }
        *slot = std::sync::Arc::new(part);
    }
    assert!(checker::check_witness(&sat, &wrong).is_err());
    // A refutation with one clause removed.
    let query = pigeons(3);
    let answer = certified(&query);
    let mut cut = answer.refutation().unwrap().clone();
    cut.steps.drain(..cut.steps.len() - 1);
    assert!(checker::check_refutation(&query, &cut).is_err());
    let mut open = answer.refutation().unwrap().clone();
    open.steps.pop();
    assert!(checker::check_refutation(&query, &open).is_err());
    // The lemma of a numeric refutation removed.
    let numbers = [num("x", Cmp::Le, 0), num("x", Cmp::Ge, 2)];
    let mut bare = certified(&numbers).refutation().unwrap().clone();
    bare.steps.retain(|s| !matches!(s.by, Justification::Linear(_)));
    assert!(checker::check_refutation(&numbers, &bare).is_err());
    // A linear lemma whose negated literals have an integer solution.
    let lemma = [num("x", Cmp::Le, 0), num("x", Cmp::Ge, 2)];
    let answer = certified(&lemma);
    let mut weak = answer.refutation().unwrap().clone();
    for step in weak.steps.iter_mut() {
        if matches!(step.by, Justification::Linear(_)) {
            // (x ≤ 0) ∨ (x ≥ 2) is no lemma: x = 1 satisfies both negations.
            for literal in step.clause.iter_mut() {
                literal.positive = !literal.positive;
            }
        }
    }
    assert!(checker::check_refutation(&lemma, &weak).is_err());
    // A status with the certificate of the other one.
    let swapped = Answer { status: Status::Unsatisfiable, certificate: Certificate::Witness(witness.clone()) };
    assert!(checker::check(&sat, &swapped).is_err());
}

const CORPUS: [&str; 8] = [
    "The API shall return foo.\nThe API shall not return foo.\n",
    "When the user leaves, the API shall return foo.\nWhen the user leaves, the API shall not return foo.\n",
    "room_type is Private or Public.\nroom_type is Invalid.\n",
    "When a request arrives, the gateway shall respond within 2 seconds.\nWhen a request arrives, the gateway shall respond within 5 seconds.\n",
    "The session shall expire after 30 minutes.\nThe session shall expire after 60 minutes.\n",
    "When the size is at least 100, the API shall stop.\nWhen the size is at most 100, the API shall not stop.\n",
    "When the door opens, the controller shall stop the motor.\nWhen the controller stops the motor, the alarm shall sound.\nWhen the door opens, the alarm shall not sound.\n",
    "The user may delete the message.\nWhile the room is archived, the user shall not delete the message.\nThe timeout shall be less than the retry interval.\nThe retry interval shall be at most 5 seconds.\n",
];

#[test]
fn every_answer_over_unrolled_statements_carries_a_certificate() {
    let mut statuses = Vec::new();
    for source in CORPUS {
        let model = run(source).model;
        for length in [2, 3, 4] {
            let trace = unroll(&model, length);
            let mut prover = Prover::default();
            let background: Vec<(usize, Formula)> = trace.background.iter().map(|f| (prover.add(f), f.clone())).collect();
            let groups: Vec<(usize, Formula)> = trace.groups.iter().map(|(f, _)| (prover.add(f), f.clone())).collect();
            let guards: Vec<(usize, Formula)> = trace.groups.iter().filter_map(|(_, g)| g.clone()).map(|g| (prover.add(&g), g)).collect();
            // The whole set, the set without each statement, and the set under each condition.
            let mut queries: Vec<Vec<(usize, Formula)>> = vec![background.iter().chain(&groups).cloned().collect()];
            for skip in 0..groups.len() {
                queries.push(background.iter().cloned().chain(groups.iter().enumerate().filter(|(n, _)| *n != skip).map(|(_, g)| g.clone())).collect());
            }
            for guard in &guards {
                queries.push(background.iter().chain(&groups).cloned().chain([guard.clone()]).collect());
            }
            for query in queries {
                let ids: Vec<usize> = query.iter().map(|(id, _)| *id).collect();
                let formulas: Vec<Formula> = query.into_iter().map(|(_, f)| f).collect();
                let answer = prover.decide(&ids);
                if let Err(problem) = checker::check(&formulas, &answer) {
                    panic!("{source} at {length}: {problem}");
                }
                statuses.push(answer.status);
            }
        }
    }
    assert!(statuses.contains(&Status::Satisfiable) && statuses.contains(&Status::Unsatisfiable));
    assert!(!statuses.contains(&Status::Unknown), "a query of the corpus stayed open");
}
