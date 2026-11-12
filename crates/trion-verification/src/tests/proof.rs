//! The formulas behind two rows of the inventory, rebuilt beside the proof:
//! the set that reaches the greatest weight, and the formulas that the SMT
//! output asserts.

use super::checker;
use super::common::*;
use crate::proof::{Question, StatusOutcome};
use crate::{analyze, Analysis, Bounds, Options};
use trion_solver::{Formula, Status};

fn certified(src: &str) -> Analysis {
    analyze(&set(src), &Options { bounds: Bounds { trace_length: 3, ..Bounds::default() }, certificates: true, ..Options::default() })
}

fn accepted(pool: &[Formula], question: &Question, wanted: Status) {
    assert_eq!(question.status(), wanted);
    if let Err(problem) = checker::check(&question.formulas(pool), &question.answer) {
        panic!("a certificate is rejected: {problem}");
    }
}

#[test]
fn the_greatest_weight_has_a_witness_and_a_refutation_of_every_greater_weight() {
    let source = "[H]\nThe API shall not log the call.\n\n[R1]\nThe API should log the call.\n    weight 5\n\n[R2]\nThe API should return foo.\n    weight 2\n\n[R3]\nThe API should not return foo.\n    weight 3\n";
    let analysis = certified(source);
    assert_eq!(analysis.consistency.status, Status::Satisfiable);
    let preference = analysis.preference.as_ref().expect("a preference");
    assert_eq!(preference.kept.iter().map(|r| r.id.as_str()).collect::<Vec<_>>(), ["R3"]);
    assert_eq!((preference.kept_weight, preference.optimal), (3, true));
    let proof = analysis.proof.as_ref().unwrap();
    let recommendations = proof.recommendations.as_ref().unwrap();
    accepted(&proof.pool, &recommendations.witness, Status::Satisfiable);
    assert_eq!(recommendations.dropped.len(), 2);
    for dropped in &recommendations.dropped {
        assert!(dropped.members.contains(&dropped.entry));
        accepted(&proof.pool, &dropped.refutation, Status::Unsatisfiable);
    }
    // W is the weight of the kept set, and B ∧ H ∧ S(W + 1) is refuted.
    let greatest = recommendations.greatest.as_ref().expect("the greatest weight is certified");
    assert_eq!(greatest.weight, 3);
    accepted(&proof.pool, &greatest.refutation, Status::Unsatisfiable);
    assert!(greatest.heavier.iter().all(|f| greatest.refutation.query.contains(f)));
    assert!(proof.entries.iter().filter(|e| e.kind.as_str() != "recommendation").all(|e| greatest.refutation.query.contains(&e.formula)));
    // S(W) itself has a model: the weight is reached.
    let weighted: Vec<(usize, Formula, u64)> = proof.entries.iter().enumerate().filter(|(_, e)| e.kind.as_str() == "recommendation").map(|(n, e)| (n, proof.pool[e.formula].clone(), e.weight.unwrap())).collect();
    let mut reached: Vec<Formula> = proof.background.iter().map(|&f| proof.pool[f].clone()).collect();
    reached.extend(proof.entries.iter().filter(|e| e.kind.as_str() != "recommendation").map(|e| proof.pool[e.formula].clone()));
    reached.extend(crate::proof::heavier(&weighted, 3));
    let answer = trion_solver::decide(&reached);
    assert_eq!(answer.status, Status::Satisfiable);
    checker::check(&reached, &answer).unwrap();
    assert!(proof.uncertified.iter().all(|u| u.kind != "recommendations-greatest-weight"));
}

#[test]
fn the_smt_output_is_the_decided_formulas() {
    let source = "[A] When the door opens, the alarm shall sound.\n[R] The alarm should not sound.\n";
    let analysis = certified(source);
    let decided = crate::analysis::decided(&set(source), &analysis, 3);
    let smt = crate::proof::smt::decided_to_smt2(&decided.background, &decided.contracts);
    // The asserted formulas are those of the status question, moment by moment.
    assert!(smt.contains("|Event(door open@0)|") && smt.contains("|Act(alarm_sound@3)|"), "{smt}");
    assert!(!smt.contains("|Event(door open)|"), "{smt}");
    let proof = analysis.proof.as_ref().unwrap();
    let StatusOutcome::Satisfiable { witness } = &proof.status else { panic!() };
    let asked: Vec<String> = witness.formulas(&proof.pool).iter().map(|f| f.to_string()).collect();
    let written: Vec<String> = decided.background.iter().chain(decided.contracts.iter().filter(|(_, _, recommendation)| !recommendation).map(|(_, f, _)| f)).map(|f| f.to_string()).collect();
    assert_eq!(asked, written);
    // A recommendation is no part of the status: it is written and not asserted.
    assert!(smt.contains("; R: a recommendation, not asserted"), "{smt}");
    assert_eq!(smt.matches(":named").count(), 1);
    // A longer trace writes more moments.
    assert!(crate::analysis::smt2(&set(source), &analysis, 5).contains("@5"));
}
