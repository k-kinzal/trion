//! The certificates of the trion package itself: every question of the
//! inventory has an outcome, and the checker of the tests accepts each
//! certificate. This shows nothing about what the package says; it shows
//! that no answer about it rests on the search alone.

#[path = "../../trion-verification/tests/common/checker.rs"]
mod checker;

use std::path::Path;
use trion_verification::proof::{CheckResult, ConditionOutcome, StatusOutcome};
use trion_solver::Status;
use trion_verification::{analyze, Bounds, Options};

#[test]
fn every_question_about_the_trion_package_has_a_certified_outcome() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let project = trion_cli::project::load(&root).expect("the trion package loads");
    let analysis = analyze(&project.set, &Options { bounds: Bounds::default(), certificates: true, ..Options::default() });
    let proof = analysis.proof.as_ref().expect("a proof");
    // The status has a witness over the background and every entry that is no recommendation.
    let StatusOutcome::Satisfiable { witness } = &proof.status else { panic!("the status is {:?}", proof.status.status()) };
    assert!(proof.entries.iter().filter(|e| e.kind.as_str() != "recommendation").all(|e| witness.query.contains(&e.formula)));
    assert!(proof.background.iter().all(|b| witness.query.contains(b)));
    // One outcome for the condition of each entry that has one; none is open.
    let conditional = proof.entries.iter().filter(|e| e.condition.is_some()).count();
    assert_eq!(proof.conditions.len(), conditional);
    assert!(conditional > 0, "{conditional}");
    let open: Vec<_> = proof.conditions.iter().filter(|c| !matches!(c.outcome, ConditionOutcome::NoConflict { .. })).map(|c| (proof.entries[c.entry].statement.as_ref().map(|s| s.id.clone()), c.outcome.name())).collect();
    assert!(open.is_empty(), "{open:?}");
    // Every check is proved, with one refutation for each formula of the other side.
    for claim in &proof.checks {
        let CheckResult::Proved { forward, backward, .. } = &claim.result else { panic!("{} is {}", claim.environment.name, claim.result.name()) };
        assert_eq!((forward.len(), backward.len()), (claim.not_right.len(), claim.not_left.len()));
    }
    // The checker accepts the certificate of every question.
    let questions = proof.questions();
    assert!(questions.len() > conditional);
    for question in &questions {
        assert_ne!(question.status(), Status::Unknown);
        if let Err(problem) = checker::check(&question.formulas(&proof.pool), &question.answer) {
            panic!("a certificate is rejected: {problem}");
        }
    }
    for relation in &proof.relations {
        for query in &relation.queries {
            checker::check(&query.all(), &query.answer).expect("the certificate of a question of the reader");
        }
    }
    for example in &proof.examples {
        let questions: Vec<_> = match &example.status {
            StatusOutcome::Satisfiable { witness } => vec![witness],
            StatusOutcome::Unsatisfiable { refutation, minimal, .. } => std::iter::once(refutation).chain(minimal.iter().flatten()).collect(),
            StatusOutcome::Unknown => panic!("the example {} is unknown", example.name),
        };
        for question in questions {
            checker::check(&question.formulas(&example.pool), &question.answer).expect("the certificate of an example");
        }
    }
}
