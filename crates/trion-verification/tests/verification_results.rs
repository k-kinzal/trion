//! The three-valued results of the checker, at the level of the library.

mod common;
use common::*;
use trion_solver::Status;
use trion_verification::{analyze, Analysis, Bounds, Options};

fn bounded(src: &str, decisions: Option<u64>) -> Analysis {
    analyze(&set(src), &Options { bounds: Bounds { decisions, ..Bounds::default() }, subject_revision: Some("r1".to_string()), ..Options::default() })
}

const CHOICE: &str = "The API shall either accept the call or reject the call.\n";

#[test]
fn a_result_is_satisfiable_unsatisfiable_or_unknown_by_its_status() {
    let cases = [
        (bounded("The API shall stop.\n", None), Status::Satisfiable),
        (bounded("The API shall stop.\nThe API shall not stop.\n", None), Status::Unsatisfiable),
        (bounded(CHOICE, Some(0)), Status::Unknown),
    ];
    for (analysis, status) in cases {
        let result = &analysis.consistency;
        assert_eq!(result.status, status);
        // Exactly one of the three holds, and it is the one the status names.
        assert_eq!((result.is_satisfiable(), result.is_unsatisfiable(), result.is_unknown()), (status == Status::Satisfiable, status == Status::Unsatisfiable, status == Status::Unknown));
        assert_eq!(result.status.as_str(), ["satisfiable", "unsatisfiable", "unknown"][status as usize]);
    }
}

#[test]
fn a_result_carries_its_subject_method_and_bounds() {
    // A trace copies each atom for each moment, so the budget is wider than for one moment.
    let result = bounded(CHOICE, Some(200)).consistency;
    assert_eq!(result.subject_revision.as_deref(), Some("r1"));
    assert_eq!(result.bounds, Bounds { decisions: Some(200), ..Bounds::default() });
    assert!(!result.method.is_empty() && !result.profile.is_empty() && !result.assumptions.is_empty());
    assert!(result.exhaustive && result.peak_decisions <= 200);
    let cut = bounded(CHOICE, Some(0)).consistency;
    assert!(!cut.exhaustive && cut.is_unknown());
}

#[test]
fn an_unknown_result_is_flagged_and_a_core_is_minimal_only_when_proved() {
    let unknown = bounded(CHOICE, Some(0));
    assert!(unknown.has_unknown());
    assert_eq!(codes(&unknown), ["consistency-unknown"]);
    assert!(!bounded(CHOICE, None).has_unknown());
    let conflict = bounded("The API shall stop.\nThe API shall not stop.\nThe API shall log the call.\n", None);
    assert_eq!(conflict.conflicts.len(), 1);
    assert!(conflict.conflicts[0].minimal);
    assert_eq!(conflict.conflicts[0].elements.len(), 2);
}

