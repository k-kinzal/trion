//! The three results of a proof obligation, at the level of the library:
//! proved, refuted, or neither, by the bounds of the questions.

mod common;
use common::*;
use trion_verification::{Bounds, ObligationVerdict, Options};

fn bounded(decisions: Option<u64>) -> Options {
    Options { bounds: Bounds { decisions, ..Bounds::default() }, subject_revision: Some("r1".to_string()) }
}

const CHOICE: &str = "The API shall either accept the call or reject the call.\n";

#[test]
fn an_obligation_is_proved_refuted_or_unproved() {
    assert_eq!(consistency("The API shall stop.\n", &bounded(None)), ObligationVerdict::Proved);
    assert_eq!(consistency("The API shall stop.\nThe API shall not stop.\n", &bounded(None)), ObligationVerdict::Refuted);
    // A question that the bounds end is neither proved nor refuted.
    assert_eq!(consistency(CHOICE, &bounded(Some(0))), ObligationVerdict::Unproved);
    assert_eq!(consistency(CHOICE, &bounded(None)), ObligationVerdict::Proved);
}

#[test]
fn an_unproved_obligation_is_reported_and_a_refutation_names_its_statements() {
    let unproved = proved(&set(CHOICE), &bounded(Some(0)));
    assert!(codes(&unproved).iter().all(|c| c == "obligation-unproved") && !codes(&unproved).is_empty(), "{:?}", codes(&unproved));
    let conflict = run("The API shall stop.\nThe API shall not stop.\nThe API shall log the call.\n");
    assert_eq!(codes(&conflict), ["contradiction"]);
    let mut named: Vec<&str> = conflict.diagnostics[0].refs.iter().map(|r| r.text.as_str()).collect();
    named.sort();
    assert_eq!(named, ["The API shall not stop.", "The API shall stop."]);
}
