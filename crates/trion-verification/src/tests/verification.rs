//! The verdict of an obligation, below the interface of the analysis.

use super::common::*;
use crate::{Bounds, ObligationVerdict, Options};

fn bounded(decisions: Option<u64>) -> Options {
    Options { bounds: Bounds { decisions, ..Bounds::default() }, subject_revision: Some("r1".to_string()) }
}

const CHOICE: &str = "The API shall either accept the call or reject the call.\n";

#[test]
fn each_obligation_has_one_verdict() {
    assert_eq!(consistency(CHOICE, &bounded(Some(0))), ObligationVerdict::Unproved);
    assert_eq!(consistency(CHOICE, &bounded(None)), ObligationVerdict::Proved);
    assert_eq!(consistency("The API shall stop.\nThe API shall not stop.\n", &bounded(None)), ObligationVerdict::Refuted);
    // A specification that a behaviour satisfies is inconsistent when its
    // statements cannot be kept in a situation that the environment can
    // bring about: here the door is the environment's.
    let conditional = "environment door\nWhile the door is open, the API shall stop.\nWhile the door is open, the API shall not stop.\n";
    assert_eq!(consistency(conditional, &bounded(None)), ObligationVerdict::Refuted);
}
