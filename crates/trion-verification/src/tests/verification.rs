//! The result flow, below the interface of the analysis.

use super::common::*;
use crate::{analyze, Analysis, Bounds, Options};

fn bounded(src: &str, decisions: Option<u64>) -> Analysis {
    analyze(&set(src), &Options { bounds: Bounds { decisions, ..Bounds::default() }, subject_revision: Some("r1".to_string()), ..Options::default() })
}

const CHOICE: &str = "The API shall either accept the call or reject the call.\n";

#[test]
fn each_result_has_one_verdict() {
    assert_eq!(bounded(CHOICE, Some(0)).consistency.verdict, "unknown");
    assert_eq!(bounded(CHOICE, None).consistency.verdict, "consistent");
    assert_eq!(bounded("The API shall stop.\nThe API shall not stop.\n", None).consistency.verdict, "inconsistent");
    // A specification that a behaviour satisfies is inconsistent when its
    // statements cannot be kept in a situation that can occur.
    let conditional = bounded("While the door is open, the API shall stop.\nWhile the door is open, the API shall not stop.\n", None);
    assert!(conditional.consistency.is_satisfiable());
    assert_eq!(conditional.consistency.verdict, "inconsistent");
}
