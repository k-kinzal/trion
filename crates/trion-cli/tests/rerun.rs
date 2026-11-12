//! A run of the stability gate at other bounds takes from the first run what
//! does not depend on the bounds. It must give what a run from the files
//! gives: the status, the conflicts, the checks, the examples and the
//! certified outcomes.

mod common;
use common::*;
use trion_verification::{analyze, Analysis, Bounds, Options};

const PACKAGE: &str = "primitive room\nprimitive owner\nprimitive user\nprimitive message\nprimitive switch\n\n[R1] Some room has no owner.\n[R2] Some room has an owner.\n[P] The user may delete the message.\n[A] The room shall be archived.\n[N] While the room is archived, the user shall not delete the message.\n[S1] When the switch is active, the switch shall not be active.\n[S2] When the switch is not active, the switch shall be active.\n\nexample ALTERNATING:\n    kind consistency\n    input \"\"\"\nprimitive lamp\n[L1] When the lamp is lit, the lamp shall not be lit.\n[L2] When the lamp is not lit, the lamp shall be lit.\n\"\"\"\n    expect consistent\n";

fn summary(analysis: &Analysis) -> serde_json::Value {
    let codes: Vec<&str> = analysis.diagnostics.iter().map(|d| d.code.as_str()).collect();
    let proof = analysis.proof.as_ref().expect("the run is certified");
    serde_json::json!({
        "consistency": analysis.consistency,
        "conflicts": analysis.conflicts,
        "checks": analysis.checks,
        "examples": analysis.examples,
        "codes": codes,
        "bounds": format!("{:?}", proof.bounds),
        "questions": proof.questions().iter().map(|q| format!("{:?}", q.status())).collect::<Vec<_>>(),
        "unread": analysis.silence.opaque.len() + analysis.silence.ungrounded.len(),
    })
}

#[test]
fn a_later_run_that_shares_the_first_run_gives_what_a_run_from_the_files_gives() {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", PACKAGE)]);
    let project = trion_cli::project::load(f.path()).unwrap();
    let first_bounds = Bounds { trace_length: 2, scope: 1, ..Bounds::default() };
    let options = |bounds: Bounds| Options { bounds, certificates: true, ..Options::default() };
    let first = analyze(&project.set, &options(first_bounds));
    // At one individual the two statements about some room contradict.
    assert_eq!(first.consistency.verdict, "inconsistent", "{:?}", first.consistency);
    let mut statuses = Vec::new();
    for (trace_length, scope) in [(3, 1), (4, 1), (2, 2), (2, 3)] {
        let bounds = Bounds { trace_length, scope, ..first_bounds };
        let again = first.again(&project.set, &options(bounds));
        let fresh = analyze(&project.set, &options(bounds));
        // The diagnostics of reading belong to the first run; what the
        // unrolling and the solver report is the same.
        let reading: Vec<&str> = fresh.diagnostics.iter().map(|d| d.code.as_str()).filter(|code| !again.diagnostics.iter().any(|d| d.code == *code)).collect();
        assert!(reading.is_empty(), "the shared run lacks {reading:?}");
        let (mut a, mut b) = (summary(&again), summary(&fresh));
        a["codes"] = serde_json::Value::Null;
        b["codes"] = serde_json::Value::Null;
        assert_eq!(a, b, "at {trace_length} moments and {scope} individuals");
        statuses.push(again.consistency.verdict.clone());
    }
    // More moments keep the contradiction of one individual; a second individual removes it.
    assert_eq!(statuses, ["inconsistent", "inconsistent", "consistent", "consistent"]);
}
