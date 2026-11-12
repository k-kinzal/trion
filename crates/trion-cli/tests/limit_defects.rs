//! Readings that were wrong, each with its reproducer.

mod common;
use common::*;

fn check(text: &str) -> serde_json::Value {
    Fixture::new(&[("a.trion", text)]).trion(&["verify", "--json", "a.trion"]).json()
}

fn model(text: &str) -> String {
    Fixture::new(&[("a.trion", text)]).inspect(&["model", "a.trion"]).stdout
}

#[test]
fn a_purpose_does_not_change_the_required_action() {
    let text = "[P1]\nThe API shall log the call so that the auditor reviews the call.\n\n[P2]\nThe API shall not log the call.\n";
    // A purpose has no formal reading: the statement that holds one is rejected.
    let report = check(text);
    assert!(report["opaque"].as_array().unwrap().iter().any(|d| d["code"] == "UNSUPPORTED_SEMANTICS" && d["message"].as_str().unwrap().contains("so that")), "{report}");
    let model = model("[P1]\nThe API shall log the call so that the auditor reviews the call.\n");
    assert!(model.contains("Act(API|log call)"), "{model}");
    assert!(!model.contains("so that"), "{model}");
}

#[test]
fn a_proportion_is_not_read_as_a_duration() {
    let report = check("[Q1]\nThe API shall respond within 200 ms for 99.9 percent of requests.\n");
    assert_eq!(report_codes(&report), ["UNSUPPORTED_SEMANTICS"], "{report}");
    assert!(report["diagnostics"][0]["message"].as_str().unwrap().contains("proportion"));
    // A time after `for` is still a duration.
    assert!(model("[W] The API shall wait for 5 seconds.\n").contains("duration"));
}

#[test]
fn has_and_have_are_one_verb() {
    let model = model("[M1]\nWhen an accepted construct has no supported formal interpretation, the compiler shall report the construct.\n\n[M2]\nWhen the accepted constructs have no supported formal interpretation, the compiler shall stop.\n");
    assert!(model.contains("accepted construct have no supported formal interpretation"), "{model}");
    assert!(!model.contains(" ha no "), "{model}");
}
