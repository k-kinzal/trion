use serde_json::Value;
use std::{fs, process::Command};

#[test]
fn propositional_formalize_analyze_and_replay_use_the_pinned_artifact() {
    let temp = tempfile::tempdir().unwrap();
    let fixture = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/fixtures/propositional/card.cnl"
    );
    let accepted = Command::new(env!("CARGO_BIN_EXE_trion"))
        .args(["formalize", fixture])
        .output()
        .unwrap();
    assert!(accepted.status.success(), "{accepted:?}");
    let subject = temp.path().join("accepted.json");
    fs::write(&subject, &accepted.stdout).unwrap();

    let analyzed = Command::new(env!("CARGO_BIN_EXE_trioc"))
        .args(["analyze"])
        .arg(&subject)
        .output()
        .unwrap();
    assert!(analyzed.status.success(), "{analyzed:?}");
    let record: Value = serde_json::from_slice(&analyzed.stdout).unwrap();
    assert_eq!(record["artifact"]["grammar"], "propositional-cnl/1");
    assert_eq!(record["analysis"]["outcome"]["conclusion"], "entails");
    assert_eq!(record["analysis"]["outcome"]["evidence"], "exhaustive");
    assert_eq!(record["analysis"]["outcome"]["reference_assignments"], 4);
    let saved = temp.path().join("record.json");
    fs::write(&saved, &analyzed.stdout).unwrap();
    let replayed = Command::new(env!("CARGO_BIN_EXE_trioc"))
        .args(["replay"])
        .arg(&saved)
        .output()
        .unwrap();
    assert!(replayed.status.success(), "{replayed:?}");
    assert_eq!(replayed.stdout, b"entails\n");

    let timed = Command::new(env!("CARGO_BIN_EXE_trioc"))
        .args(["analyze", "--timeout-ms", "0"])
        .arg(&subject)
        .output()
        .unwrap();
    assert!(!timed.status.success());
    let timed: Value = serde_json::from_slice(&timed.stdout).unwrap();
    assert_eq!(timed["analysis"]["outcome"]["execution"], "timeout");
    assert_eq!(timed["analysis"]["outcome"]["conclusion"], "none");

    let damaged = String::from_utf8(analyzed.stdout).unwrap().replace(
        "\"premises\":\"consistent\"",
        "\"premises\":\"consistent\",\"premises\":\"consistent\"",
    );
    fs::write(&saved, damaged).unwrap();
    let rejected = Command::new(env!("CARGO_BIN_EXE_trioc"))
        .args(["replay"])
        .arg(&saved)
        .output()
        .unwrap();
    assert!(!rejected.status.success(), "{rejected:?}");
}

#[test]
fn propositional_reports_contradiction_and_refuses_non_artifacts() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("contradictory.cnl");
    fs::write(
        &source,
        "proposition P. assume P. assume not P. entails true.",
    )
    .unwrap();
    let accepted = Command::new(env!("CARGO_BIN_EXE_trion"))
        .args(["formalize"])
        .arg(&source)
        .output()
        .unwrap();
    assert!(accepted.status.success(), "{accepted:?}");
    let subject = temp.path().join("accepted.json");
    fs::write(&subject, accepted.stdout).unwrap();
    let analyzed = Command::new(env!("CARGO_BIN_EXE_trioc"))
        .args(["analyze"])
        .arg(&subject)
        .output()
        .unwrap();
    assert!(!analyzed.status.success());
    assert_eq!(
        analyzed.stderr,
        b"vacuous entailment: contradictory premises\n"
    );
    let record: Value = serde_json::from_slice(&analyzed.stdout).unwrap();
    assert_eq!(record["analysis"]["outcome"]["conclusion"], "entails");
    assert_eq!(record["analysis"]["outcome"]["premises"], "contradictory");

    fs::write(&source, "entails always true.").unwrap();
    let unsupported = Command::new(env!("CARGO_BIN_EXE_trion"))
        .args(["formalize"])
        .arg(&source)
        .output()
        .unwrap();
    assert!(!unsupported.status.success());
    let report: Value = serde_json::from_slice(&unsupported.stdout).unwrap();
    assert_eq!(report["status"], "unsupported");
    fs::write(&subject, unsupported.stdout).unwrap();
    let refused = Command::new(env!("CARGO_BIN_EXE_trioc"))
        .args(["analyze"])
        .arg(&subject)
        .output()
        .unwrap();
    assert!(!refused.status.success());
}

#[test]
fn propositional_replays_the_saved_example() {
    let fixture = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/fixtures/propositional/card.analysis.json"
    );
    let replayed = Command::new(env!("CARGO_BIN_EXE_trioc"))
        .args(["replay", fixture])
        .output()
        .unwrap();
    assert!(replayed.status.success(), "{replayed:?}");
    assert_eq!(replayed.stdout, b"entails\n");
}
