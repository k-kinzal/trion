mod common;

use common::{verify_in, Fixture};
use serde_json::Value;
use std::{fs, process::Command};

#[test]
fn propositional_checks_are_decided_from_the_mmt_form() {
    let fixture = Fixture::new(&[
        ("trion.toml", "[package]\nname = \"cards\"\n"),
        (
            "checks.trion",
            r#"
check VALID:
    grammar "propositional-cnl/1"
    input "proposition P. proposition Q. assume P implies Q. assume P. entails Q."
check ALTERNATE-SPELLING:
    grammar "propositional-cnl/2"
    input "proposition P. proposition Q. assume if P then Q. assume P. entails Q."
check CONVERSE:
    grammar "propositional-cnl/1"
    input "proposition P. proposition Q. assume P implies Q. assume Q. entails P."
check VACUOUS:
    grammar "propositional-cnl/1"
    input "proposition P. assume P. assume not P. entails false."
check EMPTY-MODEL:
    grammar "propositional-cnl/1"
    input "satisfiable."
check FALSE-TARGET:
    grammar "propositional-cnl/1"
    input "entails false."
"#,
        ),
    ]);
    let converted = fixture.convert(&["--out", "archive", "--json"]);
    assert_eq!(converted.code, 0, "{}{}", converted.stdout, converted.stderr);
    let conversion = converted.json();
    let obligations = conversion["obligations"].as_array().unwrap();
    let proof = fixture.prove(&["archive", "--json"]);
    assert_eq!(proof.code, 1, "{}{}", proof.stdout, proof.stderr);
    let report = proof.json();
    let results = report["results"].as_array().unwrap();
    assert_eq!(obligations.len(), results.len());
    for (declared, decided) in obligations.iter().zip(results) {
        assert_eq!(declared["name"], decided["obligation"]);
        assert_eq!(declared["proposition"], decided["proposition"]);
    }
    let check = |name| {
        results
            .iter()
            .find(|result| result["obligation"] == format!("check/{name}"))
            .unwrap_or_else(|| panic!("missing {name}: {report}"))
    };
    for name in ["VALID", "ALTERNATE-SPELLING", "EMPTY-MODEL"] {
        assert_eq!(check(name)["verdict"], "proved");
    }
    assert_eq!(
        check("VALID")["proposition"],
        check("ALTERNATE-SPELLING")["proposition"]
    );
    for name in ["CONVERSE", "VACUOUS", "FALSE-TARGET"] {
        assert_eq!(check(name)["verdict"], "refuted");
    }
    assert_eq!(check("CONVERSE")["questions"], 2);
    assert_eq!(check("VACUOUS")["questions"], 1);
    let outcome = |name| &check(name)["propositional"]["outcome"];
    assert_eq!(outcome("VALID")["evidence"], "exhaustive");
    assert_eq!(outcome("VALID")["reference_assignments"], 4);
    assert_eq!(outcome("CONVERSE")["conclusion"], "does_not_entail");
    assert_eq!(outcome("CONVERSE")["evidence"]["checked_counterexample"], serde_json::json!([false, true]));
    assert_eq!(outcome("FALSE-TARGET")["evidence"]["checked_counterexample"], serde_json::json!([]));
    assert_eq!(outcome("VACUOUS")["premises"], "contradictory");
    assert_eq!(outcome("VACUOUS")["conclusion"], "entails");
    assert_eq!(check("VACUOUS")["reason"], "vacuous entailment: contradictory premises");
    assert_eq!(check("ALTERNATE-SPELLING")["propositional"]["input"]["input"]["grammar"], "propositional-cnl/2");

    let text = fixture.prove(&["archive"]);
    assert!(text.stdout.contains("counterexample: P=false, Q=true"), "{}", text.stdout);
    assert!(text.stdout.contains("counterexample: empty valuation"), "{}", text.stdout);
    assert!(text.stdout.contains("vacuous entailment: contradictory premises"), "{}", text.stdout);

    fixture.write("proof.json", &proof.stdout);
    let replay = |record| Command::new(env!("CARGO_BIN_EXE_trioc"))
        .current_dir(fixture.path())
        .args(["replay", record, "--form", "archive"])
        .output().unwrap();
    assert!(replay("proof.json").status.success());
    let mut damaged = report.clone();
    let entries = damaged["results"].as_array_mut().unwrap();
    let counterpart = entries.iter().find(|result| result["obligation"] == "check/VALID")
        .unwrap()["propositional"].clone();
    let converse = entries.iter_mut().find(|result| result["obligation"] == "check/CONVERSE").unwrap();
    converse["propositional"]["answers"][1] = counterpart["answers"][1].clone();
    fixture.write("damaged.json", &damaged.to_string());
    let rejected = replay("damaged.json");
    assert_eq!(rejected.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&rejected.stderr).contains("saved evidence disagrees with replay"));

    for (field, replacement) in [
        ("reason", serde_json::json!("an unrelated reason")),
        ("questions", serde_json::json!(999)),
        ("counterexamples", serde_json::json!([{"facts": ["an invented fact"], "statements": []}])),
    ] {
        let mut damaged = report.clone();
        let result = damaged["results"].as_array_mut().unwrap().iter_mut()
            .find(|result| result["obligation"] == "check/CONVERSE").unwrap();
        result[field] = replacement;
        fixture.write("damaged.json", &damaged.to_string());
        let rejected = replay("damaged.json");
        assert_eq!(rejected.status.code(), Some(2), "{field}: {rejected:?}");
        assert!(String::from_utf8_lossy(&rejected.stderr).contains("saved evidence disagrees with replay"));
    }

    let source = fixture.read("archive/source/specification.mmt");
    let mut form = trioc_cli::mmt::Form::read(&source).unwrap();
    let position = form.obligations.obligations.iter().position(|item| item.name == "check/CONVERSE").unwrap();
    let trion_verification::ObligationQuestion::All { parts } = &form.obligations.obligations[position].question else {
        panic!("an entailment has two questions");
    };
    let trion_verification::ObligationQuestion::Unsatisfiable { query } = &parts[1] else {
        panic!("the counterexample question checks unsatisfiability");
    };
    form.obligations.pool[*query.last().unwrap()] = trion_solver::Formula::True;
    assert!(form.write().unwrap_err().contains("does not match the questions of its original Core input"));
}

#[test]
fn a_propositional_check_rejects_input_outside_its_pinned_grammar() {
    let fixture = Fixture::new(&[
        ("trion.toml", "[package]\nname = \"cards\"\n"),
        (
            "checks.trion",
            r#"
check WRONG-VERSION:
    grammar "propositional-cnl/1"
    input "entails if true then true."
check UNDECLARED:
    grammar "propositional-cnl/1"
    input "entails R."
"#,
        ),
    ]);
    let result = verify_in(fixture.path(), &["--json"]);
    assert_eq!(result.code, 1, "{}{}", result.stdout, result.stderr);
    let report = result.json();
    assert!(report["proof"].is_null(), "{report}");
    let diagnostics = report["diagnostics"].as_array().unwrap();
    for status in ["unsupported propositional input", "invalid propositional input"] {
        assert!(diagnostics.iter().any(|d| d["message"].as_str().is_some_and(|m| m.contains(status))), "{report}");
    }
}

#[test]
fn mmt_propositional_proof_reports_limits_and_checked_certificates() {
    let fixture = Fixture::new(&[
        ("trion.toml", "[package]\nname = \"limits\"\n"),
        ("checks.trion", r#"
check SEARCH:
    grammar "propositional-cnl/1"
    input "proposition P. proposition Q. assume P or Q. satisfiable."
check LARGE:
    grammar "propositional-cnl/1"
    input "proposition A. proposition B. proposition C. proposition D. proposition E. proposition F. proposition G. proposition H. proposition I. proposition J. proposition K. proposition L. proposition M. entails true."
"#),
    ]);
    let run = verify_in(fixture.path(), &["--decision-limit", "0", "--json"]);
    assert_eq!(run.code, 1, "{}{}", run.stdout, run.stderr);
    let report = run.json();
    let result = |name| report["proof"]["results"].as_array().unwrap().iter()
        .find(|result| result["obligation"] == format!("check/{name}")).unwrap();
    let search = result("SEARCH");
    assert_eq!(search["verdict"], "unproved");
    assert_eq!(search["propositional"]["decision_limit"], 0);
    assert_eq!(search["propositional"]["outcome"]["execution"], "resource_limit");
    assert_eq!(search["propositional"]["outcome"]["conclusion"], "none");
    let large = result("LARGE");
    assert_eq!(large["verdict"], "proved");
    assert_eq!(large["propositional"]["scope"], "all_valuations");
    assert_eq!(large["propositional"]["approximation"], "exact");
    assert_eq!(large["propositional"]["outcome"]["evidence"], "checked_certificate");
    assert!(large["propositional"]["outcome"]["reference_assignments"].is_null());
}

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
