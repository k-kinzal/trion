//! What a result is about, and when a saved result holds (plan W13).
//!
//! A result names its subject: the package, the digests of its inputs and obligations, and the bounds of its
//! obligations. A saved result is a result about its own subject only, and
//! `trioc prove --against` compares each field.

mod common;
use common::*;
use serde_json::Value;

const MANIFEST: (&str, &str) = ("trion.toml", "[package]\nname = \"x\"\n");
const TEXT: &str = "primitive API\n\n[A]\nThe API shall stop.\n";

fn subject(report: &Value) -> &Value {
    &report["proof"]["subject"]
}

#[test]
fn a_report_names_what_it_is_about() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", TEXT)]);
    let first = f.verify(&["--json"]).json();
    let again = f.verify(&["--json"]).json();
    // The same text, rules, programs and settings: the same subject.
    assert_eq!(subject(&first), subject(&again));
    assert_eq!(subject(&first)["package"], "x");
    assert_eq!(subject(&first)["input_digest"].as_str().unwrap().len(), 64);
    assert_eq!(
        subject(&first)["obligations_digest"]
            .as_str()
            .unwrap()
            .len(),
        64
    );
    assert_eq!(subject(&first)["moments"], 3);
    // Another bound is another subject.
    let longer = f.verify(&["--json", "--trace-length", "4"]).json();
    assert_eq!(subject(&longer)["moments"], 4);
    assert_eq!(
        subject(&first)["input_digest"],
        subject(&longer)["input_digest"]
    );
    // Another text is another subject.
    f.write(
        "a.trion",
        &wrap("x", "primitive API\n\n[A]\nThe API shall not stop.\n"),
    );
    let other = f.verify(&["--json"]).json();
    assert_ne!(
        subject(&first)["input_digest"],
        subject(&other)["input_digest"]
    );
    // The declarations of a package decide which reading applies, not another set of rules.
    let typed = Fixture::new(&[MANIFEST, ("a.trion", "individuals user\nprimitive API\n\n[A]\nWhen a user enters, the API shall greet the user.\n")]);
    assert_eq!(subject(&typed.verify(&["--json"]).json())["individuals"], 3);
}

/// The message of the refusal of a saved result.
fn stale(report: &Value) -> String {
    report["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .find(|d| d["code"] == "result-stale")
        .map(|d| d["message"].as_str().unwrap().to_string())
        .unwrap_or_else(|| panic!("no result-stale: {report}"))
}

#[test]
fn a_saved_result_about_another_subject_is_refused() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", TEXT)]);
    let saved = f.verify(&["--json"]);
    assert_eq!(saved.code, 0);
    // What `trioc prove --json` writes is the saved result.
    let proof = saved.json()["proof"].clone();
    f.write("saved.json", &proof.to_string());
    // The same subject: the saved result holds.
    let same = f.verify(&["--json", "--against", "saved.json"]);
    assert_eq!(same.code, 0, "{}", same.stdout);
    assert_verified(&same.json());
    // Another setting.
    let longer = f.verify(&["--json", "--against", "saved.json", "--trace-length", "4"]);
    assert_ne!(longer.code, 0);
    let message = stale(&longer.json());
    assert!(
        message.contains("moments (`4` here, `3` saved)"),
        "{message}"
    );
    // Another text.
    f.write(
        "a.trion",
        &wrap(
            "x",
            "primitive API\n\n[A]\nThe API shall stop.\n\n[B]\nThe API may wait.\n",
        ),
    );
    let edited = f.verify(&["--json", "--against", "saved.json"]);
    assert_ne!(edited.code, 0);
    assert!(unverified(&edited.json()).contains(&"result-stale".to_string()));
    assert!(
        stale(&edited.json()).contains("input_digest ("),
        "{}",
        edited.stdout
    );
    // A result whose other fields are kept while one is changed.
    let mut altered = proof.clone();
    altered["subject"]["obligations_digest"] = Value::String("different obligations".to_string());
    f.write("a.trion", &wrap("x", TEXT));
    f.write("altered.json", &altered.to_string());
    let refused = f.verify(&["--json", "--against", "altered.json"]);
    assert_ne!(refused.code, 0);
    assert!(
        stale(&refused.json()).contains("obligations_digest ("),
        "{}",
        refused.stdout
    );
    // A file that is no result.
    f.write("nothing.json", "{}");
    assert_ne!(f.verify(&["--json", "--against", "nothing.json"]).code, 0);
}
