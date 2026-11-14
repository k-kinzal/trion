//! What a result is about, and when a saved result holds (plan W13).
//!
//! A report names its subject: the digest of the texts, the semantic
//! version, the versions of the programs and the settings, and a key over
//! all of them. A saved report, a saved proof or a cache entry is a result
//! about its own subject only.

mod common;
use common::*;
use serde_json::Value;

const MANIFEST: (&str, &str) = ("trion.toml", "[package]\nname = \"x\"\n");
const TEXT: &str = "primitive API\n\n[A]\nThe API shall stop.\n";

fn subject(report: &Value) -> &Value {
    &report["outcome"]["subject"]
}

#[test]
fn a_report_names_what_it_is_about() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", TEXT)]);
    let first = f.trion(&["verify", "--json"]).json();
    let again = f.trion(&["verify", "--json"]).json();
    // The same text, rules, programs and settings: the same key.
    assert_eq!(subject(&first), subject(&again));
    assert_eq!(subject(&first)["semantics"], "0.1.0");
    assert_eq!(subject(&first)["checker"], "0.1.0");
    assert_eq!(subject(&first)["trace_length"], 3);
    assert_eq!(subject(&first)["prover"], serde_json::json!(["z3", "-in"]));
    // Another bound is another subject.
    let longer = f.trion(&["verify", "--json", "--trace-length", "4"]).json();
    assert_ne!(subject(&first)["key"], subject(&longer)["key"]);
    assert_eq!(subject(&first)["revision"], subject(&longer)["revision"]);
    // Another text is another subject.
    f.write("a.trion", &wrap("x", "primitive API\n\n[A]\nThe API shall not stop.\n"));
    let other = f.trion(&["verify", "--json"]).json();
    assert_ne!(subject(&first)["revision"], subject(&other)["revision"]);
    assert_ne!(subject(&first)["key"], subject(&other)["key"]);
    // The declarations of a package decide which reading applies, not another set of rules.
    let typed = Fixture::new(&[MANIFEST, ("a.trion", "individuals user\nprimitive API\n\n[A]\nWhen a user enters, the API shall greet the user.\n")]);
    assert_eq!(subject(&typed.trion(&["verify", "--json"]).json())["semantics"], "0.1.0");
}

#[test]
fn a_saved_result_about_another_subject_is_refused() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", TEXT)]);
    let saved = f.trion(&["verify", "--json"]);
    assert_eq!(saved.code, 0);
    f.write("saved.json", &saved.stdout);
    // The same subject: the saved result holds.
    let same = f.trion(&["verify", "--json", "--against", "saved.json"]);
    assert_eq!(same.code, 0, "{}", same.stdout);
    assert_verified(&same.json());
    // Another setting.
    let longer = f.trion(&["verify", "--json", "--against", "saved.json", "--trace-length", "4"]);
    assert_ne!(longer.code, 0);
    let message = longer.json()["diagnostics"].as_array().unwrap().iter().find(|d| d["code"] == "result-stale").map(|d| d["message"].as_str().unwrap().to_string()).unwrap();
    assert!(message.contains("trace_length (3 there, 4 here)"), "{message}");
    // Another text.
    f.write("a.trion", &wrap("x", "primitive API\n\n[A]\nThe API shall stop.\n\n[B]\nThe API may wait.\n"));
    let edited = f.trion(&["verify", "--json", "--against", "saved.json"]);
    assert_ne!(edited.code, 0);
    assert!(unverified(&edited.json()).contains(&"result-stale".to_string()));
    // A report whose key is kept while a field is changed.
    let mut altered: Value = serde_json::from_str(&saved.stdout).unwrap();
    altered["outcome"]["subject"]["semantics"] = Value::String("9.9.9".to_string());
    f.write("a.trion", &wrap("x", TEXT));
    f.write("altered.json", &altered.to_string());
    let refused = f.trion(&["verify", "--json", "--against", "altered.json"]);
    assert_ne!(refused.code, 0);
    assert!(refused.stdout.contains("semantics (\\\"9.9.9\\\" there"), "{}", refused.stdout);
    // A file that is no report.
    f.write("nothing.json", "{}");
    assert_ne!(f.trion(&["verify", "--json", "--against", "nothing.json"]).code, 0);
}
