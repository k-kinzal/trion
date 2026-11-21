//! The acceptance cases of the language: for each case,
//! `fixtures/acceptance/<ID>-<name>` holds a package and `CASE.toml` with
//! what the package means, why, and what a verification of it must say.
//!
//! The expectation of a case is written from the meaning of its statements
//! and is not taken from what the command prints. A case is `closed` when
//! the command meets the expectation, and `open` while it does not: an open
//! case names the work that closes it. The test fails when a closed case no
//! longer meets its expectation, and when an open case meets it and is
//! still listed as open, so the list says what holds today.

mod common;
use common::*;
use serde_json::Value;
use std::fs;
use std::path::Path;

fn copy_tree(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap().flatten() {
        let (path, target) = (entry.path(), to.join(entry.file_name()));
        if path.is_dir() {
            copy_tree(&path, &target);
        } else {
            fs::copy(&path, &target).unwrap();
        }
    }
}

fn strings(value: Option<&toml::Value>) -> Vec<String> {
    value.and_then(toml::Value::as_array).map(|items| items.iter().filter_map(|item| item.as_str().map(str::to_string)).collect()).unwrap_or_default()
}

/// The codes of every error of a report: of the conversion, in each of its
/// lists, and of the proof.
fn errors(report: &Value) -> Vec<String> {
    let mut out = Vec::new();
    for list in [&report["diagnostics"], &report["checker"], &report["opaque"], &report["ungrounded"], &report["inexpressible"], &report["sources"]["diagnostics"]] {
        out.extend(list.as_array().into_iter().flatten().filter(|d| d["severity"] == "error").filter_map(|d| d["code"].as_str().map(str::to_string)));
    }
    out
}

/// Where a run differs from the expectation of its case; empty when it meets it.
///
/// - `verified`: the package converts and every obligation of its MMT form
///   is proved; the exit code says the same.
/// - `diagnostics`: codes of errors that the conversion or the proof reports.
/// - `obligations`: the verdict of each named obligation.
fn differences(expect: &toml::Value, code: i32, report: &Value) -> Vec<String> {
    let mut out = Vec::new();
    let verdicts = verdicts(report);
    let errors = errors(report);
    if let Some(verified) = expect.get("verified").and_then(toml::Value::as_bool) {
        let found = report["conforms"] == true && !verdicts.is_empty() && verdicts.values().all(|v| v == "proved") && errors.is_empty();
        if found != verified {
            out.push(format!("the package is {}verified and {verified} is expected: {:?} {verdicts:?}", if found { "" } else { "not " }, errors));
        }
        // The exit code and the outcome say the same.
        if (code == 0) != verified {
            out.push(format!("the exit code is {code} where verified is expected to be {verified}"));
        }
    }
    for code in strings(expect.get("diagnostics")) {
        if !errors.contains(&code) {
            out.push(format!("no error has the code `{code}`: {errors:?}"));
        }
    }
    for (name, verdict) in expect.get("obligations").and_then(toml::Value::as_table).into_iter().flatten() {
        let found = verdicts.get(name.as_str());
        if found.map(String::as_str) != verdict.as_str() {
            out.push(format!("the obligation `{name}` is {found:?} and {verdict} is expected"));
        }
    }
    out
}

#[test]
fn each_acceptance_case_is_met_or_is_listed_as_open_with_the_work_that_closes_it() {
    let root = repo_root().join("crates/trion-cli/fixtures/acceptance");
    let mut names: Vec<String> = fs::read_dir(&root).unwrap().flatten().filter(|e| e.path().is_dir()).map(|e| e.file_name().to_string_lossy().into_owned()).collect();
    names.sort();
    assert!(!names.is_empty());
    let mut failures = Vec::new();
    for name in names {
        let dir = root.join(&name);
        let case: toml::Value = toml::from_str(&fs::read_to_string(dir.join("CASE.toml")).unwrap()).unwrap_or_else(|e| panic!("{name}/CASE.toml: {e}"));
        // A case says what its statements mean before it says what is expected.
        for field in ["id", "title", "work", "status", "reason"] {
            assert!(case.get(field).and_then(toml::Value::as_str).is_some_and(|text| !text.trim().is_empty()), "{name}: the case has no `{field}`");
        }
        let expect = case.get("expect").unwrap_or_else(|| panic!("{name}: the case expects nothing"));
        assert!(expect.get("verified").is_some(), "{name}: the case does not say whether the package is verified");
        let work = tempfile::tempdir().unwrap();
        copy_tree(&dir.join("package"), work.path());
        let arguments = strings(case.get("args"));
        let arguments: Vec<&str> = arguments.iter().map(String::as_str).collect();
        let result = verify_in(work.path(), &arguments);
        // A run without a report meets no expectation: a parse error or a missing prover is no refutation.
        let Ok(report) = serde_json::from_str::<Value>(&result.stdout) else {
            failures.push(format!("{name}: the command printed no report (exit code {}): {}", result.code, result.stderr));
            continue;
        };
        let found = differences(expect, result.code, &report);
        match case["status"].as_str().unwrap() {
            "closed" if !found.is_empty() => failures.push(format!("{name} is closed and is not met:\n  {}", found.join("\n  "))),
            "open" if found.is_empty() => failures.push(format!("{name} is met: write `status = \"closed\"` in its CASE.toml")),
            "open" | "closed" => {}
            other => failures.push(format!("{name}: the status `{other}` is neither `open` nor `closed`")),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn a_report_is_a_success_only_when_every_part_of_it_says_so() {
    // The common assertion of a success reads every list of a report, and
    // not the diagnostics alone.
    let clean = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "primitive API\n\n[A]\nThe API shall stop.\n")]).verify(&["--json"]);
    assert_eq!(clean.code, 0, "{}", clean.stdout);
    assert_verified(&clean.json());
    // A quality that nothing defines leaves the diagnostics of the reading
    // empty, and it is no success: the package does not convert, and nothing is proved.
    let quality = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "primitive API\n\n[G]\nThe API shall be secure.\n")]).verify(&["--json"]);
    assert_eq!(quality.code, 1, "{}", quality.stdout);
    let report = quality.json();
    assert!(analysis_codes(&report).is_empty(), "{report}");
    assert_eq!(unverified(&report), ["inexpressible-property"], "{report}");
    assert!(report["proof"].is_null(), "{report}");
    // The text says the same as the report.
    let text = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "primitive API\n\n[G]\nThe API shall be secure.\n")]).verify(&[]).stdout;
    assert!(text.contains("error[inexpressible-property]") && text.trim_end().ends_with("\ndoes not conform"), "{text}");
    let text = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "primitive API\n\n[A]\nThe API shall stop.\n")]).verify(&[]).stdout;
    assert!(text.contains("obligation consistency (consistency): proved") && text.contains("within traces of 3 moments") && text.contains("no result holds beyond its bound"), "{text}");
    assert!(text.trim_end().ends_with("\nproved"), "{text}");
}

#[test]
fn a_construct_that_a_rule_names_and_gives_no_meaning_stops_the_verification() {
    // Each of these was accepted and verified: the parser reads the form,
    // and what it says reached no formula or only a part of a name. The
    // ledger of patterns lists each with the work that gives it a meaning.
    const TERMS: &str = "primitive API\nprimitive client\nprimitive message\nprimitive file\nprimitive header\nprimitive deadline\nprimitive proof\nprimitive token\nprimitive door\nprimitive user\nprimitive profile\nprimitive report\n\n";
    let verify = |text: &str| Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &format!("{TERMS}{text}"))]).verify(&["--json"]);
    for (rule, text) in [
        ("role-rate", "[A]\nThe API shall send at most 3 messages per second.\n"),
        ("role-exclusion", "[A]\nThe API shall send the file except the header.\n"),
        ("role-by", "[A]\nThe API shall respond by the deadline.\n"),
        ("predicate-able-to", "[A]\nThe client is able to retry.\n"),
        ("content-of-noun", "[A]\nThe API shall store the proof that the token is valid.\n"),
        ("frame-before", "[A]\nBefore the door opens, the API shall stop.\n"),
        ("frame-counted-event", "[A]\nAfter 3 failed retries, the API shall stop.\n"),
        ("frame-counted-event", "[A]\nWhen 3 users join, the API shall stop.\n"),
        ("subject-counted-descriptive", "[A]\nAt most 5 users have a profile.\n"),
        ("object-zero-or-more", "[A]\nThe API shall send zero or more reports.\n"),
    ] {
        let run = verify(text);
        let report = run.json();
        assert_eq!(run.code, 1, "{text}{report}");
        let named = report["opaque"].as_array().unwrap().iter().any(|d| d["code"] == "UNSUPPORTED_SEMANTICS" && d["message"].as_str().unwrap().contains(&format!("(`{rule}`)")));
        assert!(named, "{text}no error names `{rule}`: {}", report["opaque"]);
        assert!(unverified(&report).contains(&"UNSUPPORTED_SEMANTICS".to_string()), "{report}");
    }
    // The forms that say the same and are read stay accepted.
    for text in [
        "[A]\nThe API shall stop before the door opens.\n",
        "[A]\nWhen the door opens, the API shall respond within 5 seconds.\n",
        "A guest means a user without a profile.\n\n[A]\nThe API shall greet the guest.\n",
        "[A]\nThere are at most 5 users.\n\n[B]\nThe API shall greet each user.\n",
    ] {
        let report = verify(text).json();
        assert!(report["opaque"].as_array().unwrap().is_empty(), "{text}{}", report["opaque"]);
    }
}
