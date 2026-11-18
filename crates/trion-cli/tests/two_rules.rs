//! The two rules of the language (AGENTS.md) against each sentence pattern:
//! a simple sentence is exactly one contract, and composite vocabulary
//! rewrites a sentence into simple sentences and has no meaning of its own.
//! Each reading example of the catalog states a pattern, and the conversion
//! holds each example to both rules; `--properties` holds every statement of
//! a package to them. `TRION_FAULT` seeds a reader that breaks a rule, so
//! that the check is seen to fail.

mod common;
use common::*;

/// A package with one reading example of the pattern of `input`.
fn example(input: &str, expect: &[&str]) -> Fixture {
    let expect: String = expect.iter().map(|line| format!("    expect \"{line}\"\n")).collect();
    let text = format!("namespace p\nsystem API\nprimitive API, message\n\nexample PATTERN:\n    kind reading\n    form contract\n    input \"{input}\"\n{expect}");
    Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &text)])
}

fn codes(run: &Result) -> Vec<String> {
    let report = run.json();
    report["diagnostics"].as_array().into_iter().chain(report["checker"].as_array()).flatten().map(|d| d["code"].as_str().unwrap_or_default().to_string()).collect()
}

const SIMPLE: (&str, &[&str]) = ("The API shall store the message.", &["assume: ⊤", "guarantee: (Act(API|store message) ∧ ¬Forbid(API|store message) ∧ ¬Discouraged(API|store message))"]);
const COMPOSITE: (&str, &[&str]) = (
    "The API shall store the message and log the message.",
    &[
        "assume: ⊤",
        "guarantee: (Act(API|store message) ∧ ¬Forbid(API|store message) ∧ ¬Discouraged(API|store message))",
        "assume: ⊤",
        "guarantee: (Act(API|log message) ∧ ¬Forbid(API|log message) ∧ ¬Discouraged(API|log message))",
    ],
);

#[test]
fn each_reading_example_holds_the_two_rules() {
    for (input, expect) in [SIMPLE, COMPOSITE] {
        let run = example(input, expect).convert(&["--json"]);
        assert_eq!(run.code, 0, "{input}: {}{}", run.stdout, run.stderr);
        assert!(codes(&run).iter().all(|code| !["sentence-not-one-contract", "composite-not-its-expansion", "example-failed"].contains(&code.as_str())), "{input}: {}", run.stdout);
    }
}

#[test]
fn a_pattern_that_reads_a_simple_sentence_as_two_contracts_is_refused() {
    let (input, expect) = SIMPLE;
    let f = example(input, expect);
    let run = verify_with(f.path(), &["--json"], &[("TRION_FAULT", "one-contract")]);
    assert_ne!(run.code, 0, "{}", run.stdout);
    assert!(codes(&run).contains(&"sentence-not-one-contract".to_string()), "{}", run.stdout);
}

#[test]
fn a_pattern_that_gives_composite_vocabulary_a_meaning_of_its_own_is_refused() {
    let (input, expect) = COMPOSITE;
    let f = example(input, expect);
    let run = verify_with(f.path(), &["--json"], &[("TRION_FAULT", "expansion")]);
    assert_ne!(run.code, 0, "{}", run.stdout);
    assert!(codes(&run).contains(&"composite-not-its-expansion".to_string()), "{}", run.stdout);
    // A simple sentence has no expansion to compare.
    let (input, expect) = SIMPLE;
    let simple = example(input, expect);
    let run = verify_with(simple.path(), &["--json"], &[("TRION_FAULT", "expansion")]);
    assert!(!codes(&run).contains(&"composite-not-its-expansion".to_string()), "{}", run.stdout);
}

#[test]
fn every_statement_of_the_specification_of_trion_holds_the_two_rules() {
    let run = convert_in(&repo_root(), &["--json", "--properties"]);
    let found: Vec<String> = codes(&run).into_iter().filter(|code| code == "sentence-not-one-contract" || code == "composite-not-its-expansion").collect();
    assert!(found.is_empty(), "{found:?}");
    assert!(run.json()["demonstrations"].as_array().is_some_and(|d| d.len() > 100), "{}", run.stdout);
}
