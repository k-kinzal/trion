//! What a verification result states: the verdict of each obligation, its
//! subject and bounds, the statements of a conflict and the results that
//! the bounds leave unproved.
//!
//! Retired with the engine of `trioc check`, because the proof of the MMT
//! form does not state them: whether a search was exhaustive and how many
//! decisions it took, the assumptions, profile and method of a result, the
//! decision limit as a part of the subject (it decides only whether an
//! answer is found, never what it means), and the scopes, expansion, terms,
//! derivation and definitions of a conflict.

mod common;
use common::*;
use serde_json::Value;

const CONFLICT: &str = "[A] The API shall return foo.\n[B] The API shall not return foo.\n";
const CHOICE: &str = "primitive API\nprimitive call\n[C] The API shall either accept the call or reject the call.\n";

fn fixture(text: &str) -> Fixture {
    Fixture::new(&[("trion.toml", MANIFEST), ("spec.trion", text)])
}

fn check(text: &str, limit: Option<&str>) -> (i32, Value) {
    let f = fixture(text);
    let mut args = vec!["--json"];
    if let Some(limit) = limit {
        args.extend(["--decision-limit", limit]);
    }
    let result = f.verify(&args);
    (result.code, result.json())
}

fn text_report(text: &str, args: &[&str]) -> (i32, String) {
    let result = fixture(text).verify(args);
    (result.code, result.stdout)
}

/// The verdict of an obligation of a report.
fn verdict(report: &Value, obligation: &str) -> String {
    verdicts(report).get(obligation).cloned().unwrap_or_else(|| "absent".to_string())
}

/// A package of one statement that is decided without a search.
const ONE: &str = "primitive API, foo\n[A] The API shall return foo.\n";

#[test]
fn a_consistency_result_has_one_of_three_statuses() {
    let status = |text: &str, limit: Option<&str>| verdict(&check(text, limit).1, "consistency");
    assert_eq!(status(ONE, None), "proved");
    assert_eq!(status(CONFLICT, None), "refuted");
    assert_eq!(status(CHOICE, Some("0")), "unproved");
    // The same input is decided once the bound leaves room for the search.
    assert_eq!(status(CHOICE, Some("100")), "proved");
}

#[test]
fn compatibility_without_requirements_asks_whether_an_environment_exists() {
    let (_, allowed) = check("primitive delay\nThe delay is at most 5 seconds.\n", None);
    assert_eq!(verdict(&allowed, "compatibility"), "proved");
    let (_, excluded) = check("primitive delay\nThe delay is at least 6 seconds.\nThe delay is at most 5 seconds.\n", None);
    assert_eq!(verdict(&excluded, "compatibility"), "refuted");
}

#[test]
fn the_checker_publishes_the_verdict_of_the_status() {
    // A refuted consistency names the statements that cannot all be kept.
    let (_, report) = check(CONFLICT, None);
    assert_eq!(verdict(&report, "consistency"), "refuted");
    let conflict = report["diagnostics"].as_array().unwrap().iter().find(|d| d["code"] == "contradiction").unwrap_or_else(|| panic!("{report}"));
    let named: Vec<&str> = conflict["refs"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap()).collect();
    assert_eq!(named, ["A", "B"], "{report}");
    let (_, printed) = text_report(CONFLICT, &[]);
    assert!(printed.contains("obligation consistency (consistency): refuted") && printed.trim_end().ends_with("\nnot proved"), "{printed}");
}

#[test]
fn a_search_that_the_bounds_end_is_unknown_and_no_success() {
    let (code, report) = check(CHOICE, Some("0"));
    assert_eq!(verdict(&report, "consistency"), "unproved");
    assert_eq!(report_codes(&report), ["obligation-unproved"]);
    assert_eq!(code, 1, "an unknown result must not pass");
    let (code, printed) = text_report(CHOICE, &["--decision-limit", "0"]);
    assert_eq!(code, 1, "{printed}");
    assert!(printed.contains("obligation consistency (consistency): unproved") && printed.trim_end().ends_with("\nnot proved"), "{printed}");
    assert_eq!(check(CHOICE, None).0, 0);
}

#[test]
fn a_result_names_its_revision_assumptions_profile_method_and_bounds() {
    let (_, report) = check("[A] The status is open or closed.\n[B] While the status is open, the API shall stop.\n", Some("50"));
    let subject = &report["proof"]["subject"];
    let revision = subject["revision"].as_str().unwrap();
    assert!(revision.len() >= 12 && revision.chars().all(|c| c.is_ascii_hexdigit()), "{revision}");
    assert_eq!(subject["moments"], 3, "{subject}");
    assert!(subject["semantics"].as_str().is_some_and(|s| !s.is_empty()) && subject["tool"].as_str().is_some_and(|s| !s.is_empty()), "{subject}");
    // Each result states the bound of its proposition.
    for result in report["proof"]["results"].as_array().unwrap() {
        assert!(result["proposition"].as_str().unwrap().starts_with("within traces of 3 moments"), "{result}");
    }
    // A changed specification is another subject.
    let (_, other) = check(ONE, None);
    assert_ne!(other["proof"]["subject"]["revision"], subject["revision"]);
    let (_, printed) = text_report(ONE, &["--decision-limit", "7"]);
    assert!(printed.contains("within traces of 3 moments") && printed.contains("no result holds beyond its bound"), "{printed}");
}

#[test]
fn a_bounded_result_states_its_bounds_and_claims_no_more_than_its_search() {
    // The bound ends the search: the result decides nothing.
    let (_, cut) = check(CHOICE, Some("0"));
    assert_eq!(verdict(&cut, "consistency"), "unproved");
    // The search ends inside the bound: the result is proved.
    let (_, whole) = check(CHOICE, Some("100"));
    assert_eq!(verdict(&whole, "consistency"), "proved");
    // A conflict that the bound hides is not reported as consistency.
    let hidden = format!("{CHOICE}[D] The API shall not accept the call.\n[E] The API shall not reject the call.\n");
    assert_eq!(verdict(&check(&hidden, None).1, "consistency"), "refuted");
    assert_ne!(verdict(&check(&hidden, Some("0")).1, "consistency"), "proved");
}

#[test]
fn a_broken_recommendation_is_not_an_inconsistency() {
    let (code, soft) = check("[A] The API should return foo.\n[B] The API shall not return foo.\n", None);
    assert_eq!(report_codes(&soft), ["recommendation-violation"]);
    assert_eq!(verdict(&soft, "consistency"), "proved");
    assert_eq!(code, 1);
    let (_, hard) = check(CONFLICT, None);
    assert_eq!(report_codes(&hard), ["contradiction"]);
    assert_eq!(verdict(&hard, "consistency"), "refuted");
    // Both kinds in one specification are reported apart.
    let (_, both) = check(&format!("{CONFLICT}[C] The API should stop.\n[D] The API shall not stop.\n"), None);
    let mut codes = report_codes(&both);
    codes.sort();
    assert_eq!(codes, ["contradiction", "recommendation-violation"]);
    let ids = |code: &str| -> Vec<String> { both["diagnostics"].as_array().unwrap().iter().filter(|d| d["code"] == code).flat_map(|d| d["refs"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap().to_string())).collect() };
    assert_eq!(ids("contradiction"), ["A", "B"]);
    assert_eq!(ids("recommendation-violation"), ["C", "D"]);
}

#[test]
fn an_unreachable_condition_stays_in_the_coverage_explanation() {
    // No value outside the closed domain can occur, so [V] holds emptily.
    // (The explanation of coverage, with the condition and the statement
    // that excludes it, is retired with the engine.)
    let text = "[D] The status is open or closed.\n[A] While the status is open, the API shall stop.\n[B] While the status is closed, the API shall stop.\n[V] While the status is pending, the API shall log the call.\n";
    let (_, report) = check(text, None);
    // A statement that requires nothing in any situation is no
    // contradiction. Its vacuity is no fault that consistency,
    // compatibility, correctness or completeness finds (AGENTS.md, limit 2):
    // no finding names it.
    assert!(report_codes(&report).is_empty(), "{report}");
    assert_eq!(verdict(&report, "consistency"), "proved");
    assert_eq!(verdict(&report, "compatibility"), "proved");
}

// Every question is decided over the trace. `While the status is open, the
// API shall stop.` requires the stop at each moment of the interval and `The
// API shall stop.` at some moment, so those two are no equivalent sides. The
// two triggers below answer the same occurrences exactly when the status has
// no third value.
const CASES: &str = "[OPEN] When the status is open, the API shall stop.\n[NOT-CLOSED] When the status is not closed, the API shall stop.\n[CLOSED] When the status is closed, the API shall log the call.\n";

fn with_check(text: &str) -> String {
    format!("{text}check SAME:\n    relation equivalent\n    left [OPEN]\n    right [NOT-CLOSED]\n    using definitions\n")
}

#[test]
fn a_check_uses_the_definitions_that_its_operands_need() {
    // The two conditions are one condition only under the definition of the status.
    let (_, defined) = check(&with_check(&format!("[STATUS] The status is open or closed.\n{CASES}")), None);
    assert!(analysis_codes(&defined).is_empty(), "{defined}");
    assert_eq!(verdict(&defined, "check/SAME"), "proved");
    let (_, open) = check(&with_check(CASES), None);
    assert_eq!(analysis_codes(&open), ["check-refuted"]);
    assert_eq!(verdict(&open, "check/SAME"), "refuted");
}

#[test]
fn a_check_that_the_bounds_leave_open_is_unknown() {
    let text = with_check(&format!("[STATUS] The status is open or closed.\n{CASES}"));
    let (code, report) = check(&text, Some("0"));
    assert_eq!(verdict(&report, "check/SAME"), "unproved");
    assert!(report_codes(&report).contains(&"obligation-unproved".to_string()), "{report}");
    assert!(!report_codes(&report).contains(&"check-refuted".to_string()), "{report}");
    assert_eq!(code, 1);
    let (_, printed) = text_report(&text, &["--decision-limit", "0"]);
    assert!(printed.contains("obligation check/SAME (check): unproved"), "{printed}");
}

fn comparison(text: &str, base: &str, candidate: &str, expect: &str) -> String {
    format!("{text}example E:\n    kind comparison\n    base {base}\n    candidate {candidate}\n    using definitions\n    expect {expect}\n")
}

/// The verdict of the example `E`: `proved` when it observes what it
/// expects, `refuted` when it does not, `unproved` when the bounds leave it open.
fn observed(report: &Value) -> String {
    verdict(report, "example/E")
}

#[test]
fn a_comparison_reads_both_sides_in_one_environment() {
    // With the definition of the status, the base already requires the candidate.
    let defined = format!("[STATUS] The status is open or closed.\n{CASES}");
    let (_, report) = check(&comparison(&defined, "[OPEN]", "[NOT-CLOSED]", "redundant"), None);
    assert!(analysis_codes(&report).is_empty(), "{report}");
    // The same definition serves the other direction.
    let (_, report) = check(&comparison(&defined, "[NOT-CLOSED]", "[OPEN]", "redundant"), None);
    assert!(analysis_codes(&report).is_empty(), "{report}");
    // Without it, the candidate adds the case that the base statement does not cover.
    let (_, report) = check(&comparison(CASES, "[OPEN]", "[NOT-CLOSED]", "extension"), None);
    assert!(analysis_codes(&report).is_empty(), "{report}");
    // The bounds of the analysis hold for the base and the candidate alike.
    let (_, report) = check(&comparison(&defined, "[OPEN]", "[NOT-CLOSED]", "redundant"), Some("0"));
    assert_eq!(observed(&report), "unproved");
}

#[test]
fn a_comparison_with_an_undecided_base_is_unknown() {
    let text = comparison(&format!("{CHOICE}[N] The API shall log the call.\n"), "[C]", "[N]", "extension");
    assert!(report_codes(&check(&text, None).1).is_empty());
    let (_, report) = check(&text, Some("0"));
    assert_eq!(observed(&report), "unproved");
}

#[test]
fn a_comparison_without_the_needed_evidence_is_unknown() {
    // The base is decided by propagation alone; the candidate needs a search.
    let text = comparison(&format!("[N] The API shall log the call.\n{CHOICE}"), "[N]", "[C]", "extension");
    assert!(report_codes(&check(&text, None).1).is_empty());
    let (_, report) = check(&text, Some("0"));
    assert_eq!(observed(&report), "unproved");
    assert!(report_codes(&report).contains(&"obligation-unproved".to_string()), "{report}");
}

#[test]
fn an_unknown_result_satisfies_no_expectation() {
    let example = |expect: &str| format!("example E:\n    kind consistency\n    input \"The API shall either accept the call or reject the call.\"\n    expect {expect}\n");
    assert!(report_codes(&check(&example("consistent"), None).1).is_empty());
    for expect in ["consistent", "inconsistent"] {
        let (code, report) = check(&example(expect), Some("0"));
        assert_eq!(observed(&report), "unproved", "{expect}: {report}");
        assert!(report_codes(&report).contains(&"obligation-unproved".to_string()), "{expect}: {report}");
        assert_eq!(code, 1);
    }
    // `unknown` is no expectation: a result is proved or refuted, and what
    // the bounds leave open is reported as unproved, never as expected.
    let (code, report) = check(&example("unknown"), None);
    assert!(report_codes(&report).contains(&"example-invalid".to_string()), "{report}");
    assert_eq!(observed(&report), "absent", "{report}");
    assert_eq!(code, 1);
    // An unknown equivalence does not count as proved.
    let (_, report) = check(&with_check(&format!("[STATUS] The status is open or closed.\n{CASES}")), Some("0"));
    assert_ne!(verdict(&report, "check/SAME"), "proved");
}

const FLOW: &str = "[TEXT]\nWhen the checker finds a contradiction C,\nthe checker shall perform all of the following actions:\n    record C;\n    notify the author about C;\n[FLOW]\nWhen the checker finds a contradiction C,\nthe checker shall follow this flow:\n    step keep: record C;\n    step tell: notify the author about C;\n    start keep\n    keep -> tell\n    finish tell\n";

#[test]
fn an_undecided_relation_of_a_diagram_is_unknown() {
    // The base holds a choice, so its relation to the flow needs a search.
    let text = comparison(&format!("{FLOW}{CHOICE}"), "[TEXT], [C]", "[FLOW]", "extension");
    let (_, decided) = check(&text, None);
    assert_eq!(observed(&decided), "proved", "the example observes the extension that it expects: {decided}");
    let (code, report) = check(&text, Some("0"));
    assert_eq!(observed(&report), "unproved");
    assert_eq!(code, 1);
}

// The client is the environment: it decides when a call is sent. (Where the
// API receives the call, the trigger is the system's own, nothing requires
// it, and a system that never receives one keeps both: AGENTS.md, limit 2.)
const SCOPED: &str = "environment client\n[CALL] A call means a request that a client sends.\nsection \"Calls\":\n    When the client sends a call:\n        [LOG] The API shall log the call.\n[QUIET] When the client sends a call, the API shall not log the call.\n";

#[test]
fn a_conflict_reports_its_elements_with_their_scopes_and_terms() {
    // The statement under a shared condition is in conflict with the one
    // that writes the condition itself, and both are named.
    let (_, report) = check(SCOPED, None);
    assert_eq!(report_codes(&report), ["contradiction"]);
    let conflict = report["diagnostics"].as_array().unwrap().iter().find(|d| d["code"] == "contradiction").unwrap();
    let named: Vec<&str> = conflict["refs"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap()).collect();
    assert_eq!(named, ["LOG", "QUIET"], "{report}");
    // The written text holds no condition; the conflict names the statement as it is written.
    let log = conflict["refs"].as_array().unwrap().iter().find(|r| r["id"] == "LOG").unwrap();
    assert_eq!(log["text"], "The API shall log the call.");
    // The situation that the conflict needs is the call that the client sends.
    assert!(conflict["message"].as_str().unwrap().contains("client send"), "{conflict}");
}

#[test]
fn a_conflict_exposes_its_derivation_and_definitions() {
    // The conflict is minimal: without either statement, the rest can be
    // kept. (Alone, a statement shares no term with another one; the API and
    // the client are primitives so that it is grounded.)
    let head = "environment client\nprimitive API, client\n[CALL] A call means a request that a client sends.\n";
    let log = "section \"Calls\":\n    When the client sends a call:\n        [LOG] The API shall log the call.\n";
    let quiet = "[QUIET] When the client sends a call, the API shall not log the call.\n";
    for (id, rest) in [("LOG", quiet), ("QUIET", log)] {
        let (_, report) = check(&format!("{head}{rest}"), None);
        assert_eq!(verdict(&report, "consistency"), "proved", "without {id}: {report}");
    }
    // The contracts that the conflict is derived from are written with the
    // package: the condition of the shared block is the assumption of [LOG].
    let (_, report) = check(SCOPED, None);
    let contract = |id: &str| report["contracts"].as_array().unwrap().iter().find(|c| c["statement"]["id"] == id && c["role"] == "guarantee").unwrap_or_else(|| panic!("{id}: {report}")).clone();
    assert!(contract("LOG")["assume"].to_string().contains("Event"), "{report}");
    assert!(contract("LOG")["guarantee"].to_string().contains("Act"), "{report}");
    assert!(contract("QUIET")["guarantee"].to_string().contains("Forbid"), "{report}");
}

#[test]
fn a_statement_without_a_formal_interpretation_names_the_obligation_it_blocks() {
    // A definition is accepted and names a term; it is no formula to compare.
    let text = "[CALL] A call means a request that a client sends.\n[LOG] The API shall log the call.\ncheck SAME:\n    relation equivalent\n    left [CALL]\n    right [LOG]\n    using definitions\n";
    let (code, report) = check(text, None);
    assert_eq!(analysis_codes(&report), ["UNSUPPORTED_SEMANTICS"]);
    let diagnostic = report["diagnostics"].as_array().unwrap().iter().find(|d| d["code"] == "UNSUPPORTED_SEMANTICS").unwrap();
    assert!(diagnostic["message"].as_str().unwrap().contains("[CALL]") && diagnostic["message"].as_str().unwrap().contains("check SAME"), "{diagnostic}");
    // The check is not decided: the package does not convert, and no obligation stands for it.
    assert_eq!(verdict(&report, "check/SAME"), "absent", "an unsupported obligation is not reported as decided");
    assert_eq!(code, 1);
    let example = comparison("primitive API\n[CALL] A call means a request that a client sends.\n[LOG] The API shall log the call.\n", "[LOG]", "[CALL]", "extension");
    let (_, report) = check(&example, None);
    assert_eq!(analysis_codes(&report), ["UNSUPPORTED_SEMANTICS"]);
    let diagnostic = report["diagnostics"].as_array().unwrap().iter().find(|d| d["code"] == "UNSUPPORTED_SEMANTICS").unwrap();
    assert!(diagnostic["message"].as_str().unwrap().contains("comparison E"), "{report}");
}
