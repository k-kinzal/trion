//! What a verification result states: its status, its method and bounds, the
//! elements of a conflict and the results that the bounds leave unknown.

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
    let mut args = vec!["verify", "--json"];
    if let Some(limit) = limit {
        args.extend(["--decision-limit", limit]);
    }
    let result = f.trion(&args);
    (result.code, result.json())
}

fn text_report(text: &str, args: &[&str]) -> (i32, String) {
    let result = fixture(text).trion(args);
    (result.code, result.stdout)
}

#[test]
fn a_consistency_result_has_one_of_three_statuses() {
    let status = |text: &str, limit: Option<&str>| check(text, limit).1["consistency"]["status"].as_str().unwrap().to_string();
    assert_eq!(status("[A] The API shall return foo.\n", None), "satisfiable");
    assert_eq!(status(CONFLICT, None), "unsatisfiable");
    assert_eq!(status(CHOICE, Some("0")), "unknown");
    // The same input is decided once the bound leaves room for the search.
    assert_eq!(status(CHOICE, Some("100")), "satisfiable");
}

#[test]
fn the_checker_publishes_the_verdict_of_the_status() {
    let verdict = |text: &str, limit: Option<&str>| {
        let report = check(text, limit).1;
        (report["consistency"]["status"].as_str().unwrap().to_string(), report["consistency"]["verdict"].as_str().unwrap().to_string())
    };
    assert_eq!(verdict("[A] The API shall return foo.\n", None), ("satisfiable".to_string(), "consistent".to_string()));
    assert_eq!(verdict(CONFLICT, None), ("unsatisfiable".to_string(), "inconsistent".to_string()));
    assert_eq!(verdict(CHOICE, Some("0")), ("unknown".to_string(), "unknown".to_string()));
    let (_, printed) = text_report(CONFLICT, &["verify"]);
    assert!(printed.contains("consistency: inconsistent"), "{printed}");
}

#[test]
fn a_search_that_the_bounds_end_is_unknown_and_no_success() {
    let (code, report) = check(CHOICE, Some("0"));
    assert_eq!(report["consistency"]["status"], "unknown");
    assert_eq!(report["consistency"]["exhaustive"], false);
    assert_eq!(report_codes(&report), ["consistency-unknown"]);
    assert_eq!(code, 1, "an unknown result must not pass");
    let (code, printed) = text_report(CHOICE, &["verify", "--decision-limit", "0"]);
    assert_eq!(code, 1, "{printed}");
    assert!(printed.contains("consistency: unknown") && printed.contains("gate check: failed"), "{printed}");
    assert_eq!(check(CHOICE, None).0, 0);
}

#[test]
fn a_result_names_its_revision_assumptions_profile_method_and_bounds() {
    let (_, report) = check("[A] The status is open or closed.\n[B] While the status is open, the API shall stop.\n", Some("50"));
    let result = &report["consistency"];
    let revision = result["subject_revision"].as_str().unwrap();
    assert!(revision.len() >= 12 && revision.chars().all(|c| c.is_ascii_hexdigit()), "{revision}");
    assert!(result["assumptions"].as_array().unwrap().iter().any(|a| a.as_str().unwrap().contains("at most one of its values")), "{result}");
    assert!(result["profile"].as_str().unwrap().contains("bounded traces"), "{result}");
    assert_eq!(result["bounds"]["trace_length"], 3);
    assert!(result["method"].as_str().unwrap().contains("DPLL"), "{result}");
    assert_eq!(result["bounds"]["decisions"], 50);
    // A changed specification is another subject.
    let (_, other) = check("[A] The API shall stop.\n", None);
    assert_ne!(other["consistency"]["subject_revision"], result["subject_revision"]);
    assert_eq!(other["consistency"]["bounds"]["decisions"], Value::Null);
    let (_, printed) = text_report("[A] The API shall stop.\n", &["verify", "--decision-limit", "7"]);
    for part in ["revision ", "bounds: 7 decisions", "method: ", "profile: ", "assumptions: "] {
        assert!(printed.contains(part), "{part}: {printed}");
    }
}

#[test]
fn a_bounded_result_states_its_bounds_and_claims_no_more_than_its_search() {
    // The bound ends the search: the result states the bound and decides nothing.
    let (_, cut) = check(CHOICE, Some("0"));
    assert_eq!(cut["consistency"]["bounds"]["decisions"], 0);
    assert_eq!(cut["consistency"]["status"], "unknown");
    assert_eq!(cut["consistency"]["exhaustive"], false);
    // The search ends inside the bound: the exhausted search is the proof of the result.
    let (_, whole) = check(CHOICE, Some("100"));
    assert_eq!(whole["consistency"]["bounds"]["decisions"], 100);
    assert_eq!(whole["consistency"]["exhaustive"], true);
    assert!(whole["consistency"]["peak_decisions"].as_u64().unwrap() <= 100);
    // A conflict that the bound hides is not reported as consistency.
    let hidden = format!("{CHOICE}[D] The API shall not accept the call.\n[E] The API shall not reject the call.\n");
    assert_eq!(check(&hidden, None).1["consistency"]["status"], "unsatisfiable");
    assert_ne!(check(&hidden, Some("0")).1["consistency"]["status"], "satisfiable");
}

#[test]
fn a_broken_recommendation_is_not_an_inconsistency() {
    let (code, soft) = check("[A] The API should return foo.\n[B] The API shall not return foo.\n", None);
    assert_eq!(report_codes(&soft), ["recommendation-violation"]);
    assert_eq!(soft["consistency"]["status"], "satisfiable");
    assert_eq!(code, 1);
    let (_, hard) = check(CONFLICT, None);
    assert_eq!(report_codes(&hard), ["contradiction"]);
    assert_eq!(hard["consistency"]["status"], "unsatisfiable");
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
    // No value outside the closed domain can occur, so [B] holds emptily.
    let (_, report) = check("[D] The status is open or closed.\n[A] While the status is open, the API shall stop.\n[B] While the status is closed, the API shall stop.\n[V] While the status is pending, the API shall log the call.\n", None);
    let vacuous = report["coverage"]["vacuous"].as_array().unwrap();
    assert_eq!(vacuous.len(), 1, "{report}");
    assert_eq!(vacuous[0]["reference"]["id"], "V");
    assert!(vacuous[0]["condition"].as_str().unwrap().contains("pending"), "{report}");
    assert_eq!(vacuous[0]["reason"], "excluded by `D`", "{report}");
    // A statement that requires nothing in any situation is an error of its own, and no contradiction.
    assert_eq!(report_codes(&report), ["condition-unreachable"], "{report}");
    assert_eq!(report["consistency"]["verdict"], "consistent");
    // A reachable condition is not listed.
    let (_, clean) = check("[A] While the status is open, the API shall stop.\n", None);
    assert_eq!(clean["coverage"]["vacuous"].as_array().unwrap().len(), 0);
    let (_, printed) = text_report("[D] The status is open or closed.\n[A] While the status is open, the API shall stop.\n[B] While the status is closed, the API shall stop.\n[V] While the status is pending, the API shall log the call.\n", &["verify"]);
    assert!(printed.contains("coverage: [V] holds only because its condition is excluded by `D`"), "{printed}");
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
    assert_eq!(defined["checks"][0]["result"], "proved");
    let (_, open) = check(&with_check(CASES), None);
    assert_eq!(analysis_codes(&open), ["check-refuted"]);
    assert_eq!(open["checks"][0]["result"], "refuted");
}

#[test]
fn a_check_that_the_bounds_leave_open_is_unknown() {
    let text = with_check(&format!("[STATUS] The status is open or closed.\n{CASES}"));
    let (code, report) = check(&text, Some("0"));
    assert_eq!(report["checks"][0]["result"], "unknown");
    assert!(report_codes(&report).contains(&"check-unknown".to_string()), "{report}");
    assert!(!report_codes(&report).contains(&"check-refuted".to_string()), "{report}");
    assert_eq!(code, 1);
    let (_, printed) = text_report(&text, &["verify", "--decision-limit", "0"]);
    assert!(printed.contains("0/1 checks proved"), "{printed}");
}

fn comparison(text: &str, base: &str, candidate: &str, expect: &str) -> String {
    format!("{text}example E:\n    kind comparison\n    base {base}\n    candidate {candidate}\n    using definitions\n    expect {expect}\n")
}

fn observed(report: &Value) -> String {
    match report["examples"].get(0) {
        Some(example) => example["observed"].as_str().unwrap().to_string(),
        None => format!("{report}"),
    }
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
    assert_eq!(observed(&report), "unknown");
}

#[test]
fn a_comparison_with_an_undecided_base_is_unknown() {
    let text = comparison(&format!("{CHOICE}[N] The API shall log the call.\n"), "[C]", "[N]", "extension");
    assert!(report_codes(&check(&text, None).1).is_empty());
    let (_, report) = check(&text, Some("0"));
    assert_eq!(observed(&report), "unknown");
}

#[test]
fn a_comparison_without_the_needed_evidence_is_unknown() {
    // The base is decided by propagation alone; the candidate needs a search.
    let text = comparison(&format!("[N] The API shall log the call.\n{CHOICE}"), "[N]", "[C]", "extension");
    assert!(report_codes(&check(&text, None).1).is_empty());
    let (_, report) = check(&text, Some("0"));
    assert_eq!(observed(&report), "unknown");
    assert!(report_codes(&report).contains(&"example-failed".to_string()), "{report}");
}

#[test]
fn an_unknown_result_satisfies_no_expectation() {
    let example = |expect: &str| format!("example E:\n    kind consistency\n    input \"The API shall either accept the call or reject the call.\"\n    expect {expect}\n");
    assert!(report_codes(&check(&example("consistent"), None).1).is_empty());
    for expect in ["consistent", "inconsistent", "unknown"] {
        let (code, report) = check(&example(expect), Some("0"));
        assert_eq!(observed(&report), "unknown", "{report}");
        assert!(report_codes(&report).contains(&"example-failed".to_string()), "{expect}: {report}");
        assert_eq!(code, 1);
    }
    // An unknown equivalence does not count as proved.
    let (_, report) = check(&with_check(&format!("[STATUS] The status is open or closed.\n{CASES}")), Some("0"));
    assert_ne!(report["checks"][0]["result"], "proved");
}

const FLOW: &str = "[TEXT]\nWhen the checker finds a contradiction C,\nthe checker shall perform all of the following actions:\n    record C;\n    notify the author about C;\n[FLOW]\nWhen the checker finds a contradiction C,\nthe checker shall follow this flow:\n    step keep: record C;\n    step tell: notify the author about C;\n    start keep\n    keep -> tell\n    finish tell\n";

#[test]
fn an_undecided_relation_of_a_diagram_is_unknown() {
    // The base holds a choice, so its relation to the flow needs a search.
    let text = comparison(&format!("{FLOW}{CHOICE}"), "[TEXT], [C]", "[FLOW]", "extension");
    let (_, decided) = check(&text, None);
    assert_eq!(observed(&decided), "extension");
    let (code, report) = check(&text, Some("0"));
    assert_eq!(observed(&report), "unknown");
    assert_eq!(code, 1);
}

const SCOPED: &str = "[CALL] A call means a request that a client sends.\nsection \"Calls\":\n    When the API receives a call:\n        [LOG] The API shall log the call.\n[QUIET] When the API receives a call, the API shall not log the call.\n";

#[test]
fn a_conflict_reports_its_elements_with_their_scopes_and_terms() {
    let (_, report) = check(SCOPED, None);
    assert_eq!(report_codes(&report), ["contradiction"]);
    let conflict = &report["conflicts"][0];
    let element = |id: &str| conflict["elements"].as_array().unwrap().iter().find(|e| e["reference"]["id"] == id).unwrap_or_else(|| panic!("{id}: {conflict}")).clone();
    let log = element("LOG");
    // The written text holds no condition; the scopes and the expansion do.
    assert_eq!(log["reference"]["text"], "The API shall log the call.");
    let scopes: Vec<&str> = log["scopes"].as_array().unwrap().iter().map(|s| s.as_str().unwrap()).collect();
    assert_eq!(scopes, ["section \"Calls\"", "When the API receives a call"]);
    assert_eq!(log["expansion"], "When the API receives a call, the API shall log the call.");
    let terms: Vec<&str> = log["terms"].as_array().unwrap().iter().map(|s| s.as_str().unwrap()).collect();
    assert!(terms.iter().any(|t| t.starts_with("API (")) && terms.iter().any(|t| t.starts_with("call (")), "{terms:?}");
    // A statement that writes its own condition inherits none.
    assert_eq!(element("QUIET")["scopes"].as_array().unwrap().len(), 0);
    let (_, printed) = text_report(SCOPED, &["verify"]);
    assert!(printed.contains("scopes: section \"Calls\"; When the API receives a call"), "{printed}");
    assert!(printed.contains("terms: "), "{printed}");
}

#[test]
fn a_conflict_exposes_its_derivation_and_definitions() {
    let (_, report) = check(SCOPED, None);
    let conflict = &report["conflicts"][0];
    assert_eq!(conflict["minimal"], true);
    let steps = conflict["derivation"].as_array().unwrap();
    let step = |origin: &str| steps.iter().find(|s| s["origin"] == origin).unwrap_or_else(|| panic!("{origin}: {conflict}")).clone();
    assert!(step("LOG")["assume"].as_str().unwrap().contains("Event("), "{conflict}");
    assert!(step("LOG")["guarantee"].as_str().unwrap().contains("Act("), "{conflict}");
    assert!(step("QUIET")["guarantee"].as_str().unwrap().contains("Forbid("), "{conflict}");
    // The definition of a term that the elements use is listed with the conflict.
    let definitions: Vec<&str> = conflict["definitions"].as_array().unwrap().iter().map(|d| d["id"].as_str().unwrap()).collect();
    assert_eq!(definitions, ["CALL"]);
    let (_, printed) = text_report(SCOPED, &["verify"]);
    assert!(printed.contains("conflict [contradiction] (minimal):"), "{printed}");
    assert!(printed.contains("derivation LOG: ") && printed.contains("definition [CALL] "), "{printed}");
}

#[test]
fn a_statement_without_a_formal_interpretation_names_the_obligation_it_blocks() {
    // A definition is accepted and names a term; it is no formula to compare.
    let text = "[CALL] A call means a request that a client sends.\n[LOG] The API shall log the call.\ncheck SAME:\n    relation equivalent\n    left [CALL]\n    right [LOG]\n    using definitions\n";
    let (code, report) = check(text, None);
    assert_eq!(analysis_codes(&report), ["UNSUPPORTED_SEMANTICS"]);
    let diagnostic = &report["diagnostics"][0];
    assert!(diagnostic["message"].as_str().unwrap().contains("[CALL]") && diagnostic["message"].as_str().unwrap().contains("check SAME"), "{diagnostic}");
    // The check stays among the outcomes as one that has no supported reading: it is not decided, and it is not gone.
    assert_eq!(report["checks"].as_array().unwrap().iter().map(|c| c["result"].as_str().unwrap()).collect::<Vec<_>>(), ["unsupported"], "an unsupported obligation is not reported as decided");
    assert!(report["claims"].as_array().unwrap().iter().any(|c| c["claim"] == "property_entails" && c["subject"] == "check SAME" && c["verdict"] == "unsupported"), "{report}");
    assert_eq!(code, 1);
    let example = comparison("[CALL] A call means a request that a client sends.\n[LOG] The API shall log the call.\n", "[LOG]", "[CALL]", "extension");
    let (_, report) = check(&example, None);
    assert_eq!(analysis_codes(&report), ["UNSUPPORTED_SEMANTICS"]);
    assert!(report["diagnostics"][0]["message"].as_str().unwrap().contains("comparison E"), "{report}");
}
