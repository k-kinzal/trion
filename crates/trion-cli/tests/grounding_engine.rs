//! What grounding a specification needs from the engine: names that survive
//! their aliases, relations between terms that stay cheap, and reports that
//! name only what was not read.

mod common;
use common::*;
use serde_json::Value;

fn check(text: &str) -> Value {
    Fixture::new(&[("a.trion", text)]).verify(&["--json", "a.trion"]).json()
}

fn codes(text: &str) -> Vec<String> {
    report_codes(&check(text))
}

/// As `codes`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn codes_of_the_analysis(text: &str) -> Vec<String> {
    analysis_codes(&check(text))
}

fn model(text: &str) -> String {
    Fixture::new(&[("a.trion", text)]).inspect(&["model", "a.trion"]).stdout
}

/// The messages of one silent list of a check report.
fn silent(report: &Value, list: &str) -> Vec<String> {
    report[list].as_array().unwrap().iter().map(|d| d["message"].as_str().unwrap().to_string()).collect()
}

#[test]
fn an_alias_is_not_read_inside_the_name_that_it_stands_for() {
    let text = "alias statement = normative statement\n[D] A normative statement means a sentence with a modal verb.\n[A] Each statement shall end with a period.\n[B] Each normative statement shall not end with a period.\n";
    // Both spellings are one term, and the definition defines it.
    let model = model(text);
    assert!(model.contains("normative statement|end with period"), "{model}");
    assert!(!model.contains("normative normative"), "{model}");
    assert_eq!(codes(text), ["contradiction"]);
    let glossary = Fixture::new(&[("a.trion", text)]).inspect(&["glossary", "a.trion"]).stdout;
    assert!(glossary.contains("normative statement\texplicit"), "{glossary}");
}

#[test]
fn a_definition_that_an_alias_collapses_is_reported() {
    let report = check("alias statement = normative statement\n[D] A statement means a normative statement.\n");
    assert!(report_codes(&report).contains(&"definition-collapsed".to_string()), "{report}");
    // A definition by another term is no collapse.
    assert!(!codes("[D] A guest means a user.\n[A] The guest shall log in.\n").contains(&"definition-collapsed".to_string()));
}

/// Many rules about one term, as a specification of a language has them.
/// The events and the marks are primitives: a statement that shares no
/// term with another one is ungrounded, and that is not what is tested.
fn rules(count: usize) -> String {
    (0..count).map(|i| format!("primitive event{i}, mark{i}\n[R{i}] When the event{i} occurs, each statement shall keep the mark{i}.\n")).collect()
}

#[test]
fn inclusions_in_a_term_that_every_rule_names_are_decided() {
    let kinds = ["definition", "rule", "obligation", "prohibition", "recommendation", "permission", "description"];
    let inclusions: String = kinds.iter().map(|kind| format!("Each {kind} is a statement.\n")).collect();
    let text = format!("{inclusions}{}[X] When the event3 occurs, each rule shall not keep the mark3.\n", rules(120));
    let report = check(&text);
    // The prohibition of a rule meets the obligation of every statement.
    assert_eq!(analysis_codes(&report), ["contradiction"], "{report}");
    // The conflict needs the event to occur, and the environment decides
    // that it does: the situation that the counterexample names is the event.
    assert_eq!(verdicts(&report).get("consistency").map(String::as_str), Some("refuted"), "{report}");
    let found = report["diagnostics"].as_array().unwrap().iter().find(|d| d["code"] == "contradiction").unwrap();
    assert!(found["message"].as_str().unwrap().contains("event3"), "{report}");
    let consistent = check(&format!("{inclusions}{}", rules(120)));
    assert!(analysis_codes(&consistent).is_empty(), "{consistent}");
    assert_eq!(verdicts(&consistent).get("consistency").map(String::as_str), Some("proved"), "{consistent}");
}

#[test]
fn a_statement_with_many_details_is_decided() {
    let details: Vec<String> = (0..120).map(|i| format!("[R{i}]")).collect();
    // The statement is refined by its details: each detail requires what it requires where it applies.
    let abstract_rule = format!("[TOP] When the event0 occurs, each statement shall keep the mark0.\n    detailed by {}\n", details.join(", "));
    let text = format!("{abstract_rule}{}", rules(120));
    let report = check(&text);
    assert!(report_codes(&report).is_empty(), "{report}");
    assert_eq!(verdicts(&report).get("consistency").map(String::as_str), Some("proved"), "{report}");
    // A conflict with one detail is found, and the details still refine the statement.
    let broken = check(&format!("{text}[X] When the event7 occurs, each statement shall not keep the mark7.\n"));
    assert_eq!(report_codes(&broken), ["contradiction"], "{broken}");
    assert_eq!(verdicts(&broken).get("refinement/TOP").map(String::as_str), Some("proved"), "{broken}");
    // An abstract statement that its details do not imply is reported.
    let unrefined = format!("[TOP] The language shall keep each statement.\n    detailed by {}\n{}", details.join(", "), rules(120));
    // A document that keeps both exists, so a requirement of it is missing from its details.
    assert_eq!(report_codes(&check(&unrefined)), ["detail-not-refining", "detail-incomplete"]);
}

#[test]
fn an_exclusion_agrees_with_an_enumeration_of_the_same_values() {
    let listed = "[SEV] The severity of a diagnostic is error, warning, or information.\n[X] No error is a warning.\n";
    assert!(codes(listed).is_empty(), "{:?}", codes(listed));
    // One thing still cannot be both. The statements describe the language,
    // which no statement gives to the system: they are assumptions, and
    // together they allow no environment.
    let both = "[N1] The notation of the language is a controlled natural language.\n[N2] The notation of the language is English.\n[X] No controlled natural language is English.\n";
    assert_eq!(codes(both), ["incompatible"]);
}

const VOCABULARY: &str = "A statement means a sentence of a specification.\nprimitive sentence\nprimitive specification\nprimitive comment\n";

#[test]
fn a_modified_phrase_is_a_kind_of_its_head() {
    // A rule about each statement reaches each cited statement.
    let text = format!("{VOCABULARY}[A] Each statement shall not hold a comment.\n[B] Each cited statement shall hold a comment.\n");
    assert_eq!(codes(&text), ["contradiction"]);
    // The phrase is grounded through its head.
    let report = check(&format!("{VOCABULARY}primitive parser\n[C] The parser shall keep the cited statement.\n"));
    assert!(silent(&report, "ungrounded").is_empty(), "{report}");
    // Without a meaning for the head, nothing grounds the phrase.
    let loose = check("primitive parser\n[C] The parser shall keep the cited statement.\n");
    assert!(silent(&loose, "ungrounded")[0].contains("cited statement"), "{loose}");
}

#[test]
fn a_modifier_that_denies_its_head_makes_no_kind() {
    let text = format!("{VOCABULARY}[A] Each statement shall not hold a comment.\n[B] Each former statement shall hold a comment.\n");
    let report = check(&text);
    assert!(analysis_codes(&report).is_empty(), "{report}");
    assert!(silent(&report, "ungrounded").iter().any(|m| m.contains("former statement")), "{report}");
}

#[test]
fn only_an_unread_part_is_an_opaque_reading() {
    // `that list` points at a list; a quoted word is a literal.
    let read = check("[A] The parser shall keep that list.\n[B] The parser shall reject a line with \"each\".\n[C] The parser shall begin with \"choose after\".\n");
    assert!(silent(&read, "opaque").is_empty(), "{read}");
    // A clause and a quantifier without a reading are reported, once for one statement.
    let unread = check("[A] The reader shall show the item because the user waits.\n[B] The parser shall accept some reference.\n");
    let messages = silent(&unread, "opaque");
    assert_eq!(messages.len(), 2, "{messages:?}");
    assert!(messages.iter().any(|m| m.contains("`because` is a conjunction")), "{messages:?}");
    assert!(messages.iter().any(|m| m.contains("`some` is a quantifier")), "{messages:?}");
}

#[test]
fn a_term_defined_in_an_unused_namespace_is_pointed_out() {
    let manifest = "[package]\nname = \"p\"\nentry = \"p.trion\"\n";
    let entry = "package p\n\nnamespace p.words\n\nprimitive message\nA response means a message.\n\nnamespace p.rules\n\nprimitive parser\n[A] The parser shall keep the response.\n";
    let f = Fixture::raw(&[("trion.toml", manifest), ("p.trion", entry)]);
    let report = f.verify(&["--json"]).json();
    let messages = silent(&report, "ungrounded");
    assert!(messages.iter().any(|m| m.contains("`response` is defined in the namespace `words`") && m.contains("`use p.words`")), "{messages:?}");
    // With the namespace used, the statement is grounded.
    let used = entry.replace("namespace p.rules\n", "namespace p.rules\n\nuse p.words\n");
    let f = Fixture::raw(&[("trion.toml", manifest), ("p.trion", &used)]);
    assert!(silent(&f.verify(&["--json"]).json(), "ungrounded").is_empty());
}
