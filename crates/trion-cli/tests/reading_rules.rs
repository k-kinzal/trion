//! Reading rules that give a part of a sentence a formal structure instead
//! of an opaque atom, and how an accepted construct relates to a normative
//! statement. Each test
//! runs its reproducer as the body of `namespace p.x:` in a package `p`.

mod common;
use common::*;
use serde_json::Value;

fn package(body: &str) -> Fixture {
    let indented: String = body.lines().map(|line| if line.is_empty() { "\n".to_string() } else { format!("    {line}\n") }).collect();
    Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\nentry = \"a.trion\"\n"), ("a.trion", &format!("package p edition \"1\"\n\nnamespace p.x:\n{indented}"))])
}

fn check(body: &str) -> Value {
    package(body).verify(&["--json"]).json()
}

#[allow(dead_code)]
fn model(body: &str) -> String {
    package(body).inspect(&["model"]).stdout
}

/// The statements of each contradiction, sorted.
fn conflicts(report: &Value) -> Vec<Vec<String>> {
    report["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|d| d["code"] == "contradiction")
        .map(|d| {
            let mut ids: Vec<String> = d["refs"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap().to_string()).collect();
            ids.sort();
            ids.dedup();
            ids
        })
        .collect()
}

#[allow(dead_code)]
fn opaque(report: &Value) -> Vec<String> {
    report["opaque"].as_array().unwrap().iter().map(|d| d["message"].as_str().unwrap().to_string()).collect()
}

fn contradicts(body: &str, members: &[&str]) {
    let report = check(body);
    let found = conflicts(&report);
    assert!(found.iter().any(|ids| members.iter().all(|m| ids.iter().any(|id| id == m))), "{body}\nexpected {members:?}, found {found:?}");
}

fn errors(report: &Value, code: &str) -> Vec<String> {
    report["opaque"].as_array().unwrap().iter().chain(report["ungrounded"].as_array().unwrap()).filter(|d| d["code"] == code && d["severity"] == "error").map(|d| d["message"].as_str().unwrap().to_string()).collect()
}

/// No part of the body is unread, and no statement of it constrains nothing.
fn read(body: &str) -> Value {
    let report = check(body);
    assert!(errors(&report, "UNSUPPORTED_SEMANTICS").is_empty() && errors(&report, "ungrounded").is_empty(), "{body}\n{}", report["diagnostics"]);
    report
}

const DECISION: &str = "primitive construct\nprimitive expression\nprimitive checker\nprimitive error\nprimitive interpretation\n\n[MODEL-TEXT-DENOTATION]\nEach normative statement denotes exactly one expression.\n\n[MODEL-ACCEPTED]\nAn accepted construct means a construct that the checker reports without an error.\n\n[MODEL-ACCEPTED-NORMATIVE]\nEach accepted construct is a normative statement.\n\n[MODEL-INTERPRETATION]\nThe supported formal interpretation of a construct means the expression that the construct denotes.\n\n[MODEL-UNINTERPRETED]\nAn uninterpreted construct means a construct that has no supported formal interpretation.\n\n[MODEL-UNINTERPRETED-REJECTED]\nNo uninterpreted construct is an accepted construct.\n";

#[test]
fn each_accepted_construct_denotes_one_expression() {
    // Every statement of the decision describes and none requires: each is
    // an assumption, and assumptions that cannot all hold leave no
    // environment. The decision as the specification states it holds together.
    let report = check(DECISION);
    assert_eq!(verdicts(&report)["compatibility"], "proved", "{report}");
    // An accepted construct without an interpretation contradicts it.
    let report = check(&format!("{DECISION}\n[X1]\nSome accepted construct has no supported formal interpretation.\n"));
    assert_eq!(verdicts(&report)["compatibility"], "refuted", "{report}");
    assert!(report["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "incompatible"), "{report}");
}

#[test]
fn a_part_without_a_reading_is_an_error() {
    let fixture = package("primitive parser\nprimitive sentence\nprimitive keyword\n\n[K1]\nThe parser shall not accept a sentence because the sentence contains a keyword.\n");
    let result = fixture.verify(&["--json"]);
    assert_ne!(result.code, 0, "a sentence with an unread part must not pass");
    let found = errors(&result.json(), "UNSUPPORTED_SEMANTICS");
    assert!(found.iter().any(|m| m.contains("`because`")), "{found:?}");
    // The same rule in words that are read passes.
    let result = package("primitive parser\nprimitive sentence\nprimitive keyword\nprimitive rule\n\n[K1]\nThe parser shall reject each sentence that contains a keyword and that matches no rule.\n").verify(&["--json"]);
    assert_eq!(result.code, 0, "{}", result.stdout);
}

#[test]
fn a_statement_that_constrains_nothing_is_an_error() {
    let result = package("[G1]\nThe room shall keep the ledger.\n").verify(&["--json"]);
    assert_ne!(result.code, 0);
    assert_eq!(errors(&result.json(), "ungrounded").len(), 1);
    let result = package("primitive room\nprimitive ledger\n\n[G1]\nThe room shall keep the ledger.\n").verify(&["--json"]);
    assert_eq!(result.code, 0, "{}", result.stdout);
}

#[test]
fn a_restricted_noun_phrase_is_a_kind_of_its_head() {
    let terms = "primitive checker\nprimitive statement\nprimitive atom\n\n";
    // What is forbidden for every statement is forbidden for the restricted ones.
    contradicts(&format!("{terms}[R1]\nThe checker shall not report a statement.\n\n[R2]\nThe checker shall report each statement that shares no atom.\n"), &["R1", "R2"]);
    let report = read(&format!("{terms}[R2]\nThe checker shall report each statement that shares no atom.\n"));
    assert!(conflicts(&report).is_empty());
    // The clause is a property of each member of the class.
    let text = model(&format!("{terms}[R2]\nThe checker shall report each statement that shares no atom.\n"));
    assert!(text.contains("¬Act(x::statement that share no atom|share atom)"), "{text}");
}

#[test]
fn a_repeated_marker_continues_the_clauses_of_the_outer_head() {
    let text = model("primitive checker\nprimitive statement\nprimitive subject\nprimitive verb\n\n[R1]\nThe checker shall reject each statement that has no subject and that has no verb.\n");
    assert!(text.contains("x::statement that has no subject and that has no verb|have verb"), "{text}");
    read("primitive checker\nprimitive statement\nprimitive subject\nprimitive verb\n\n[R1]\nThe checker shall reject each statement that has no subject and that has no verb.\n");
}

#[test]
fn a_content_clause_and_a_demonstrative_are_read() {
    read("primitive checker\nprimitive trigger\n\n[C1]\nThe checker shall not assume that the trigger occurs.\n");
    read("primitive parser\nprimitive file\n\n[D1]\nWhen the parser reads a file, the parser shall close that file.\n");
}

#[test]
fn only_excludes_the_actions_with_another_focus() {
    let terms = "primitive editor\nprimitive file\nprimitive directory\n\n";
    contradicts(&format!("{terms}[O1]\nThe editor shall write only to the file.\n\n[O2]\nThe editor shall write to the directory.\n"), &["O1", "O2"]);
    let report = read(&format!("{terms}[O1]\nThe editor shall write only to the file.\n\n[O3]\nThe editor shall write to the file.\n"));
    assert!(conflicts(&report).is_empty());
    // A quoted word is a literal, not a focus.
    let report = check(&format!("{terms}[O4]\nThe editor shall write the word \"only\" to the file.\n\n[O2]\nThe editor shall write the word \"only\" to the directory.\n"));
    assert!(conflicts(&report).is_empty(), "{report}");
}

#[test]
fn a_counted_object_bounds_one_number() {
    let terms = "primitive citation\nprimitive title\n\n";
    contradicts(&format!("{terms}[C1]\nEach citation shall have exactly 1 title.\n\n[C2]\nEach citation shall have at least 2 titles.\n"), &["C1", "C2"]);
    let report = read(&format!("{terms}[C1]\nEach citation shall have exactly 1 title.\n\n[C3]\nEach citation shall have at most 3 titles.\n"));
    assert!(conflicts(&report).is_empty());
}

#[test]
fn an_action_with_an_order_role_implies_the_action() {
    let terms = "primitive compiler\nprimitive model\nprimitive publication\n\n";
    contradicts(&format!("{terms}[B1]\nThe compiler shall check the model before publication.\n\n[B2]\nThe compiler shall not check the model.\n"), &["B1", "B2"]);
    read(&format!("{terms}[B1]\nThe compiler shall check the model before publication.\n"));
}

#[test]
fn a_determiner_and_a_modifier_of_an_inner_noun_are_read() {
    read("primitive loader\nprimitive package\nprimitive file\n\n[D1]\nThe loader shall load each package that names every file.\n");
    read("primitive parser\nprimitive annotation\nprimitive statement\n\nA later statement means a statement that follows a statement.\n\n[D2]\nThe parser shall not attach an annotation to a later statement.\n");
}

#[test]
fn a_comparison_takes_a_measure_with_an_of_phrase() {
    let text = model("[Q1]\nThe duration of an action is at most the elapsed time of the action.\n");
    assert!(text.contains("x::action duration − x::action elapsed time ≤ 0"), "{text}");
}

#[test]
fn the_specification_of_trion_has_no_unread_part() {
    let result = verify_in(&repo_root(), &["--json", "."]);
    let report = result.json();
    assert!(report["opaque"].as_array().unwrap().is_empty(), "{}", report["opaque"]);
    assert!(report["ungrounded"].as_array().unwrap().is_empty(), "{}", report["ungrounded"]);
}
