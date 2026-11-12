//! Sentences that were read as something else than they say. Each is now
//! read as it is written or rejected.

mod common;
use common::*;

const HEAD: &str = "primitive parser\nprimitive source file\nprimitive checker\nprimitive diagnostic\nprimitive room\nprimitive user\nprimitive report\nprimitive timeout\nprimitive limit\n\n";

fn check(text: &str) -> serde_json::Value {
    Fixture::new(&[("a.trion", &format!("{HEAD}{text}"))]).trion(&["verify", "--json", "a.trion"]).json()
}

fn model(text: &str) -> String {
    Fixture::new(&[("a.trion", &format!("{HEAD}{text}"))]).inspect(&["model", "a.trion"]).stdout
}

fn unread(text: &str) -> Vec<String> {
    check(text)["opaque"].as_array().unwrap().iter().map(|d| d["message"].as_str().unwrap().to_string()).collect()
}

#[test]
fn a_comma_and_a_whole_statement_join_two_statements() {
    let view = model("[A]\nThe parser reads the source file, and the checker reports the diagnostic.\n");
    assert!(view.contains("Act(parser|read source file)") && view.contains("Act(checker|report diagnostic)"), "{view}");
    // The second statement is no object of the first.
    assert!(!view.contains("read checker"), "{view}");
    // A verb after `and` continues the first statement.
    let continued = model("[B]\nThe parser reads the source file, and reports the diagnostic.\n");
    assert!(continued.contains("Act(parser|report diagnostic)"), "{continued}");
}

#[test]
fn a_repeated_copula_states_two_predicates_of_one_subject() {
    let view = model("[A]\nThe room is archived and is locked.\n");
    assert!(view.contains("Dom(room, archived)") && view.contains("Dom(room, locked)"), "{view}");
    let report = check("[A]\nThe room is archived and is locked.\n[B]\nThe room is not locked.\n");
    assert!(report["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "contradiction"), "{report}");
}

#[test]
fn a_permission_of_a_composed_response_is_one_permission() {
    let list = "[P]\nThe user may perform all of the following actions:\n    create a report;\n    send the report;\n";
    let view = model(list);
    // One permission of the whole; no item is permitted alone.
    assert!(view.contains("¬Forbid(user|all of (create report) (send report))"), "{view}");
    assert!(!view.contains("¬Forbid(user|create report)"), "{view}");
    // What forbids an item forbids the whole.
    let report = check(&format!("{list}\n[Q]\nThe user shall not send the report.\n"));
    assert!(report["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "contradiction"), "{report}");
    // A choice is forbidden only when each alternative is.
    let choice = "[P]\nThe user may perform exactly one of the following actions:\n    create a report;\n    send the report;\n";
    let free = check(&format!("{choice}\n[Q]\nThe user shall not send the report.\n"));
    assert!(!free["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "contradiction"), "{free}");
}

#[test]
fn a_comparison_that_is_no_bound_is_rejected() {
    let messages = unread("[V]\nThe timeout is less than the limit and the report.\n");
    assert!(messages.iter().any(|m| m.contains("`less than` is a comparison")), "{messages:?}");
}

#[test]
fn a_relative_clause_without_a_reading_is_rejected() {
    // Two actors on one member: the clause names no one action on the room.
    let messages = unread("[A]\nThe checker shall report each room that the parser and the user read.\n");
    assert!(messages.iter().any(|m| m.contains("is a clause")), "{messages:?}");
    assert!(unread("[A]\nThe checker shall report each room that the parser reads.\n").is_empty());
}

#[test]
fn a_content_clause_is_read_by_the_class_of_its_verb() {
    // An establishing verb makes its clause hold when its action completes.
    let unrolled = |text: &str| Fixture::new(&[("a.trion", &format!("{HEAD}{text}"))]).inspect(&["model", "--unrolled", "a.trion"]).stdout;
    let made = unrolled("[A]\nThe checker shall verify that the room is locked.\n");
    assert!(made.contains("(Act(checker|verify that room is locked@0) → Val(room@0, locked))"), "{made}");
    // A reporting verb says nothing of whether the clause holds.
    let told = unrolled("[A]\nThe checker shall report that the room is locked.\n");
    assert!(told.contains("Act(checker|report that room is locked@0)") && !told.contains("(Act(checker|report that room is locked@0) → Val(room@0, locked))"), "{told}");
    assert!(unread("[A]\nThe checker shall report that the room is locked.\n[B]\nWhen the checker reports that the room is locked, the user shall read the report.\n").is_empty());
    // Two reports about two clauses are two actions.
    let apart = check("[A]\nThe checker shall report that the room is locked.\n[B]\nThe checker shall not report that the room is archived.\n");
    assert!(!apart["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "contradiction"), "{apart}");
    let same = check("[A]\nThe checker shall report that the room is locked.\n[B]\nThe checker shall not report that the room is locked.\n");
    assert!(same["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "contradiction"), "{same}");
    // Any other verb takes no content clause.
    let messages = unread("[A]\nThe checker shall keep that the room is locked.\n");
    assert!(messages.iter().any(|m| m.contains("after a verb that takes no content clause")), "{messages:?}");
}
