//! The account of a reading: every word of a sentence is read by a reading
//! rule or the statement is rejected. Each test runs its reproducer as the
//! body of `namespace p.x:` in a package `p`.

mod common;
use common::*;
use serde_json::Value;

const TERMS: &str = "primitive checker\nprimitive statement\nprimitive parser\nprimitive item\nprimitive result\nprimitive room\nprimitive token\nprimitive report\nprimitive user\n\n";

fn package(body: &str) -> Fixture {
    let indented: String = format!("{TERMS}{body}").lines().map(|line| if line.is_empty() { "\n".to_string() } else { format!("    {line}\n") }).collect();
    Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\nentry = \"a.trion\"\n"), ("a.trion", &format!("package p edition \"1\"\n\nnamespace p.x:\n{indented}"))])
}

fn check(body: &str) -> (i32, Value) {
    let result = package(body).trion(&["verify", "--json"]);
    (result.code, result.json())
}

fn unread(report: &Value) -> Vec<String> {
    report["opaque"].as_array().unwrap().iter().filter(|d| d["code"] == "UNSUPPORTED_SEMANTICS" && d["severity"] == "error").map(|d| d["message"].as_str().unwrap().to_string()).collect()
}

fn conflicts(report: &Value) -> usize {
    report["diagnostics"].as_array().unwrap().iter().filter(|d| d["code"] == "contradiction").count()
}

/// The statement is rejected, and the error names the word.
fn rejected(body: &str, word: &str) -> String {
    let (code, report) = check(body);
    let found = unread(&report);
    assert_ne!(code, 0, "{body}");
    let Some(message) = found.iter().find(|m| m.starts_with(&format!("`{word}` "))) else { panic!("{body}\nno error names `{word}`: {found:?}") };
    message.clone()
}

/// Every part of the body is read.
fn read(body: &str) -> Value {
    let (_, report) = check(body);
    assert!(unread(&report).is_empty(), "{body}\n{:?}", unread(&report));
    assert!(report["ungrounded"].as_array().unwrap().is_empty(), "{body}\n{}", report["ungrounded"]);
    report
}

#[test]
fn a_function_word_that_the_parser_took_for_a_content_word_is_rejected() {
    // None of these words was in the lists that the checker sought in the
    // names of atoms: each one stands where a content word is expected.
    for (body, word) in [
        ("[A] The checker shall keep several statements.\n[B] The checker shall not keep a statement.\n", "several"),
        ("[A] The checker shall report the statement itself.\n[B] The checker shall not report the statement.\n", "itself"),
        ("[A] The parser shall read the item instead.\n[B] The parser shall not read the item.\n", "instead"),
        ("[A] The parser shall keep the item together.\n[B] The parser shall not keep the item.\n", "together"),
        ("[A] The room is consistent in an item.\n[B] The room is not consistent.\n", "in"),
        ("[A] The checker shall report a statement rather than an item.\n[B] The checker shall not report a statement.\n", "rather"),
        ("[A] The parser shall read the result merely.\n[B] The parser shall not read the result.\n", "merely"),
    ] {
        let message = rejected(body, word);
        assert!(message.contains("no reading rule reads it there"), "{message}");
    }
}

#[test]
fn a_definition_and_a_verb_place_are_checked_too() {
    // A definition has no contract; its words are the names of its axiom.
    rejected("A kept item means an item that the parser keeps in another room.\n\n[A] The parser shall read each kept item.\n[B] While the user is present, the parser shall not read a kept item.\n", "another");
    // `that the parser keeps together`: the parser took `together` for the verb.
    let message = rejected("A kept item means an item that the parser keeps together.\n\n[A] The parser shall read each kept item.\n[B] While the user is present, the parser shall not read a kept item.\n", "together");
    assert!(message.contains("as a verb"), "{message}");
    read("A kept item means an item that the parser keeps.\n\n[A] The parser shall read each kept item.\n[B] When the parser reads a kept item, the parser shall report the result.\n");
}

#[test]
fn the_error_names_the_part_and_a_form_that_is_read() {
    let message = rejected("[A] The room is consistent in an item.\n[B] The room is not consistent.\n", "in");
    assert!(message.contains("is a preposition inside a predicate (`consistent in an item`)"), "{message}");
    assert!(message.contains("write the phrase as a role after the verb, or define the whole phrase as a term"), "{message}");
    let message = rejected("[A] The checker shall keep several statements.\n[B] The checker shall not keep a statement.\n", "several");
    assert!(message.contains("`at most 3 requests`"), "{message}");
}

#[test]
fn a_word_of_a_declared_term_is_part_of_a_name() {
    // `otherwise` is an adverb; inside a defined term it is a name.
    rejected("[A] The parser shall keep the otherwise item.\n[B] The parser shall not keep an item.\n", "otherwise");
    read("An otherwise item means an item that the parser keeps.\n\n[A] The parser shall keep the otherwise item.\n[B] When the parser keeps the otherwise item, the parser shall read the result.\n");
}

#[test]
fn an_action_on_a_kind_of_a_noun_is_an_action_on_the_noun() {
    // The first statement is a statement: a ban on every statement bans it.
    // A word of order is read inside a term that a definition declares.
    let first = "A first statement means a statement of a sequence that no statement of that sequence precedes.\n";
    let report = read(&format!("{first}[A] The checker shall report the first statement.\n[B] The checker shall not report a statement.\n"));
    assert_eq!(conflicts(&report), 1, "{report}");
    let later = "A later statement means a statement that follows a statement.\n";
    let report = read(&format!("{later}[A] The checker shall report a later statement.\n[B] The checker shall not report a statement.\n"));
    assert_eq!(conflicts(&report), 1, "{report}");
    // Outside a declared term the order is not read, so the statement is rejected.
    rejected("[A] The checker shall report the first statement.\n[B] The checker shall not report a statement.\n", "first");
    // A word that tells two things apart is no name of a kind.
    for word in ["another", "different", "other"] {
        let article = if word == "another" { "" } else { "a " };
        rejected(&format!("[A] The checker shall report {article}{word} statement.\n[B] The checker shall not report a statement.\n"), word);
    }
}

#[test]
fn an_action_that_makes_a_proposition_hold_implies_it() {
    // `ensure that the token is valid` makes the token valid.
    let report = read("[A] The checker shall ensure that the token is valid.\n[B] The token shall not be valid.\n");
    assert_eq!(conflicts(&report), 1, "{report}");
    let report = read("[A] The checker shall guarantee that the token is valid.\n[B] The token shall not be valid.\n");
    assert_eq!(conflicts(&report), 1, "{report}");
    // A proposition that an action is about is not asserted by that action.
    let report = read("[A] The checker shall report that the token is valid.\n[B] The token shall not be valid.\n[C] When the checker reports that the token is valid, the user shall read the report.\n");
    assert_eq!(conflicts(&report), 0, "{report}");
}

#[test]
fn between_after_a_noun_names_the_owners_of_the_noun() {
    let model = package("[A] The checker shall report each relation between a statement and an item.\n[B] The checker shall not report a relation of a statement and of an item.\n").inspect(&["model"]).stdout;
    assert!(!model.contains("between"), "{model}");
    let report = read("[A] The checker shall report each relation between a statement and an item.\n[B] The checker shall not report a relation of a statement and of an item.\n");
    assert_eq!(conflicts(&report), 1, "{report}");
}

#[test]
fn a_nominal_predicate_is_named_as_its_noun_phrases_are() {
    let model = package("[A] Each report is a result of the checker.\n[B] Each item is a statement or a token.\n").inspect(&["model"]).stdout;
    assert!(model.contains("Dom(x::report, checker result)"), "{model}");
    assert!(model.contains("(Dom(x::item, statement) ∨ Dom(x::item, token))"), "{model}");
    // The choice is a real one: denying both alternatives contradicts it.
    let report = read("[B] Each item is a statement or a token.\n[C] No item is a statement.\n[D] No item is a token.\n");
    assert_eq!(conflicts(&report), 1, "{report}");
}

#[test]
fn a_denied_both_denies_the_conjunction() {
    // Each value alone is allowed; the two together are not.
    let body = "[X] No room is both open and closed.\n[A] While the user is present, the room is open.\n";
    let report = read(body);
    assert_eq!(conflicts(&report), 0, "{report}");
    let model = package(body).inspect(&["model"]).stdout;
    assert!(model.contains("guarantee: ¬(Dom(x::room, open) ∧ Dom(x::room, closed))"), "{model}");
}

#[test]
fn a_reading_example_compares_the_observed_entry_with_the_expected_one() {
    let example = |guarantee: &str| format!("example DENIED:\n    kind reading\n    input \"No room is both open and closed.\"\n    expect \"assume: ⊤\"\n    expect \"guarantee: {guarantee}\"\n    expect \"temporal: activation: none; throughout the applicable system scope\"\n    expect \"temporal: state no room is open and closed: holds throughout the applicable system scope\"\n    expect \"axiom: (Val(x::room, closed) → Dom(x::room, closed))\"\n    expect \"axiom: ¬(Val(x::room, closed) ∧ Val(x::room, open))\"\n    expect \"axiom: (Val(x::room, open) → Dom(x::room, open))\"\n");
    // The entry that the reader gives.
    let (code, report) = check(&example("¬(Dom(x::room, open) ∧ Dom(x::room, closed))"));
    assert_eq!(code, 0, "{}", report["diagnostics"]);
    assert_eq!(report["examples"][0]["kind"], "reading");
    // The reading that the reader gave before the denial of `both` was read: the example fails.
    let (code, report) = check(&example("(¬Dom(x::room, open) ∧ ¬Dom(x::room, closed))"));
    assert_ne!(code, 0);
    assert!(report["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "example-failed"), "{}", report["diagnostics"]);
    // An example of this kind states its entry in quoted lines.
    let (_, report) = check("example BARE:\n    kind reading\n    input \"No room is both open and closed.\"\n    expect consistent\n");
    assert!(report["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "parse-example"), "{}", report["diagnostics"]);
}

#[test]
fn a_reading_example_of_the_contract_form_states_the_assumption_and_the_guarantee_alone() {
    let example = |guarantee: &str| format!("example WHEN:\n    kind reading\n    form contract\n    input \"When the door opens, the bell shall ring.\"\n    expect \"assume: Event(x::door open)\"\n    expect \"guarantee: {guarantee}\"\n");
    // The contract that the reader gives: the temporal shape and the axioms are no part of this form.
    let (code, report) = check(&example("(Act(x::bell|ring) ∧ ¬Forbid(x::bell|ring) ∧ ¬Discouraged(x::bell|ring))"));
    assert_eq!(code, 0, "{}", report["diagnostics"]);
    assert_eq!(report["examples"][0]["observed"].as_str().unwrap().lines().count(), 2, "{}", report["examples"][0]);
    // Another guarantee is not the contract of the sentence: the example fails.
    let (code, report) = check(&example("Act(x::bell|ring)"));
    assert_ne!(code, 0);
    assert!(report["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "example-failed"), "{}", report["diagnostics"]);
}

#[test]
fn the_model_command_prints_the_reading_rules_of_each_statement() {
    let out = package("[A] When a user arrives, the checker shall report each statement that the parser rejects within 5 seconds.\n\n[B] No room is both open and closed.\n").inspect(&["model", "--rules"]).stdout;
    let rules = |id: &str| -> Vec<String> {
        let at = out.find(&format!("{id}\n  rules: ")).unwrap_or_else(|| panic!("{out}"));
        out[at..].lines().nth(1).unwrap().trim_start_matches("  rules: ").split(", ").map(str::to_string).collect()
    };
    for rule in ["frame-when", "obligation", "action", "noun-phrase-universal", "relative-object-gap", "role-deadline", "measure-quantity"] {
        assert!(rules("A").iter().any(|r| r == rule), "{rule}: {:?}", rules("A"));
    }
    assert_eq!(rules("B"), ["description", "noun-phrase-none", "predicate-enumeration"]);
}
