//! Forms that passed while they said less than their words: each is now read
//! for what it says, or the checker rejects it.

mod common;
use common::*;

const HEAD: &str = "primitive author\nprimitive constraint\nprimitive string\nprimitive quote\nprimitive reader\nprimitive reference\nprimitive user\nprimitive binding\nprimitive variable\nprimitive service\nprimitive namespace\nprimitive term\nprimitive checker\nprimitive gate\nprimitive diagnostic\nprimitive edition\nprimitive request\n\n";

fn check(text: &str) -> serde_json::Value {
    Fixture::new(&[("a.trion", &format!("{HEAD}{text}"))]).trion(&["verify", "--json", "a.trion"]).json()
}

/// The messages of the parts that have no reading, and of the sentences that have no parse.
fn rejected(text: &str) -> Vec<String> {
    let report = check(text);
    let mut out: Vec<String> = report["opaque"].as_array().unwrap().iter().map(|d| d["message"].as_str().unwrap().to_string()).collect();
    out.extend(report["diagnostics"].as_array().unwrap().iter().filter(|d| d["severity"] == "error").map(|d| format!("{}: {}", d["code"].as_str().unwrap(), d["message"].as_str().unwrap())));
    out
}

fn contradicts(text: &str) {
    assert!(report_codes(&check(text)).iter().any(|c| c == "contradiction"), "no contradiction in:\n{text}\n{:?}", rejected(text));
}

fn consistent(text: &str) {
    let found = rejected(text);
    assert!(found.is_empty(), "{text}\n{found:?}");
}

#[test]
fn a_bare_verb_before_a_conjunction_takes_the_object_and_the_roles_of_the_next_verb() {
    // Both verbs act on the constraint: forbidding both leaves the choice empty.
    contradicts("[A]\nThe author shall remove or weaken a constraint.\n\n[B]\nThe author shall not remove a constraint.\n\n[C]\nThe author shall not weaken a constraint.\n");
    consistent("[A]\nThe author shall remove or weaken a constraint.\n\n[B]\nThe author shall not remove a constraint.\n");
    // `begin` takes the role of `end`.
    contradicts("[A]\nEach string shall begin and end with a quote.\n\n[B]\nEach string shall not begin with a quote.\n");
    // A verb that takes nothing is written last and shares nothing.
    consistent("[A]\nThe author shall remove a constraint or wait.\n\n[B]\nThe author shall not wait a constraint.\n");
}

#[test]
fn a_plural_noun_ends_its_noun_phrase() {
    let found = rejected("[A]\nThe reader shall list references available for the user.\n");
    assert!(found.iter().any(|m| m.contains("`references` is a plural noun before further words of a name")), "{found:?}");
    let found = rejected("[A]\nThe reader shall list the constraints concerning users.\n");
    assert!(found.iter().any(|m| m.contains("`constraints` is a plural noun")), "{found:?}");
    consistent("[A]\nThe reader shall list the references that are available for the user.\n\n[B]\nThe reader shall list the references.\n");
    // A possessive and a word in `-ss` or `-us` are no plurals.
    consistent("[A]\nThe reader shall list the status report.\n\n[B]\nThe reader shall list the status report of the user.\n");
}

#[test]
fn a_rule_has_no_counted_subject() {
    for subject in ["Two bindings", "At least 2 bindings", "At most 3 bindings", "Exactly 2 bindings"] {
        let found = rejected(&format!("[A]\n{subject} shall not name a variable.\n"));
        assert!(found.iter().any(|m| m.contains("a rule has no counted subject")), "{subject}: {found:?}");
    }
    consistent("[A]\nEach binding shall name a variable.\n\n[B]\nEach binding shall name at least 1 variable.\n");
}

#[test]
fn within_is_a_deadline_or_the_place_of_a_declared_term() {
    // A declared term is a place.
    consistent("[A]\nThe checker shall rename a term within the namespace.\n\n[B]\nThe checker shall rename a term.\n");
    // A phrase that nothing bounds in time and nothing declares says neither when nor where.
    let found = rejected("[A]\nThe service shall respond within the configured timeout.\n\n[B]\nThe service shall respond.\n");
    assert!(found.iter().any(|m| m.contains("neither a quantity of time nor a declared term")), "{found:?}");
    // A quantity that a statement bounds in time is a deadline.
    consistent("[T]\nThe configured timeout is at most 3 seconds.\n\n[D]\nThe service shall respond within the configured timeout.\n");
}

#[test]
fn this_without_an_antecedent_is_unresolved() {
    let found = rejected("[A]\nThe checker shall accept this edition.\n");
    assert!(found.iter().any(|m| m.contains("UNRESOLVED_REFERENCE") || m.contains("no single earlier subject")), "{found:?}");
    consistent("[A]\nWhen a request arrives, the checker shall accept this request.\n\n[B]\nThe checker shall accept the request.\n");
}

#[test]
fn a_controlled_clause_is_permitted_or_required() {
    // To allow what is forbidden is a contradiction.
    contradicts("[B]\nThe checker shall allow the gate to open.\n\n[C]\nThe gate shall not open.\n");
    contradicts("[B]\nThe checker shall let the gate open.\n\n[C]\nThe gate shall not open.\n");
    // To forbid the permission forbids the action.
    contradicts("[B]\nThe checker shall not allow the gate to open.\n\n[C]\nThe gate shall open.\n");
    // To require is to oblige.
    contradicts("[B]\nThe checker shall require the gate to close.\n\n[C]\nThe gate shall not close.\n");
    // A permission obliges nothing.
    consistent("[B]\nThe checker shall allow the gate to open.\n\n[C]\nThe gate shall open.\n");
    // `let` without what the thing does has no reading.
    let found = rejected("[B]\nThe checker shall let the gate.\n");
    assert!(found.iter().any(|m| m.contains("`let` takes a thing and what the thing does")), "{found:?}");
}

#[test]
fn a_description_of_a_named_subject_is_a_fact() {
    contradicts("[A]\nThe checker reports the diagnostic.\n\n[B]\nThe checker shall not report the diagnostic.\n");
    // A universal subject asserts no instance.
    consistent("[A]\nEach checker reports the diagnostic.\n\n[B]\nThe checker shall not report the diagnostic.\n");
}

#[test]
fn a_possessive_word_is_no_word_of_a_name() {
    let found = rejected("[A]\nThe reader shall list the user's references.\n");
    assert!(found.iter().any(|m| m.contains("`user's` is a possessive inside a name")), "{found:?}");
    consistent("[A]\nThe reader shall list the references of the user.\n\n[B]\nThe reader shall list the references.\n");
}
