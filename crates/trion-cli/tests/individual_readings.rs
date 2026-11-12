//! What a statement says about individuals is a part of its own reading
//! where the statement distinguishes individuals itself, and a definition
//! reaches the individuals of its term. Each test runs its reproducer as the
//! body of `namespace p.x:` in a package `p`.

mod common;
use common::*;
use serde_json::Value;

fn package(body: &str) -> Fixture {
    let indented: String = body.lines().map(|line| if line.is_empty() { "\n".to_string() } else { format!("    {line}\n") }).collect();
    Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\nentry = \"a.trion\"\n"), ("a.trion", &format!("package p edition \"1\"\n\nnamespace p.x:\n{indented}"))])
}

fn check(body: &str) -> Value {
    package(body).trion(&["verify", "--json"]).json()
}

fn contradicts(body: &str) -> bool {
    check(body)["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "contradiction")
}

fn kinds(body: &str, id: &str) -> Vec<String> {
    let model = package(body).inspect(&["model", "--json"]).json();
    model["constraints"].as_array().unwrap().iter().filter(|c| c["refs"][0]["id"] == id).map(|c| c["kind"].as_str().unwrap().to_string()).collect()
}

const TERMS: &str = "primitive user\nprimitive account\nprimitive room\nprimitive name\nprimitive owner\n";

#[test]
fn a_definition_holds_of_each_individual_of_its_term() {
    let definition = format!("{TERMS}[D] A guest means a user that has no account.\n");
    // Some guest with an account is no guest.
    assert!(contradicts(&format!("{definition}[S] Some guest has an account.\n")));
    // A user may have an account: the difference is said of guests only.
    assert!(!contradicts(&format!("{definition}[S] Some user has an account.\n")));
    assert!(!contradicts(&definition));
}

#[test]
fn each_individual_of_the_kind_with_the_difference_is_of_the_term() {
    let definition = format!("{TERMS}[D] A guest means a user that has no account.\n");
    // A user without an account is a guest, so a package without guests has no such user.
    let body = format!("{definition}[U] Some user has no account.\n[G] The number of guests is at most 0.\n");
    assert!(contradicts(&body), "{}", check(&body));
    assert!(!contradicts(&format!("{definition}[U] Some user has no account.\n")));
}

#[test]
fn a_statement_that_distinguishes_individuals_reads_them_itself() {
    let body = format!("{TERMS}[N] No two rooms have the same name.\n");
    // The pair denial is a part of the reading of its statement, alone.
    assert!(kinds(&body, "N").contains(&"Axiom".to_string()), "{:?}", kinds(&body, "N"));
    assert!(!kinds(&body, "N").contains(&"Carried".to_string()));
    let model = package(&body).inspect(&["model"]).stdout;
    assert!(model.contains("¬(x::name(x::room#1, x::name#1) ∧ x::name(x::room#2, x::name#1))"), "{model}");
    // It is the same reading beside other statements.
    let with = format!("{body}[E] Each room has exactly 1 name.\n[P] There are at least 2 rooms.\n");
    let report = package(&with).trion(&["verify", "--json", "--properties"]).json();
    assert_eq!(report["properties"].as_array().map(Vec::len), Some(0), "{}", report["properties"]);
}

#[test]
fn two_nouns_of_one_carrier_speak_about_one_relation() {
    // A guest is a user, so an account of a guest is an account of that user.
    let body = format!("{TERMS}[I] Each guest is a user.\n[U] Each user has at most 1 account.\n[G] Some guest has at least 2 accounts.\n");
    assert!(contradicts(&body), "{}", check(&body));
    // Without the inclusion the two nouns name different individuals.
    assert!(!contradicts(&format!("{TERMS}[U] Each user has at most 1 account.\n[G] Some guest has at least 2 accounts.\n")));
    // A relation of users does not make every user with an account a guest.
    assert!(!contradicts(&format!("{TERMS}[I] Each guest is a user.\n[G] Each guest has no account.\n[U] Some user has an account.\n")));
}

#[test]
fn a_defined_state_holds_exactly_when_its_differences_hold() {
    let definition = "[F4]\nAn archived room means a room that accepts no messages.\n";
    // The state excludes the action.
    assert!(contradicts(&format!("{definition}\n[F5]\nWhile the room is archived, the room shall accept messages.\n")));
    // The definition is an equivalence over the disposition of the room: both directions are stated.
    let model = package(definition).inspect(&["model"]).stdout;
    assert!(model.contains("disposed to"), "{model}");
    assert!(model.contains("→ Val(x::room, archived)"), "{model}");
    // An idle room is not archived for being idle.
    assert!(!contradicts(&format!("{definition}\n[F6]\nWhile the room is active, the room shall accept messages.\n\n[F7]\nThe room shall not be archived.\n")));
}
