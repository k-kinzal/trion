//! The contract of each statement as `trion` writes it: one contract for
//! each simple sentence (AGENTS.md, rule 1), schematic in the individuals
//! that it speaks about, with its time, and with the scope of an assumption.

mod common;
use common::*;
use serde_json::Value;

fn report(text: &str) -> Value {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", text)]);
    f.convert(&["--json"]).json()
}

fn contracts_of<'a>(report: &'a Value, id: &str) -> Vec<&'a Value> {
    report["contracts"].as_array().unwrap().iter().filter(|c| c["statement"]["id"] == id).collect()
}

const GREET: &str = "system API\nenvironment user, room\n[A] When a user enters a room, the API shall greet the user.\n";

#[test]
fn a_sentence_about_individuals_is_one_schematic_contract_and_the_declaration_changes_only_the_bound() {
    let plain = report(GREET);
    let declared = report(&format!("individuals user, room\n{GREET}"));
    // One contract each, for the statement and not for its instances.
    let (plain_a, declared_a) = (contracts_of(&plain, "A"), contracts_of(&declared, "A"));
    assert_eq!((plain_a.len(), declared_a.len()), (1, 1), "{declared}");
    assert!(!declared["contracts"].as_array().unwrap().iter().any(|c| c["statement"]["id"].as_str().unwrap().contains('/')), "{declared}");
    // The same formulas: the individual is named by the noun of its variable.
    assert_eq!(plain_a[0]["assume"], declared_a[0]["assume"], "{declared}");
    assert_eq!(plain_a[0]["guarantee"], declared_a[0]["guarantee"], "{declared}");
    assert_eq!(declared_a[0]["statement"]["text"], "When a user enters a room, the API shall greet the user.");
    // The declaration says which names are variables over a type ...
    assert_eq!(declared_a[0]["parameters"], serde_json::json!([["user", "user"], ["room", "room"]]));
    assert_eq!(plain_a[0]["parameters"], serde_json::json!([]));
    // ... and the bound of the obligations: one individual of each type, or N.
    let proposition = |r: &Value| r["obligations"].as_array().unwrap().iter().find(|o| o["name"] == "consistency").unwrap()["proposition"].as_str().unwrap().to_string();
    assert!(proposition(&plain).starts_with("within traces of 3 moments, domains of one individual of each type: "), "{}", proposition(&plain));
    assert!(proposition(&declared).starts_with("within traces of 3 moments, domains of 3 individuals: "), "{}", proposition(&declared));
}

#[test]
fn a_contract_has_the_time_of_its_activation_and_of_its_response() {
    let r = report("system API\nenvironment request\nprimitive API, request\n[R] When a request arrives, the API shall answer the request within 5 seconds.\n");
    let contract = contracts_of(&r, "R")[0];
    let timing: Vec<&str> = contract["timing"].as_array().unwrap().iter().map(|l| l.as_str().unwrap()).collect();
    assert!(timing.contains(&"activation: each occurrence of Event(request arrive)"), "{timing:?}");
    assert!(timing.iter().any(|l| l.contains("action API|answer request") && l.contains("completion within 5 seconds measured from the activation")), "{timing:?}");
    // The MMT form writes the contract with its time.
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "system API\nenvironment request\nprimitive API, request\n[R] When a request arrives, the API shall answer the request within 5 seconds.\n")]);
    let out = tempfile::tempdir().unwrap();
    assert_eq!(f.convert(&["--out", &out.path().to_string_lossy()]).code, 0);
    let mmt = std::fs::read_to_string(out.path().join("source/specification.mmt")).unwrap();
    let form = trioc_cli::mmt::Form::read(&mmt).unwrap();
    let written = form.contracts.iter().find(|c| c.id == "R").expect("the contract of R");
    assert_eq!(written.timing.first().map(String::as_str), Some("activation: each occurrence of Event(request arrive)"), "{mmt}");
}

#[test]
fn an_assumption_states_the_guarantees_that_it_is_distributed_to() {
    let r = report("system API\nenvironment door, room\n[E] The door is open or closed.\nWhile the door is open:\n    [D] The room is never archived.\n    [G] The API shall log the message.\n");
    assert_eq!(contracts_of(&r, "E")[0]["scope"], serde_json::json!({"kind": "document"}), "{r}");
    assert_eq!(contracts_of(&r, "D")[0]["scope"], serde_json::json!({"kind": "block", "head": "While the door is open", "file": "a.trion", "line": 5}), "{r}");
    assert_eq!(contracts_of(&r, "G")[0]["scope"], Value::Null, "{r}");
}
