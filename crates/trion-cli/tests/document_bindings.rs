//! Types, instances and bindings of a document: what a definition declares,
//! what two bindings require, and what an undecided result leaves as it was.

mod common;
use common::*;
use serde_json::Value;

fn fixture(text: &str) -> Fixture {
    Fixture::new(&[("trion.toml", "[package]\nname = \"p\"\n"), ("a.trion", text)])
}

fn check(text: &str, flags: &[&str]) -> Value {
    let mut args = vec!["verify", "--json"];
    args.extend(flags);
    fixture(text).trion(&args).json()
}

fn model(text: &str) -> String {
    fixture(text).inspect(&["model"]).stdout
}

#[test]
fn a_type_definition_declares_no_instance() {
    let text = "primitive place\n\nA room means a place.\n";
    // The definition is an inclusion of classes; nothing says that a room exists.
    let model = model(text);
    assert!(model.contains("Dom(room, place)"), "{model}");
    assert!(!model.contains("exists"), "{model}");
    // A variable of that type is still unbound.
    let report = check("primitive place\nprimitive checker\n\nA room means a place.\n\nThe checker shall retain R.\n", &[]);
    assert_eq!(report_codes(&report), ["UNBOUND_VARIABLE"], "{report}");
}

#[test]
fn a_type_name_and_an_instance_name_are_told_apart() {
    // `room` names the type in both statements; `Q` names one room of the
    // first statement only, so the second statement cannot use it.
    let text = "primitive place\nprimitive checker\n\nA room means a place.\n\nThere is a room Q.\n\nThe checker shall retain Q.\n";
    let report = check(text, &[]);
    assert_eq!(report_codes(&report), ["UNBOUND_VARIABLE"], "{report}");
    // The type name needs no binding.
    let report = check("primitive place\nprimitive checker\n\nA room means a place.\n\nThe checker shall retain each room.\n", &[]);
    assert!(report_codes(&report).is_empty(), "{report}");
}

#[test]
fn two_bindings_do_not_require_two_objects() {
    let text = "primitive place\n\nA room means a place.\n\nThere is a room A.\n\nThere is a room B.\n\nThere is at most 1 room.\n";
    let report = check(text, &[]);
    assert!(report_codes(&report).is_empty(), "{report}");
    assert_eq!(report["consistency"]["status"], "satisfiable", "{report}");
}

#[test]
fn an_undecided_result_leaves_an_invalid_binding_reported() {
    let text = "primitive checker\nprimitive report\n\n[A]\nThe checker shall retain R.\n\n[B]\nThe checker shall print the report.\n\n[C]\nThe checker shall not print the report.\n";
    let decided = check(text, &[]);
    assert!(report_codes(&decided).contains(&"UNBOUND_VARIABLE".to_string()), "{decided}");
    // With no decisions allowed nothing is decided, and the binding is still invalid.
    let undecided = check(text, &["--decision-limit", "0"]);
    assert!(report_codes(&undecided).contains(&"UNBOUND_VARIABLE".to_string()), "{undecided}");
}

#[test]
fn a_diagram_and_its_expansion_have_one_environment() {
    let flow = "[F] When a request arrives, the API shall follow this flow:\n    step inspect: inspect the request;\n    step answer: send a reply;\n    start inspect\n    inspect -> answer\n    finish answer\n";
    let f = fixture(flow);
    let items = f.inspect(&["expand", "--json"]).json();
    let expansions: Vec<String> = items.as_array().unwrap().iter().filter(|i| i["id"].as_str().is_some_and(|id| id.starts_with('F'))).map(|i| i["expansion"].to_string()).collect();
    assert!(!expansions.is_empty(), "{items}");
    // Each sentence of the expansion stands under the condition of the diagram.
    for expansion in &expansions {
        assert!(expansion.to_lowercase().contains("when a request arrives"), "{expansion}");
    }
}
