mod common;
use common::*;
use trion_language::VocabularyMode;
use trion_verification::{analyze, Options};

const LIBRARY: &str = r"package grpc
role service:
    activate: The $subject shall use gRPC communication.
    form METHOD: The $subject $operation shall $action. where $operation matches /^\/[A-Za-z_.]+\/[A-Za-z_]+$/ when $operation matches /^(\/|[A-Z]+ \/)/
    required ERRORS: The $subject shall define status codes.
";

const USES_GRPC: &str = "The API shall use gRPC communication.\nThe API shall define status codes.\n";

fn with_library(src: &str) -> trion_verification::Analysis {
    analyze(&set_of(&[("main", true, src), ("grpc", false, LIBRARY)], VocabularyMode::Inferred), &Options::default())
}

#[test]
fn two_sentences_alone_are_consistent() {
    assert!(run_codes("The API shall use gRPC communication.\nThe API GET /foo shall return foo.\n").is_empty());
}

#[test]
fn an_imported_form_rejects_a_foreign_operation() {
    let analysis = with_library(&format!("{USES_GRPC}The API GET /foo shall return foo.\n"));
    assert_eq!(codes(&analysis), ["shape-violation"]);
    let refs: Vec<&str> = analysis.diagnostics[0].refs.iter().map(|r| r.id.as_str()).collect();
    assert!(refs.contains(&"grpc.service::METHOD"), "{refs:?}");
    assert!(refs.contains(&"main.trion:2"), "{refs:?}");
    assert!(refs.contains(&"main.trion:4"), "{refs:?}");
}

#[test]
fn a_shape_violation_is_not_called_a_contradiction() {
    let analysis = with_library(&format!("{USES_GRPC}The API GET /foo shall return foo.\n"));
    assert!(analysis.diagnostics[0].message.contains("no such thing exists"));
    assert!(!codes(&analysis).contains(&"contradiction".to_string()));
}

#[test]
fn a_conforming_operation_passes() {
    assert!(codes(&with_library(&format!("{USES_GRPC}The API /chat.Room/Get shall return foo.\n"))).is_empty());
}

#[test]
fn an_unbound_term_is_not_checked() {
    assert!(codes(&with_library("The CLI GET /foo shall return foo.\n")).is_empty());
}

#[test]
fn an_explicit_binding_applies_the_role() {
    let analysis = with_library("bind Gateway as grpc.service.\nThe Gateway shall define status codes.\nThe Gateway GET /foo shall return foo.\n");
    assert_eq!(codes(&analysis), ["shape-violation"]);
}

#[test]
fn an_alias_reaches_a_bound_term() {
    assert_eq!(codes(&with_library(&format!("alias the service = API\n{USES_GRPC}The service GET /foo shall return foo.\n"))), ["shape-violation"]);
}

#[test]
fn a_wildcard_verb_covers_any_action() {
    assert_eq!(codes(&with_library(&format!("{USES_GRPC}The API GET /foo shall stream foo.\n"))), ["shape-violation"]);
}

#[test]
fn a_prohibition_is_checked_too() {
    assert_eq!(codes(&with_library(&format!("{USES_GRPC}The API GET /foo shall not return foo.\n"))), ["shape-violation"]);
}

#[test]
fn coordination_cannot_hide_an_operation() {
    let analysis = with_library(&format!("{USES_GRPC}The API /chat.Room/Get and the API GET /foo shall return foo.\n"));
    assert_eq!(codes(&analysis), ["shape-violation"]);
}

#[test]
fn a_condition_cannot_hide_an_operation() {
    assert_eq!(codes(&with_library(&format!("{USES_GRPC}When the `GET /foo` of the API fails, the log shall rotate.\n"))), ["shape-violation"]);
}

#[test]
fn a_guarded_operation_is_still_checked() {
    assert_eq!(codes(&with_library(&format!("{USES_GRPC}While the room is open, the API GET /foo shall return foo.\n"))), ["shape-violation"]);
}

#[test]
fn a_selector_limits_the_rule() {
    assert!(codes(&with_library(&format!("{USES_GRPC}The API timeout shall expire.\n"))).is_empty());
}

#[test]
fn a_negated_form_rejects_a_match() {
    let library = "package lib\nrole r:\n    activate: The $subject shall use x.\n    form NO-TMP: The $subject $name shall $action. where $name does not match /^tmp/\n";
    let main = "The API shall use x.\nThe API tmp1 shall stop.\nThe API real shall stop.\n";
    let analysis = analyze(&set_of(&[("main", true, main), ("lib", false, library)], VocabularyMode::Inferred), &Options::default());
    assert_eq!(codes(&analysis), ["shape-violation"]);
    assert!(analysis.diagnostics[0].refs.iter().any(|r| r.text == "The API tmp1 shall stop."));
}

#[test]
fn a_role_required_form_is_a_definite_omission() {
    let analysis = with_library("The API shall use gRPC communication.\n");
    assert_eq!(codes(&analysis), ["missing-required-form"]);
    assert!(analysis.diagnostics[0].message.contains("status codes"));
}

#[test]
fn imported_specifications_compose_with_local_ones() {
    let analysis = analyze(&set_of(&[("main", true, "use lib\nThe API shall not stop.\n"), ("lib", false, "term API: entity\n[L-1] The API shall stop.\n")], VocabularyMode::Inferred), &Options::default());
    assert_eq!(codes(&analysis), ["contradiction"]);
    assert!(analysis.diagnostics[0].refs.iter().any(|r| r.id == "lib::L-1"));
}

#[test]
fn specifications_of_an_unused_namespace_do_not_meet_local_terms() {
    let analysis = analyze(&set_of(&[("main", true, "The API shall not stop.\n"), ("lib", false, "[L-1] The API shall stop.\n")], VocabularyMode::Inferred), &Options::default());
    assert!(codes(&analysis).is_empty(), "{:?}", analysis.diagnostics);
}
