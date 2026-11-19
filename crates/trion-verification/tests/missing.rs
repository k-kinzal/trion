mod common;
use common::*;

#[test]
fn a_closed_domain_reports_an_unhandled_value() {
    let analysis = run("room_type is Private and Public.\nWhen room_type is Private, the API shall reject guests.\n");
    assert_eq!(codes(&analysis), ["missing-case"]);
    assert!(analysis.diagnostics[0].message.contains("room_type is Public"));
}

#[test]
fn a_fully_handled_domain_reports_nothing() {
    assert!(run_codes("room_type is Private and Public.\nWhen room_type is Private, the API shall reject guests.\nWhen room_type is Public, the API shall admit guests.\n").is_empty());
}

#[test]
fn a_closed_domain_nobody_branches_on_reports_nothing() {
    assert!(run_codes("room_type is Private and Public.\nThe API shall stop.\n").is_empty());
}

#[test]
fn an_open_domain_never_reports_a_missing_case() {
    assert!(run_codes("room_type is Private.\nroom_type is Public.\nWhen room_type is Private, the API shall reject guests.\n").is_empty());
}

#[test]
fn unrelated_specifications_are_listed_not_called_missing() {
    let analysis = run("The API shall return foo.\nThe API shall log foo.\nThe printer shall warm up.\n");
    assert!(analysis.diagnostics.is_empty());
    assert_eq!(analysis.relations.components.len(), 2);
    assert_eq!(analysis.relations.isolated.len(), 1);
    assert_eq!(analysis.relations.isolated[0].text, "The printer shall warm up.");
}

#[test]
fn a_term_relates_to_terms_it_prefixes() {
    let analysis = run("The API shall stop.\nThe API GET /foo shall return bar.\n");
    assert_eq!(analysis.relations.components.len(), 1);
    assert!(analysis.relations.isolated.is_empty());
}

#[test]
fn conditions_relate_specifications() {
    let analysis = run("The room shall open.\nWhen the room is full, the printer shall warm up.\n");
    assert_eq!(analysis.relations.components.len(), 1);
}

#[test]
fn single_use_terms_are_listed() {
    let analysis = run("The API shall return foo.\nThe API shall log foo.\nThe API shall drop bar.\n");
    assert_eq!(analysis.relations.single_use_terms, ["bar"]);
}

#[test]
fn an_exception_covers_the_other_values() {
    assert!(run_codes("valve is Open and Closed.\nThe pump shall stop, unless the valve is Open.\nIf the valve is Open, then the pump shall not stop.\n").is_empty());
}

#[test]
fn a_missing_case_uses_the_whole_guard() {
    let analysis = run("The mode is open, closed, or pending.\nWhile the mode is not open and the mode is not closed, the API shall stop.\n");
    assert_eq!(codes(&analysis), ["missing-case", "missing-case"]);
    let messages: Vec<_> = analysis.diagnostics.iter().map(|d| d.message.as_str()).collect();
    assert!(messages.iter().any(|message| message.contains("mode is open")));
    assert!(messages.iter().any(|message| message.contains("mode is closed")));
    assert!(messages.iter().all(|message| !message.contains("mode is pending")));
    assert!(run_codes("The mode is open, closed, or pending.\nWhile the mode is not open or the mode is not closed, the API shall stop.\n").is_empty());
}
