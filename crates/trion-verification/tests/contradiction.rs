mod common;
use common::*;
use trion_verification::{ObligationVerdict, Options};

const ROOM_A: &str = "room_type is Private and Public.";
const ROOM_B: &str = "room_type is Invalid.";

#[test]
fn single_values_accumulate_into_a_domain() {
    let analysis = run("room_type is Private.\nroom_type is Public.\n");
    assert!(!analysis.has_errors(), "{:?}", analysis.diagnostics);
    let domain: Vec<String> = analysis.model.constraints.iter().map(|c| c.guarantee.to_string()).collect();
    assert_eq!(domain, ["Dom(room_type, Private)", "Dom(room_type, Public)"]);
}

#[test]
fn an_enumeration_rejects_a_value_outside_it() {
    // Two descriptions that exclude each other leave no environment: the
    // document is incompatible.
    let analysis = run(&format!("{ROOM_A}\n{ROOM_B}\n"));
    assert_eq!(cores(&analysis, "incompatible"), [[ROOM_B.to_string(), ROOM_A.to_string()]]);
}

#[test]
fn an_enumeration_accepts_a_value_inside_it() {
    assert!(run_codes(&format!("{ROOM_A}\nroom_type is Private.\n")).is_empty());
}

#[test]
fn every_enumeration_spelling_closes_the_domain() {
    for closed in ["room_type is Private or Public.", "room_type is one of Private and Public.", "room_type is Private, Public and Secret."] {
        assert_eq!(run_codes(&format!("{closed}\n{ROOM_B}\n")), ["incompatible"], "{closed}");
    }
}

#[test]
fn a_capital_letter_value_is_not_an_article() {
    let analysis = run("kind is A or B.\nkind is C.\nThe Plan A server shall stop.\nThe Plan B server shall not stop.\n");
    assert_eq!(cores(&analysis, "incompatible").len(), 1, "{:?}", analysis.diagnostics);
    assert_eq!(analysis.model.closed_domains["kind"].iter().map(String::as_str).collect::<Vec<_>>(), ["A", "B"]);
}

#[test]
fn two_different_enumerations_contradict() {
    assert_eq!(run_codes("kind is A and B.\nkind is C and D.\n"), ["incompatible"]);
}

#[test]
fn a_conflict_names_only_its_minimal_set() {
    let analysis = run(&format!("The API shall stop.\nThe log shall rotate.\n{ROOM_A}\n{ROOM_B}\nThe cache may expire.\n"));
    assert_eq!(cores(&analysis, "incompatible"), [[ROOM_B.to_string(), ROOM_A.to_string()]]);
    let analysis = run("The API shall stop.\nThe log shall rotate.\nThe API shall not stop.\nThe cache may expire.\n");
    assert_eq!(cores(&analysis, "contradiction"), [["The API shall not stop.".to_string(), "The API shall stop.".to_string()]]);
}

#[test]
fn separate_conflicts_are_all_reported() {
    let analysis = run("The API shall stop.\nThe API shall not stop.\nThe log shall rotate.\nThe log shall not rotate.\n");
    assert_eq!(cores(&analysis, "contradiction").len(), 2);
    // Where no environment exists, every system keeps the guarantees (A/G
    // contracts with a false assumption): the document is incompatible.
    let analysis = run("a_kind is A and B.\na_kind is C.\nThe API shall stop.\nThe API shall not stop.\n");
    assert_eq!(codes(&analysis), ["incompatible"]);
}

#[test]
fn a_negated_value_contradicts_the_value() {
    assert_eq!(run_codes("room_type is never Invalid.\nroom_type is Invalid.\n"), ["incompatible"]);
}

#[test]
fn an_obligation_contradicts_a_prohibition() {
    assert_eq!(run_codes("The API shall return foo.\nThe API shall not return foo.\n"), ["contradiction"]);
    assert_eq!(run_codes("The API must return foo.\nNo API shall return foo.\n"), ["contradiction"]);
}

#[test]
fn a_permission_or_recommendation_contradicts_a_prohibition() {
    assert_eq!(run_codes("The API may return foo.\nThe API shall not return foo.\n"), ["contradiction"]);
    assert_eq!(run_codes("The API should return foo.\nThe API shall not return foo.\n"), ["recommendation-violation"]);
}

#[test]
fn a_permission_does_not_oblige() {
    assert!(run_codes("The API may return foo.\nThe API should not return foo.\n").is_empty());
}

#[test]
fn articles_do_not_change_identity() {
    assert_eq!(run_codes("The API shall return the foo.\nAPI shall not return foo.\n"), ["contradiction"]);
}

#[test]
fn owner_order_does_not_change_identity() {
    assert_eq!(run_codes("The API retry shall stop.\nThe retry of the API shall not stop.\n"), ["contradiction"]);
}

#[test]
fn a_conflict_under_one_condition_is_found() {
    let analysis = run("When the user leaves, the API shall return foo.\nWhen the user leaves, the API shall not return foo.\n");
    assert_eq!(codes(&analysis), ["contradiction"]);
    assert!(analysis.diagnostics[0].message.contains("cannot all be kept"), "{}", analysis.diagnostics[0].message);
}

#[test]
fn two_descriptions_that_exclude_their_condition_say_that_it_never_occurs() {
    // The two statements have no normative force: together they say that
    // the user never leaves, and an environment in which the user never
    // leaves exists.
    assert!(run_codes("When the user leaves, status is Closed.\nWhen the user leaves, status is Open.\n").is_empty());
    assert_eq!(run_codes("When the user leaves, status shall be Closed.\nWhen the user leaves, status shall be Open.\n"), ["contradiction"]);
}

#[test]
fn exclusive_conditions_do_not_conflict() {
    assert!(run_codes("While status is Open, the API shall return foo.\nWhile status is Closed, the API shall not return foo.\n").is_empty());
}

#[test]
fn a_condition_outside_the_domain_holds_vacuously() {
    // A statement whose condition cannot hold is kept by every system: it
    // is consistent, and nothing reports it (limit 2 of the mechanism).
    let src = "status is Open and Closed.\nWhen status is Open, the API shall stop.\nWhen status is Closed, the API shall stop.\nWhen status is Paused, the API shall start.\n";
    assert!(run_codes(src).is_empty(), "{:?}", run_codes(src));
    assert_eq!(consistency(src, &Options::default()), ObligationVerdict::Proved);
}

#[test]
fn an_exception_lifts_a_conflict() {
    assert!(run_codes("The API shall stop, unless the override is active.\nWhile the override is active, the API shall not stop.\n").is_empty());
}

#[test]
fn required_alternatives_are_a_choice() {
    assert!(run_codes("The API shall either accept the call or reject the call.\nThe API shall not accept the call.\n").is_empty());
}

#[test]
fn every_alternative_can_be_excluded() {
    assert_eq!(run_codes("The API shall either accept the call or reject the call.\nThe API shall not accept the call.\nThe API shall not reject the call.\n"), ["contradiction"]);
}

#[test]
fn numeric_bounds_compose() {
    assert_eq!(run_codes("The timeout is at most 30 seconds.\nThe timeout is at least 60 seconds.\n"), ["incompatible"]);
    assert!(run_codes("The timeout is at most 60 seconds.\nThe timeout is at least 30 seconds.\n").is_empty());
}

#[test]
fn numeric_comparisons_cover_every_operator() {
    assert_eq!(run_codes("The size is greater than 5 bytes.\nThe size is less than 5 bytes.\n"), ["incompatible"]);
    assert_eq!(run_codes("The size is equal to 5 bytes.\nThe size is at least 6 bytes.\n"), ["incompatible"]);
    assert_eq!(run_codes("The size is between 1 and 3 bytes.\nThe size is at least 4 bytes.\n"), ["incompatible"]);
}

#[test]
fn units_are_converted() {
    assert_eq!(run_codes("The timeout is at most 30 seconds.\nThe timeout is at least 1 minute.\n"), ["incompatible"]);
    assert_eq!(run_codes("The body is at most 1 KB.\nThe body is at least 2000 bytes.\n"), ["incompatible"]);
    assert!(run_codes("The timeout is at most 2 minutes.\nThe timeout is at least 90 seconds.\n").is_empty());
}

#[test]
fn different_units_are_reported() {
    assert_eq!(run_codes("The limit is at most 3 seconds.\nThe limit is at least 5 bytes.\n"), ["unit-mismatch"]);
}

#[test]
fn decimals_and_number_words_are_numbers() {
    assert_eq!(run_codes("The ratio is at most 0.5 seconds.\nThe ratio is at least 0.6 seconds.\n"), ["incompatible"]);
    assert_eq!(run_codes("The retry count is at most three.\nThe retry count is at least 4.\n"), ["incompatible"]);
}

#[test]
fn an_alias_unifies_terms() {
    assert_eq!(run_codes("alias the service = API\nThe service shall return foo.\nThe API shall not return foo.\n"), ["contradiction"]);
}

#[test]
fn an_alias_reaches_objects_values_and_chains() {
    assert_eq!(run_codes("alias reply = response\nThe API shall send a reply.\nThe API shall not send a response.\n"), ["contradiction"]);
    assert_eq!(run_codes("alias a_name = b_name\nalias b_name = c_name\nc_name is X and Y.\na_name is Z.\n"), ["incompatible"]);
}

#[test]
fn conflicting_or_cyclic_aliases_are_errors() {
    assert!(run_codes("alias x_a = y_a\nalias x_a = z_a\n").contains(&"alias-conflict".to_string()));
    assert!(run_codes("alias x_a = y_a\nalias y_a = x_a\n").contains(&"alias-cycle".to_string()));
}

#[test]
fn duplicate_ids_are_errors() {
    assert_eq!(run_codes("[A-1] The API shall stop.\n[A-1] The log shall rotate.\n"), ["DUPLICATE_ID"]);
}

#[test]
fn a_definition_guarantees_nothing() {
    let analysis = run("A session means a sequence of requests.\n");
    // The definition is an axiom about its term: it obliges nobody.
    assert!(analysis.model.constraints.iter().all(|c| !matches!(c.kind, trion_language::ConstraintKind::Spec | trion_language::ConstraintKind::Permission)), "{:?}", analysis.model.constraints);
    assert!(analysis.diagnostics.is_empty());
}

#[test]
fn a_negated_condition_is_the_complement() {
    assert!(run_codes("While the room is open, the API shall stop.\nWhile the room is not open, the API shall not stop.\n").is_empty());
    assert_eq!(run_codes("room_type is not Invalid.\nroom_type is Invalid.\n"), ["incompatible"]);
}

/// Two descriptions that exclude each other: no environment exists.
fn excluded(src: &str) {
    assert_eq!(run_codes(src), ["incompatible"], "{src}");
}

/// The conditions of the first two statements, as they are read.
fn conditions(src: &str) -> (trion_solver::Formula, trion_solver::Formula) {
    let model = run(src).model;
    (model.constraints[0].assume.clone(), model.constraints[1].assume.clone())
}

/// The condition of the second statement is the complement of the
/// condition of the first. Over a trace, the environment can change the
/// condition from one moment to the next, so the two statements are not
/// thereby kept together: a prohibition after a trigger holds for the rest
/// of the trace.
fn complements(src: &str) {
    let (first, second) = conditions(src);
    // At one moment, exactly one of the two holds.
    let status = |formulas: &[trion_solver::Formula]| trion_solver::decide(formulas).status;
    assert_eq!(status(&[first.clone(), second.clone()]), trion_solver::Status::Unsatisfiable, "{src}: {first} and {second} hold together");
    assert_eq!(status(&[trion_solver::Formula::not(first.clone()), trion_solver::Formula::not(second.clone())]), trion_solver::Status::Unsatisfiable, "{src}: neither {first} nor {second}");
}

fn flagged(src: &str) {
    assert_eq!(run_codes(src), ["contradiction"], "{src}");
}

fn clean(src: &str) {
    assert_eq!(run_codes(src), Vec::<String>::new(), "{src}");
}

#[test]
fn never_is_a_prohibition() {
    flagged("The system shall store passwords.\nThe system shall never store passwords.\n");
}

#[test]
fn no_in_a_condition_is_a_denial() {
    complements("When no heartbeat is received, the watchdog shall reset the controller.\nWhen a heartbeat is received, the watchdog shall not reset the controller.\n");
    flagged("The system shall accept connections.\nThe system shall accept no connections.\n");
}

#[test]
fn a_bounded_quantifier_is_its_own_claim() {
    // A rule has no counted subject: the bound is a description of the number.
    clean("At most 5 users have a profile.\nNo users shall have a profile.\n");
    complements("If at least one replica is healthy, then the API shall serve.\nIf no replica is healthy, then the API shall not serve.\n");
}

#[test]
fn advice_against_conflicts_with_an_obligation() {
    assert_eq!(run_codes("The API shall return 200.\nThe API should not return 200.\n"), ["recommendation-violation"]);
    assert_eq!(run_codes("The API should return 200.\nThe API should not return 200.\n"), ["recommendation-violation"]);
    clean("The API may return 200.\nThe API should not return 200.\n");
}

#[test]
fn passive_with_agent_meets_active() {
    flagged("The API shall reject the request.\nThe request shall not be rejected by the API.\n");
}

#[test]
fn a_capital_is_not_a_new_term() {
    flagged("Clients shall access the dashboard.\nThe client shall not access the dashboard.\n");
}

#[test]
fn inflected_events_are_one_event() {
    flagged("When the user sends a message, the API shall stop.\nWhen the users send a message, the API shall not stop.\n");
}

#[test]
fn required_states_exclude_each_other() {
    flagged("The door shall be Open.\nThe door shall be Closed.\n");
    flagged("When payment succeeds, the status shall become Paid.\nWhen payment succeeds, the status shall become Cancelled.\n");
}

#[test]
fn a_passive_action_is_not_a_state() {
    clean("When the job ends, the record shall be logged.\nWhen the job ends, the record shall be archived.\n");
}

#[test]
fn an_obligation_implies_its_plain_action() {
    // A deadline is measured from an activation, so each sentence names its trigger.
    flagged("When a request arrives, the gateway shall return 503 within 2 seconds.\nWhen a request arrives, the gateway shall not return 503.\n");
    clean("When a request arrives, the gateway shall return 503.\nWhen a request arrives, the gateway shall not return 503 within 2 seconds.\n");
}

#[test]
fn numbers_in_actions_compose() {
    flagged("The session shall expire after 30 minutes.\nThe session shall expire after 60 minutes.\n");
    flagged("The server shall accept at most 5 connections.\nThe server shall accept at least 10 connections.\n");
    clean("When a request arrives, the gateway shall respond within 2 seconds.\nWhen a request arrives, the gateway shall respond within 5 seconds.\n");
}

#[test]
fn overlapping_numeric_conditions_conflict() {
    flagged("When the size is at least 100, the API shall stop.\nWhen the size is at most 100, the API shall not stop.\n");
    // Exclusive at one moment; the size of the environment can cross 100
    // between two moments, and the prohibition then meets the obligation.
    complements("When the size is greater than 100, the API shall stop.\nWhen the size is at most 100, the API shall not stop.\n");
    flagged("environment size\nWhen the size is greater than 100, the API shall stop.\nWhen the size is at most 100, the API shall not stop.\n");
}

#[test]
fn two_events_can_occur_together() {
    // Nothing says that the door never opens while the bell rings.
    flagged("When the door opens, the API shall stop.\nWhen the bell rings, the API shall not stop.\n");
    // The bell and the door are excluded at one moment only: the bell can
    // ring, and the door open at a later moment, after which the API may
    // not stop and has to.
    flagged("When the door opens, the API shall stop.\nWhen the bell rings, the API shall not stop.\nWhile the bell rings, no door opens.\n");
    clean("When the door opens, the API shall stop.\nWhen the bell rings, the API shall log the bell.\n");
}

#[test]
fn a_narrow_prohibition_contradicts_a_permission_where_both_apply() {
    // No statement narrows another: where the room is archived both apply.
    flagged("The user may delete the message.\nWhile the room is archived, the user shall not delete the message.\n");
    clean("The user may delete the message, unless the room is archived.\nWhile the room is archived, the user shall not delete the message.\n");
}

#[test]
fn an_action_triggers_its_event() {
    flagged("When the door opens, the controller shall stop the motor.\nWhen the controller stops the motor, the alarm shall sound.\nWhen the door opens, the alarm shall not sound.\n");
}

#[test]
fn entering_a_mode_is_being_in_it() {
    flagged("When the door opens, the controller shall enter safe mode.\nWhile the controller is in safe mode, the alarm shall sound.\nWhen the door opens, the alarm shall not sound.\n");
}

#[test]
fn a_pronoun_is_its_antecedent() {
    let guarantee = |src: &str| run(src).model.constraints[0].guarantee.to_string();
    assert_eq!(guarantee("When the server fails, it shall restart.\n"), guarantee("When the server fails, the server shall restart.\n"));
}

#[test]
fn number_forms_are_numbers() {
    excluded("The limit is at most 1,000 bytes.\nThe limit is at least 2KB.\n");
    excluded("The load is at most 80%.\nThe load is at least 90 percent.\n");
    excluded("The offset is at most -5.\nThe offset is at least 0.\n");
}

#[test]
fn comparators_are_numeric() {
    for bound in ["above 100", "over 100", "more than 100", "greater than 100"] {
        excluded(&format!("The size is {bound}.\nThe size is at most 100.\n"));
    }
    for bound in ["below 100", "under 100", "fewer than 100", "less than 100"] {
        excluded(&format!("The size is {bound}.\nThe size is at least 100.\n"));
    }
    excluded("The size is no more than 100.\nThe size is greater than 100.\n");
    excluded("The size is no less than 100.\nThe size is less than 100.\n");
    excluded("The size is greater than or equal to 100.\nThe size is less than 100.\n");
    excluded("The size is exactly 100.\nThe size is above 100.\n");
}

#[test]
fn verbal_bounds_are_numeric() {
    flagged("When the size exceeds 100, the API shall stop.\nWhen the size is greater than 100, the API shall not stop.\n");
    flagged("When the count reaches 5, the API shall stop.\nWhen the count is at least 5, the API shall not stop.\n");
}

#[test]
fn until_is_the_complement() {
    complements("Until the timer expires, the API shall stop.\nWhen the timer expires, the API shall not stop.\n");
}

#[test]
fn coordinated_actions_each_hold() {
    flagged("The API shall notify the customer and alert the team.\nThe API shall not alert the team.\n");
    flagged("The API shall notify the customer and shall not create an order.\nThe API shall create an order.\n");
}

#[test]
fn a_bare_or_is_a_choice() {
    clean("The system shall notify the customer or alert the team.\nThe system shall not notify the customer.\n");
    flagged("The system shall notify the customer or alert the team.\nThe system shall not notify the customer.\nThe system shall not alert the team.\n");
}

#[test]
fn does_not_is_the_complement() {
    complements("If the file does not exist, then the tool shall exit.\nIf the file exists, then the tool shall not exit.\n");
    complements("If the job has not completed, then the tool shall wait.\nIf the job completes, then the tool shall not wait.\n");
}

#[test]
fn a_condition_can_list_values() {
    let (listed, _) = conditions("When the token is expired or revoked, the API shall reject the call.\nWhen the token is valid, the API shall not reject the call.\n");
    assert_eq!(listed.to_string(), "(Val(token, expired) ∨ Val(token, revoked))");
    flagged("When the token is expired or revoked, the API shall reject the call.\nWhen the token is revoked, the API shall not reject the call.\n");
}
