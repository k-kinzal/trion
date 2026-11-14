//! The temporal reading of statements: activation, intervals, deadlines,
//! lifetimes and the bounded trace that the check is asked over.

mod common;
use common::*;
use serde_json::Value;

fn fixture(text: &str) -> Fixture {
    Fixture::new(&[("a.trion", text)])
}

fn codes(text: &str) -> Vec<String> {
    report_codes(&fixture(text).trion(&["verify", "--json", "a.trion"]).json())
}

/// As `codes`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn codes_of_the_analysis(text: &str) -> Vec<String> {
    analysis_codes(&fixture(text).trion(&["verify", "--json", "a.trion"]).json())
}

/// The text of `trion model`.
fn model(text: &str) -> String {
    fixture(text).inspect(&["model", "a.trion"]).stdout
}

/// The temporal shape of the statement `id`.
fn shape(text: &str, id: &str) -> Value {
    let model = fixture(text).inspect(&["model", "--json", "a.trion"]).json();
    model["temporal"].as_array().unwrap().iter().find(|o| o["statement"]["id"] == id).unwrap_or_else(|| panic!("no shape for {id}: {model}")).clone()
}

#[test]
fn a_feature_scope_selects_configurations_and_triggers_nothing() {
    let text = "[A] Where the device includes a cache, the device shall flush the cache.\n";
    let printed = model(text);
    assert!(printed.contains("assume:    Config(device include cache)"), "{printed}");
    assert!(!printed.contains("Event(device include cache)"), "{printed}");
    let shape = shape(text, "A");
    assert_eq!(shape["configuration"], serde_json::json!(["Config(device include cache)"]));
    assert_ne!(shape["activation"]["kind"], "occurrence");
    // Two features of one device are not two values of one attribute.
    assert!(codes_of_the_analysis("[A] Where the device includes a cache, the device shall flush the cache.\n[B] Where the device includes a modem, the device shall reset the modem.\n").is_empty());
}

#[test]
fn a_state_scope_constrains_the_response_throughout_its_intervals() {
    let text = "[A] While the door is open, the alarm shall sound.\n[B] While the door is open, the light shall be lit.\n";
    let printed = model(text);
    assert!(printed.contains("activation: throughout each interval of Val(door, open)"), "{printed}");
    assert!(printed.contains("state light|be lit: holds throughout each interval of its state scope"), "{printed}");
    assert_eq!(shape(text, "A")["activation"], serde_json::json!({"kind": "interval", "conditions": ["Val(door, open)"]}));
    // At every moment where the door is open the alarm sounds, so a ban on the sound conflicts.
    assert_eq!(codes("[A] While the door is open, the alarm shall sound.\n[N] The alarm shall not sound.\n"), ["contradiction"]);
}

#[test]
fn every_action_response_has_an_activation_policy() {
    let text = "[A] When the bell rings, the API shall stop.\n[B] While the door is open, the API shall wait.\n[C] The API shall log each call.\n";
    assert_eq!(shape(text, "A")["activation"]["kind"], "occurrence");
    assert_eq!(shape(text, "B")["activation"]["kind"], "interval");
    let untriggered = shape(text, "C");
    assert_eq!(untriggered["activation"]["kind"], "invocation");
    assert_eq!(untriggered["activation"]["boundary"], "each invocation of log");
}

#[test]
fn an_untriggered_requirement_applies_to_each_invocation_of_its_declared_operation() {
    let text = "predicate respond(request)\n[A] The gateway shall respond within 2 seconds.\n";
    assert!(codes_of_the_analysis(text).is_empty(), "{:?}", codes_of_the_analysis(text));
    let shape = shape(text, "A");
    assert_eq!(shape["activation"], serde_json::json!({"kind": "invocation", "operation": "respond", "declared": true, "inputs": ["request"], "boundary": "each invocation of respond"}));
    assert_eq!(shape["responses"][0]["deadline"]["origin"]["kind"], "invocation");
    assert!(model(text).contains("declared operation respond(request)"));
}

#[test]
fn an_untriggered_state_requirement_holds_without_an_activation() {
    let text = "[A] The valve shall be closed.\n";
    assert_eq!(shape(text, "A")["activation"]["kind"], "always");
    let printed = model(text);
    assert!(printed.contains("activation: none; throughout the applicable system scope"), "{printed}");
    assert!(printed.contains("state valve|be closed: holds throughout the applicable system scope"), "{printed}");
    // The state holds at every moment, so no moment can hold another value.
    assert_eq!(codes("[A] The valve shall be closed.\n[B] When the bell rings, the valve shall be open.\n"), ["contradiction"]);
}

#[test]
fn a_deadline_without_an_origin_is_reported() {
    assert_eq!(codes_of_the_analysis("[A] The gateway shall respond within 2 seconds.\n"), ["UNRESOLVED_TEMPORAL_SCOPE"]);
    assert_eq!(codes_of_the_analysis("[A] The valve shall be closed within 5 seconds.\n"), ["UNRESOLVED_TEMPORAL_SCOPE"]);
    // An explicit origin, a trigger or a state scope gives the deadline its origin.
    assert!(codes_of_the_analysis("[A] The gateway shall respond within 2 seconds after the request arrives.\n").is_empty());
    assert!(codes_of_the_analysis("[A] When a request arrives, the gateway shall respond within 2 seconds.\n").is_empty());
    // A place is no deadline, and a duration measures its own action.
    assert!(codes_of_the_analysis("[A] Each name shall resolve within the current package.\n").is_empty());
    assert!(codes_of_the_analysis("[A] The pump shall run for 5 seconds.\n").is_empty());
    let report = fixture("[A] The gateway shall respond within 2 seconds.\n").trion(&["verify", "--json", "a.trion"]).json();
    assert_eq!(report["diagnostics"][0]["refs"][0]["id"], "A");
}

#[test]
fn a_state_around_a_trigger_is_sampled_once_and_the_obligation_stays() {
    let text = "[A] While the door is open, when the bell rings, the API shall stop.\n";
    let shape = shape(text, "A");
    assert_eq!(shape["activation"], serde_json::json!({"kind": "occurrence", "event": "Event(bell ring)", "unwanted": false, "gate": ["Val(door, open)"]}));
    assert_eq!(shape["lifetime"], serde_json::json!({"opens": "the trigger occurrence", "closes": "satisfaction", "gate_resampled": false}));
    let printed = model(text);
    assert!(printed.contains("gate sampled at the occurrence: Val(door, open)"), "{printed}");
    assert!(printed.contains("a later change of the gate does not close it"), "{printed}");
    // The door may close after the bell: the stop is still owed, so a ban on it conflicts.
    assert_eq!(codes(&format!("{text}[N] The API shall not stop.\n")), ["contradiction"]);
    // A stated cancellation closes the obligation.
    let cancelled = "[A] When the bell rings, the API shall sound the alarm until the operator acknowledges the alarm.\n";
    assert_eq!(self::shape(cancelled, "A")["lifetime"]["closes"], "satisfaction or Event(operator acknowledge alarm)");
}

#[test]
fn an_exception_of_a_triggered_response_is_read_at_activation() {
    let triggered = "[A] When the bell rings, the API shall stop unless the door is locked.\n";
    assert_eq!(shape(triggered, "A")["exception"], serde_json::json!({"condition": "Val(door, locked)", "sampled": "at activation"}));
    let untriggered = "[A] The API shall log each call unless the door is locked.\n";
    assert_eq!(shape(untriggered, "A")["exception"]["sampled"], "throughout the scope of the statement");
}

#[test]
fn an_activated_positive_action_completes_eventually() {
    let text = "[A] When the bell rings, the API shall stop.\n[B] When the bell rings, the API shall not start.\n[C] When the bell rings, the API may wait.\n[D] When the bell rings, the API shall sound the alarm until the operator acknowledges the alarm.\n";
    assert_eq!(shape(text, "A")["responses"][0]["liveness"], "eventually complete(API|stop)");
    assert_eq!(shape(text, "B")["responses"][0]["liveness"], Value::Null);
    assert_eq!(shape(text, "C")["responses"][0]["liveness"], Value::Null);
    assert_eq!(shape(text, "D")["responses"][0]["liveness"], "eventually complete(API|sound alarm) unless cancelled");
}

#[test]
fn a_deadline_measures_completion_from_the_activation() {
    let text = "[A] When a request arrives, the gateway shall respond within 2 seconds.\n";
    assert_eq!(shape(text, "A")["responses"][0]["deadline"], serde_json::json!({"bound": "within 2 seconds", "measures": "completion", "origin": {"kind": "activation"}}));
    assert!(model(text).contains("completion within 2 seconds measured from the activation"));
    let explicit = "[A] When a request arrives, the gateway shall respond within 2 seconds after the session opens.\n";
    assert_eq!(shape(explicit, "A")["responses"][0]["deadline"]["origin"], serde_json::json!({"kind": "explicit", "event": "Event(session open)"}));
    // The deadline is no part of the name of the action.
    assert!(model(text).contains("Act(gateway|respond)"), "{}", model(text));
}

#[test]
fn before_after_and_until_name_their_event_and_their_boundary() {
    let text = "[A] When the order ships, the API shall notify the customer before the payment clears.\n[B] When the order ships, the API shall bill the customer after the payment clears.\n[C] When the bell rings, the API shall hold the door until the door is locked.\n";
    let reference = |id: &str| shape(text, id)["responses"][0]["references"][0].clone();
    assert_eq!(reference("A"), serde_json::json!({"relation": "before", "related": "Event(payment clear)", "related_kind": "event", "boundary": "the response completes before the event begins"}));
    assert_eq!(reference("B")["boundary"], "the response starts after the event begins");
    assert_eq!(reference("C")["related_kind"], "state");
    assert_eq!(reference("C")["related"], "Val(door, locked)");
    assert!(model(text).contains("Act(API|notify customer)"), "{}", model(text));
}

#[test]
fn ordered_actions_have_a_start_and_a_completion() {
    let ordered = "[A] When the bell rings, the API shall perform the following actions in order:\n    stop the pump;\n    log the stop;\n";
    assert_eq!(shape(ordered, "A")["orders"], serde_json::json!([["complete(API|stop pump)", "start(API|log stop)"]]));
    assert!(model(ordered).contains("action API|stop pump: start(API|stop pump) then complete(API|stop pump)"));
    // A state has neither, so it cannot stand in an order.
    let state = "[A] When the bell rings, the API shall perform the following actions in order:\n    stop the pump;\n    be ready;\n";
    assert_eq!(codes_of_the_analysis(state), ["UNRESOLVED_TEMPORAL_SCOPE"]);
}

const FLOW: &str = "[F] When a result arrives, the checker shall follow this flow:\n    step inspect: inspect the result;\n    step accept: publish the result;\n    step fail: reject the result;\n    start inspect\n    choose after inspect:\n        when the result is valid -> accept\n        otherwise -> fail\n    finish accept\n    finish fail\n";

#[test]
fn a_flow_instance_has_one_occurrence_of_each_step_one_sampling_and_no_verdict() {
    let flow = &shape(FLOW, "F")["flows"][0];
    assert_eq!(flow["occurrences"], serde_json::json!([["inspect", 1], ["accept", 1], ["fail", 1]]));
    assert_eq!(flow["choices"][0], serde_json::json!({"after": "inspect", "instant": "completion of step inspect", "guards": ["Val(result, valid)"], "otherwise": true, "selects": "exactly one target"}));
    assert_eq!(flow["finishes"][1], serde_json::json!(["fail", "completion of the flow instance, with no verification verdict"]));
    // Both targets are ordered after the step of the choice.
    let orders = shape(FLOW, "F")["orders"].to_string();
    assert!(orders.contains("start(checker|publish result)") && orders.contains("start(checker|reject result)"), "{orders}");
    // A finish step named `fail` completes the instance and fails nothing.
    let report = fixture(FLOW).trion(&["verify", "--json", "a.trion"]).json();
    assert!(analysis_codes(&report).is_empty(), "{report}");
    assert_eq!(report["consistency"]["status"], "satisfiable");
}

#[test]
fn guards_are_judged_from_invariants_definitions_and_the_path_never_from_the_flow() {
    let flow = |arms: &str| format!("[STATUS] The result status is valid or invalid.\n[F] When a result arrives, the checker shall follow this flow:\n    step inspect: inspect the result;\n    step accept: publish the result;\n    step fail: reject the result;\n    start inspect\n    choose after inspect:\n{arms}    finish accept\n    finish fail\n");
    // The closed domain of the status covers the two guards without `otherwise`.
    let covered = flow("        when the result status is valid -> accept\n        when the result status is invalid -> fail\n");
    let report = fixture(&covered).trion(&["verify", "--json", "a.trion"]).json();
    assert!(analysis_codes(&report).is_empty(), "{report}");
    let obligation = &report["guards"][0];
    assert_eq!(obligation["statement"], "F");
    assert_eq!(obligation["instant"], "completion of step inspect");
    assert_eq!(obligation["covered"], "unsatisfiable");
    assert_eq!(obligation["exclusive"], "unsatisfiable");
    let premises: Vec<&str> = obligation["premises"].as_array().unwrap().iter().map(|p| p.as_str().unwrap()).collect();
    assert!(premises.contains(&"the closed domains of the guards"), "{premises:?}");
    assert!(premises.iter().all(|p| !p.contains("invariant F")), "the flow is no premise of its own obligation: {premises:?}");
    // Without the domain the same guards leave a gap.
    let open = covered.replace("[STATUS] The result status is valid or invalid.\n", "");
    assert_eq!(codes_of_the_analysis(&open), ["INCOMPLETE_FLOW_CHOICE"]);
    // An invariant of the package is a premise.
    let invariant = format!("[LEVEL] The level is at most 5.\n{}", flow("        when the level is at most 5 -> accept\n        when the level is greater than 5 -> fail\n"));
    let report = fixture(&invariant).trion(&["verify", "--json", "a.trion"]).json();
    assert!(report["guards"][0]["premises"].to_string().contains("invariant LEVEL"), "{report}");
}

#[test]
fn each_ears_pattern_gets_the_scope_and_timing_of_this_edition() {
    let text = "[UBIQUITOUS] The valve shall be closed.\n[STATE] While the door is open, the alarm shall sound.\n[EVENT] When the bell rings, the API shall stop.\n[OPTION] Where the device includes a cache, the device shall flush the cache.\n[UNWANTED] If the pump fails, then the API shall raise an alarm.\n[COMPLEX] While the door is open, when the bell rings, the API shall wait.\n";
    let kind = |id: &str| shape(text, id)["activation"]["kind"].as_str().unwrap().to_string();
    assert_eq!(kind("UBIQUITOUS"), "always");
    assert_eq!(kind("STATE"), "interval");
    assert_eq!(kind("EVENT"), "occurrence");
    assert_eq!(kind("OPTION"), "invocation");
    assert_eq!(shape(text, "OPTION")["configuration"].as_array().unwrap().len(), 1);
    assert_eq!(shape(text, "UNWANTED")["activation"]["unwanted"], true);
    assert_eq!(shape(text, "COMPLEX")["activation"]["gate"], serde_json::json!(["Val(door, open)"]));
}

#[test]
fn a_result_names_the_trace_length_it_holds_for() {
    let f = fixture("[A] When the bell rings, the API shall stop.\n");
    let report = f.trion(&["verify", "--json", "a.trion"]).json();
    assert_eq!(report["consistency"]["bounds"]["trace_length"], 3);
    let longer = f.trion(&["verify", "--json", "--trace-length", "5", "a.trion"]).json();
    assert_eq!(longer["consistency"]["bounds"]["trace_length"], 5);
    assert!(f.trion(&["verify", "a.trion"]).stdout.contains("bounds: traces of 3 moments"));
}
