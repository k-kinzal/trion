//! The proof obligations decided as `trioc` decides them: the reading of
//! the rest of the trace, the temporal forms at several lengths, the
//! checks, the examples and the choices over the unrolled formulas, and a
//! certificate that an independent checker accepts for every answer.

mod common;
#[allow(dead_code)]
#[path = "../../trion-checker/src/certificate.rs"]
mod checker;

use common::*;
use trion_verification::{analyze, proof_obligations, Analysis, Bounds, ObligationVerdict, Options};

fn at(moments: usize) -> Options {
    Options { bounds: Bounds { trace_length: moments, ..Bounds::default() }, ..Options::default() }
}

fn certified_at(src: &str, moments: usize) -> Analysis {
    proved(&set(src), &at(moments))
}

fn certified(src: &str) -> Analysis {
    certified_at(src, 3)
}

fn errors(analysis: &Analysis) -> Vec<String> {
    analysis.diagnostics.iter().filter(|d| d.severity == trion_language::Severity::Error && d.code != "ungrounded" && d.code != "UNSUPPORTED_SEMANTICS").map(|d| d.code.clone()).collect()
}

/// The verdict of each obligation, with every answer that it rests on
/// accepted by the checker; the number of answers.
fn all_accepted(src: &str, moments: usize) -> (Vec<(String, ObligationVerdict)>, usize) {
    let set = set(src);
    let analysis = analyze(&set, &at(moments));
    let stated = proof_obligations(&set, &analysis, moments);
    let inst = stated.instance(None);
    let mut verdicts = Vec::new();
    let mut answers = 0;
    for obligation in &stated.obligations {
        let decision = stated.decide(&inst, obligation);
        for asked in &decision.asked {
            if let Err(problem) = checker::check(&asked.formulas, &asked.answer) {
                panic!("the certificate of `{}` of {} is rejected: {problem}", asked.name, obligation.name);
            }
            answers += 1;
        }
        verdicts.push((obligation.name.clone(), decision.verdict));
    }
    (verdicts, answers)
}

fn verdict_of(verdicts: &[(String, ObligationVerdict)], name: &str) -> ObligationVerdict {
    verdicts.iter().find(|(n, _)| n == name).map(|(_, v)| *v).unwrap_or_else(|| panic!("no obligation {name}: {verdicts:?}"))
}

#[test]
fn a_permission_keeps_its_own_formula() {
    // A permission is not narrowed by a prohibition: where both apply they contradict.
    let both = certified("system user\n[P] The user may delete the message.\n[A] The room shall be archived.\n[N] While the room is archived, the user shall not delete the message.\n");
    assert_eq!(errors(&both), ["contradiction"]);
    assert!(both.model.priorities.iter().all(|p| p.kind != "narrows"));
    let permission = both.model.constraints.iter().find(|c| c.refs.first().is_some_and(|r| r.id == "P")).unwrap();
    assert_eq!(permission.assume, trion_solver::Formula::True);
    // The exception written into the permission removes the conflict.
    let excepted = "system user\n[P] The user may delete the message, unless the room is archived.\n[A] The room shall be archived.\n[N] While the room is archived, the user shall not delete the message.\n";
    assert!(errors(&certified(excepted)).is_empty(), "{:?}", certified(excepted).diagnostics);
    assert_eq!(consistency(excepted, &at(3)), ObligationVerdict::Proved);
}

#[test]
fn a_conflict_under_a_condition_of_the_environment_is_a_contradiction() {
    // The user is the environment's: the system cannot keep the user from
    // leaving, and then the two statements cannot both be kept.
    let conditional = certified("[A] When the user leaves, the API shall return foo.\n[B] When the user leaves, the API shall not return foo.\n");
    assert_eq!(errors(&conditional), ["contradiction"]);
    let mut named: Vec<&str> = conditional.diagnostics.iter().find(|d| d.code == "contradiction").unwrap().refs.iter().map(|r| r.id.as_str()).collect();
    named.sort();
    assert_eq!(named, ["A", "B"]);
    // A conflict that needs a recommendation is no inconsistency.
    let advised = "[A] The API should return foo.\n[B] The API shall not return foo.\n";
    assert_eq!(errors(&certified(advised)), ["recommendation-violation"]);
    assert_eq!(consistency(advised, &at(3)), ObligationVerdict::Proved);
    // A plain refutation names the two statements and not the third.
    let plain = certified("[A] The API shall return foo.\n[B] The API shall not return foo.\n[C] The API shall log the call.\n");
    assert_eq!(errors(&plain), ["contradiction"]);
    assert!(plain.diagnostics.iter().all(|d| d.refs.iter().all(|r| r.id != "C")), "{:?}", plain.diagnostics);
}

const SWITCH: &str = "[A] When the switch is active, the switch shall not be active.\n[B] When the switch is not active, the switch shall be active.\n";

#[test]
fn the_alternating_switch_is_consistent_at_every_length() {
    // The trace active, not active, active, … satisfies both statements:
    // a required state holds at the next moment.
    for moments in 2..=6 {
        let analysis = certified_at(SWITCH, moments);
        assert!(errors(&analysis).is_empty(), "at {moments} moments: {:?}", analysis.diagnostics);
        let (verdicts, _) = all_accepted(SWITCH, moments);
        assert!(verdicts.iter().all(|(_, v)| *v == ObligationVerdict::Proved), "at {moments} moments: {verdicts:?}");
    }
    // The same statements with one position for a trigger and its response would contradict.
    let collapsed = certified("[A] While the switch is active, the switch shall not be active.\n[B] The switch shall be active.\n");
    assert!(errors(&collapsed).contains(&"contradiction".to_string()));
}

/// Statements of each temporal form with a periodic trace that satisfies them.
const PERIODIC: [(&str, &str); 10] = [
    // door open, then closed, then open, …; the bell rings at each moment.
    ("an activation by an occurrence", "[A] When the door opens, the bell shall ring.\n[B] When the door closes, the bell shall ring.\n"),
    // closed after open and open after closed, one moment each.
    ("a state required by an occurrence", "[A] When the door is open, the door shall become closed.\n[B] When the door is closed, the door shall become open.\n"),
    // each invocation of stop completes at the next moment.
    ("an activation by an invocation", "[A] The API shall stop.\n[B] The API shall log the call.\n"),
    // the lamp is lit at exactly the moments at which the door is open.
    ("throughout an interval", "[A] While the door is open, the lamp shall be lit.\n[B] While the door is closed, the lamp shall not be lit.\n[C] When the door is open, the door shall become closed.\n[D] When the door is closed, the door shall become open.\n"),
    // the room is archived at every moment.
    ("always", "[A] The room shall be archived.\n[B] The room is archived or active.\n"),
    // a request at each third moment, a response two seconds later.
    ("a deadline from its activation", "[A] When a request arrives, the gateway shall respond within 2 seconds.\n[B] When a request arrives, the gateway shall not respond within 1 second.\n"),
    // the gate opens one second after each retry.
    ("a deadline from a named origin", "[A] When a retry occurs, the gate shall open within 5 seconds of the last retry.\n"),
    // the valve closes, then the pump starts, in each period. The valve and
    // the pump are the system's: an order before an event of the
    // environment is unrealizable, and after one that never comes it is
    // never kept.
    ("before and after", "system controller, pump, valve\n[A] When the tank is full, the controller shall close the valve before the pump starts.\n[B] When the tank is full, the controller shall start the pump after the valve closes.\n"),
    // the siren sounds at each moment before the reset of its period. (A
    // prohibition after a reset would hold for the rest of the trace, and
    // the next trigger would then require the siren that it forbids.)
    ("until", "[A] When the alarm triggers, the siren shall sound until the operator resets the alarm.\n[C] While the alarm triggers, no operator resets the alarm.\n"),
    // the door is locked at the moments at which the key is absent.
    ("unless", "system door\n[A] When the door closes, the door shall become locked, unless the key is present.\n[B] While the key is present, the door shall not be locked.\n"),
];

#[test]
fn statements_that_a_periodic_trace_satisfies_are_consistent_at_every_length() {
    for (form, source) in PERIODIC {
        for moments in 2..=5 {
            let analysis = certified_at(source, moments);
            let relevant: Vec<String> = errors(&analysis).into_iter().filter(|c| c != "UNRESOLVED_TEMPORAL_SCOPE").collect();
            assert!(relevant.is_empty(), "{form} at {moments} moments: {:?}", analysis.diagnostics);
            let (verdicts, answers) = all_accepted(source, moments);
            assert_eq!(verdict_of(&verdicts, "consistency"), ObligationVerdict::Proved, "{form} at {moments} moments");
            assert!(answers > 0);
        }
    }
}

#[test]
fn a_conflict_within_the_moments_is_still_found() {
    // A response and a prohibition after one trigger.
    assert_eq!(errors(&certified("[A] When the door opens, the alarm shall sound.\n[B] When the door opens, the alarm shall not sound.\n")), ["contradiction"]);
    // A chain through the completion of an action, whichever moment the action completes at.
    let chain = "[A] When the door opens, the controller shall stop the motor.\n[B] When the controller stops the motor, the alarm shall sound.\n[C] When the door opens, the alarm shall not sound.\n";
    for moments in 2..=5 {
        assert_eq!(errors(&certified_at(chain, moments)), ["contradiction"], "at {moments} moments");
    }
    // Two states after one trigger exclude each other at the next moment.
    assert_eq!(errors(&certified("[K] The door is open, closed or locked.\n[A] When the bell rings, the door shall become closed.\n[B] When the bell rings, the door shall become locked.\n")), ["contradiction"]);
    // A state under a condition that holds throughout, against an obligation:
    // the obligation can be met at a moment at which the condition does not
    // hold, and not in the situation in which it holds throughout.
    assert_eq!(errors(&certified("environment room\n[A] While the room is archived, the API shall not store the message.\n[B] The API shall store the message.\n")), ["contradiction"]);
}

const CHECKED: &str = "[T]\nWhen the door opens, the controller shall perform the following actions in order:\n    stop the motor;\n    sound the alarm;\n\n[F]\nWhen the door opens, the controller shall follow this flow:\n    step stop: stop the motor;\n    step sound: sound the alarm;\n\n    start stop\n    stop -> sound\n    finish sound\n\ncheck SAME:\n    relation equivalent\n    left [T]\n    right [F]\n    using definitions\n";

#[test]
fn a_check_is_decided_over_the_unrolled_formulas_at_the_bounds_of_the_run() {
    for moments in [2, 3, 5] {
        let (verdicts, _) = all_accepted(CHECKED, moments);
        assert_eq!(verdict_of(&verdicts, "check/SAME"), ObligationVerdict::Proved, "at {moments} moments");
    }
    // Two sides that differ are refuted.
    let (verdicts, _) = all_accepted(&CHECKED.replace("step sound: sound the alarm;", "step sound: sound the horn;"), 3);
    assert_eq!(verdict_of(&verdicts, "check/SAME"), ObligationVerdict::Refuted);
}

#[test]
fn a_comparison_a_choice_and_a_consistency_example_are_decided_over_the_trace() {
    let source = "[BASE]\nWhen the door opens, the alarm shall sound.\n\n[SAME]\nWhen the door opens, the alarm shall sound.\n\n[MORE]\nWhen the door opens, the lamp shall flash.\n\n[AGAINST]\nWhen the door opens, the alarm shall not sound.\n\nexample REDUNDANT:\n    kind comparison\n    base [BASE]\n    candidate [SAME]\n    expect redundant\n\nexample EXTENSION:\n    kind comparison\n    base [BASE]\n    candidate [MORE]\n    expect extension\n\nexample CONFLICT:\n    kind comparison\n    base [BASE]\n    candidate [AGAINST]\n    expect conflict\n\nexample SWITCH:\n    kind consistency\n    input \"When the switch is active, the switch shall not be active.\"\n    expect consistent\n\nexample BOTH:\n    kind consistency\n    input \"The API shall stop. The API shall not stop.\"\n    expect inconsistent\n";
    let analysis = certified(source);
    let failed: Vec<_> = analysis.diagnostics.iter().filter(|d| d.code.starts_with("example")).collect();
    assert!(failed.is_empty(), "{failed:?}");
    let (verdicts, _) = all_accepted(source, 3);
    for name in ["REDUNDANT", "EXTENSION", "CONFLICT", "SWITCH", "BOTH"] {
        assert_eq!(verdict_of(&verdicts, &format!("example/{name}")), ObligationVerdict::Proved, "{name}");
    }
    // The guards of a choice exclude each other and cover every case.
    let flow = "[STATUS] The result status is valid or invalid.\n[F] When a result arrives, the checker shall follow this flow:\n    step inspect: inspect the result;\n    step accept: publish the result;\n    step fail: reject the result;\n    start inspect\n    choose after inspect:\n        when the result status is valid -> accept\n        when the result status is invalid -> fail\n    finish accept\n    finish fail\n";
    let analysis = certified(flow);
    assert!(errors(&analysis).is_empty(), "{:?}", analysis.diagnostics);
    let (verdicts, _) = all_accepted(flow, 3);
    let choices: Vec<_> = verdicts.iter().filter(|(n, _)| n.starts_with("choice/")).collect();
    assert!(choices.len() >= 2 && choices.iter().all(|(_, v)| *v == ObligationVerdict::Proved), "{verdicts:?}");
}

#[test]
fn a_condition_of_the_environment_that_the_descriptions_exclude_leaves_its_statement_no_environment() {
    // The door is the environment's, and its condition is part of the
    // assumption of [A]: the descriptions allow no door that is ajar, so no
    // environment meets the assumption. Every system keeps [A] (consistency
    // holds), and the document is incompatible.
    let excluded = "[D]\nThe door is open or closed.\n\n[A]\nWhile the door is ajar, the lamp shall be lit.\n";
    assert_eq!(errors(&certified(excluded)), ["incompatible"]);
    assert_eq!(consistency(excluded, &at(3)), ObligationVerdict::Proved);
}

#[test]
fn the_situations_are_decided_without_listing_them() {
    // Both conditions can hold together, and then the two statements cannot be kept.
    for text in ["[J1]\nWhen a user sends a message, the API shall store the message.\n\n[J2]\nWhile the room is archived, the API shall not store the message.\n", "environment size\n[A]\nWhen the size is at least 100, the API shall stop.\n\n[B]\nWhen the size is at most 100, the API shall not stop.\n"] {
        let conflict = certified(text);
        assert_eq!(errors(&conflict), ["contradiction"], "{text}");
        assert_eq!(conflict.diagnostics.iter().find(|d| d.code == "contradiction").unwrap().refs.len(), 2);
    }
    // No conflict: every situation has a response.
    let kept = "[K1]\nWhen a user sends a message, the API shall store the message.\n\n[K2]\nWhile the room is archived, the API shall log the message.\n";
    assert!(errors(&certified(kept)).is_empty());
    assert_eq!(consistency(kept, &at(3)), ObligationVerdict::Proved);
    // Statements that share no response are answered apart: twelve states
    // with two values each have 4096 situations, and none is listed.
    let apart: String = ["door", "lamp", "valve", "pump", "gate", "fan", "bell", "horn", "lock", "vent", "hatch", "relay"].iter().enumerate().map(|(i, part)| format!("[K{i}]\nThe {part} is open or closed.\n[A{i}]\nWhile the {part} is open, the API shall raise the {part} flag.\n[B{i}]\nWhile the {part} is closed, the API shall clear the {part} flag.\n")).collect();
    assert_eq!(consistency(&apart, &at(3)), ObligationVerdict::Proved);
    // A statement without normative force that excludes the situation at
    // one moment does not exclude it over the trace: the user sends while
    // the room is open, the room is archived at the next moment, and the
    // message can then be neither stored nor left unstored.
    let excluded = "[J1]\nWhen a user sends a message, the API shall store the message.\n\n[J2]\nWhile the room is archived, the API shall not store the message.\n\n[J3]\nWhile the room is archived, no user sends a message.\n";
    assert_eq!(errors(&certified(excluded)), ["contradiction"]);
    // A room that is never archived settles it.
    let settled = "[J1]\nWhen a user sends a message, the API shall store the message.\n\n[J2]\nWhile the room is archived, the API shall not store the message.\n\n[J3]\nThe room is never archived.\n";
    assert!(errors(&certified(settled)).is_empty(), "{:?}", errors(&certified(settled)));
    assert_eq!(consistency(settled, &at(3)), ObligationVerdict::Proved);
}

#[test]
fn an_assumption_in_a_shared_condition_block_is_distributed_to_that_block_only() {
    // [D] describes the environment inside the block: it is the assumption
    // of the statements of the block, and of no other (AGENTS.md, rule 3).
    let head = "system API\nenvironment door, room\nWhile the door is open:\n    [D] The room is never archived.\n    [G] The API shall log the message.\n";
    // Outside the block [D] assumes nothing, and the two statements meet
    // where the door is open and the room is archived.
    let outside = format!("{head}[B1] While the door is open and the room is archived, the API shall store the message.\n[B2] While the door is open and the room is archived, the API shall not store the message.\n");
    assert_eq!(errors(&certified(&outside)), ["contradiction"]);
    assert_eq!(consistency(&outside, &at(3)), ObligationVerdict::Refuted);
    // Inside the block [D] is their assumption: the room is never archived
    // where they apply, and every system keeps them.
    let inside = format!("{head}    [B1] While the room is archived, the API shall store the message.\n    [B2] While the room is archived, the API shall not store the message.\n");
    assert!(errors(&certified(&inside)).is_empty(), "{:?}", errors(&certified(&inside)));
    assert_eq!(consistency(&inside, &at(3)), ObligationVerdict::Proved);
    // Written outside every block, the description is the assumption of the
    // whole document.
    let document = "system API\nenvironment door, room\n[D] While the door is open, the room is never archived.\n[B1] While the door is open and the room is archived, the API shall store the message.\n[B2] While the door is open and the room is archived, the API shall not store the message.\n";
    assert_eq!(consistency(document, &at(3)), ObligationVerdict::Proved);
}
