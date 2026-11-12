//! The engine half of the proof obligations: relations applied in the
//! model, the status, the greatest weight, one semantics for every
//! question, the reading of the rest of the trace, and the certificates of
//! the inventory.

mod common;
#[path = "common/checker.rs"]
mod checker;

use common::*;
use trion_verification::proof::{CheckResult, ComparisonResult, ConditionOutcome, Coverage, Exclusivity, Proof, Question, StatusOutcome, CLAIM_KINDS};
use trion_solver::{Formula, Status};
use trion_verification::{analyze, Analysis, Bounds, Options};

fn certified_at(src: &str, moments: usize) -> Analysis {
    analyze(&set(src), &Options { bounds: Bounds { trace_length: moments, ..Bounds::default() }, certificates: true, ..Options::default() })
}

fn certified(src: &str) -> Analysis {
    certified_at(src, 3)
}

fn errors(analysis: &Analysis) -> Vec<String> {
    analysis.diagnostics.iter().filter(|d| d.severity == trion_language::Severity::Error && d.code != "ungrounded" && d.code != "UNSUPPORTED_SEMANTICS").map(|d| d.code.clone()).collect()
}

fn accepted(pool: &[Formula], question: &Question, wanted: Status) {
    assert_eq!(question.status(), wanted);
    if let Err(problem) = checker::check(&question.formulas(pool), &question.answer) {
        panic!("a certificate is rejected: {problem}");
    }
}

/// Every question of a proof carries a certificate that the checker accepts.
fn all_accepted(proof: &Proof) -> usize {
    let questions = proof.questions();
    for question in &questions {
        if let Err(problem) = checker::check(&question.formulas(&proof.pool), &question.answer) {
            panic!("a certificate is rejected: {problem}");
        }
    }
    for relation in &proof.relations {
        for query in &relation.queries {
            if let Err(problem) = checker::check(&query.all(), &query.answer) {
                panic!("the certificate of a question of the reader is rejected: {problem}");
            }
        }
    }
    for example in &proof.examples {
        let questions: Vec<&Question> = match &example.status {
            StatusOutcome::Satisfiable { witness } => vec![witness],
            StatusOutcome::Unsatisfiable { refutation, minimal, .. } => std::iter::once(refutation).chain(minimal.iter().flatten()).collect(),
            StatusOutcome::Unknown => Vec::new(),
        };
        for question in questions {
            if let Err(problem) = checker::check(&question.formulas(&example.pool), &question.answer) {
                panic!("the certificate of an example is rejected: {problem}");
            }
        }
    }
    questions.len()
}

const PERMISSION: &str = "[P] The user may delete the message.\n[A] The room shall be archived.\n[N] While the room is archived, the user shall not delete the message.\n";

#[test]
fn a_general_permission_is_narrowed_in_its_own_formula() {
    let analysis = certified(PERMISSION);
    assert!(errors(&analysis).is_empty(), "{:?}", analysis.diagnostics);
    assert_eq!(analysis.consistency.verdict, "consistent");
    // The pair without the second statement is consistent as well.
    let pair = certified("[P] The user may delete the message.\n[N] While the room is archived, the user shall not delete the message.\n");
    assert!(errors(&pair).is_empty(), "{:?}", pair.diagnostics);
    // The permission keeps its entry, and its formula says where it applies.
    let proof = analysis.proof.as_ref().unwrap();
    let permission = proof.entries.iter().find(|e| e.statement.as_ref().is_some_and(|s| s.id == "P")).unwrap();
    assert_eq!(permission.kind.as_str(), "permission");
    assert_eq!(permission.local_assume, Formula::True);
    assert_eq!(permission.condition, None);
    let narrowed = analysis.model.constraints.iter().find(|c| c.refs.first().is_some_and(|r| r.id == "P")).unwrap();
    assert_eq!(narrowed.assume.to_string(), "¬Val(room, archived)");
    // The relation names both statements and the questions that establish it.
    let relation = proof.relations.iter().find(|r| r.kind == "narrows").unwrap();
    assert_eq!((relation.subject.id.as_str(), relation.rests_on[0].id.as_str()), ("P", "N"));
    assert!(!relation.queries.is_empty());
    // The status question holds every entry that is no recommendation.
    let StatusOutcome::Satisfiable { witness } = &proof.status else { panic!("{:?}", proof.status.status()) };
    assert!(proof.entries.iter().all(|e| witness.query.contains(&e.formula)));
    // A prohibition without a condition still removes every admissible response.
    assert_eq!(errors(&certified("[P] The user may delete the message.\n[N] The user shall not delete the message.\n")), ["contradiction"]);
    // A prohibition under the very condition of the permission is no narrower one.
    assert_eq!(errors(&certified("[P] While the room is archived, the user may delete the message.\n[N] While the room is archived, the user shall not delete the message.\n")), ["contradiction"]);
}

#[test]
fn an_overridden_statement_and_a_default_stay_in_every_query() {
    let overridden = "[D1]\nThe door shall be open.\n\n[D2]\nWhile the alarm is active, the door shall be closed.\n    overrides [D1]\n";
    let analysis = certified(overridden);
    assert!(errors(&analysis).is_empty(), "{:?}", analysis.diagnostics);
    let proof = analysis.proof.as_ref().unwrap();
    assert!(proof.relations.iter().any(|r| r.kind == "overrides" && r.subject.id == "D1"));
    // The statement that yields has no condition of its own: the relation narrows its formula only.
    let loser = proof.entries.iter().find(|e| e.statement.as_ref().is_some_and(|s| s.id == "D1")).unwrap();
    assert_eq!((loser.local_assume.clone(), loser.condition), (Formula::True, None));
    for claim in &proof.conditions {
        let ConditionOutcome::NoConflict { witness } = &claim.outcome else { panic!("{}", claim.outcome.name()) };
        assert!(proof.entries.iter().all(|e| witness.query.contains(&e.formula)));
    }
    // It still applies wherever the other does not.
    let still = format!("{overridden}\n[D7]\nWhile the alarm is idle, the door shall be closed.\n\n[A]\nThe alarm is active or idle.\n");
    assert_eq!(errors(&certified(&still)), ["contradiction"]);
    // A default that yields to a statement whose condition always holds is no conflict.
    let default = "[D]\nThe user shall delete the message.\n    default\n\n[A]\nThe room shall be archived.\n\n[W]\nWhile the room is archived, the user shall not delete the message.\n";
    let analysis = certified(default);
    assert!(errors(&analysis).is_empty(), "{:?}", analysis.diagnostics);
    assert!(analysis.proof.as_ref().unwrap().relations.iter().any(|r| r.kind == "default" && r.subject.id == "D" && !r.queries.is_empty()));
}

#[test]
fn every_answer_that_the_reader_uses_has_a_certificate() {
    for source in [PERMISSION, "[D]\nThe user shall delete the message.\n    default\n\n[W]\nWhile the room is archived, the user shall not delete the message.\n"] {
        let analysis = certified(source);
        let queries: Vec<_> = analysis.model.priorities.iter().flat_map(|p| &p.queries).collect();
        assert!(!queries.is_empty());
        for query in queries {
            assert_ne!(query.answer.status, Status::Unknown);
            if let Err(problem) = checker::check(&query.all(), &query.answer) {
                panic!("{}: {problem}", query.purpose);
            }
        }
    }
}

#[test]
fn only_an_unconditional_refutation_of_hard_constraints_is_unsatisfiable() {
    // A conflict under a condition leaves the hard constraints satisfiable,
    // wherever the user never leaves, and the specification inconsistent.
    let conditional = certified("[A] When the user leaves, the API shall return foo.\n[B] When the user leaves, the API shall not return foo.\n");
    assert_eq!(errors(&conditional), ["contradiction"]);
    assert_eq!(conditional.consistency.status, Status::Satisfiable);
    assert_eq!(conditional.consistency.verdict, "inconsistent");
    assert!(conditional.conflicts[0].condition.is_some());
    let proof = conditional.proof.as_ref().unwrap();
    assert_eq!(proof.status.status(), Status::Satisfiable);
    let conflict = proof.conditions.iter().find_map(|c| match &c.outcome {
        ConditionOutcome::Conflict { reachable, members, refutation, minimal } => Some((reachable, members, refutation, minimal)),
        _ => None,
    });
    let (reachable, members, refutation, minimal) = conflict.expect("a conflict under a condition");
    accepted(&proof.pool, reachable, Status::Satisfiable);
    accepted(&proof.pool, refutation, Status::Unsatisfiable);
    assert_eq!(members.len(), 2);
    assert_eq!(minimal.as_ref().map(Vec::len), Some(2));
    // A conflict that needs a recommendation is no inconsistency either.
    let advised = certified("[A] The API should return foo.\n[B] The API shall not return foo.\n");
    assert_eq!(errors(&advised), ["recommendation-violation"]);
    assert_eq!(advised.consistency.status, Status::Satisfiable);
    assert_eq!(advised.consistency.verdict, "consistent");
    // A refutation with no condition forced is one.
    let plain = certified("[A] The API shall return foo.\n[B] The API shall not return foo.\n[C] The API shall log the call.\n");
    assert_eq!(plain.consistency.status, Status::Unsatisfiable);
    let proof = plain.proof.as_ref().unwrap();
    let StatusOutcome::Unsatisfiable { members, refutation, minimal } = &proof.status else { panic!() };
    assert_eq!(members.len(), 2);
    accepted(&proof.pool, refutation, Status::Unsatisfiable);
    // The set is called minimal: without either member the query has a witness.
    for witness in minimal.as_ref().expect("a minimal set") {
        accepted(&proof.pool, witness, Status::Satisfiable);
    }
    // A condition that cannot occur in any environment is told apart.
    let never = certified("[K] The mode is enabled or disabled.\n[A] While the mode is enabled, when the mode is disabled, the API shall stop.\n");
    let proof = never.proof.as_ref().unwrap();
    assert!(proof.conditions.iter().any(|c| matches!(c.outcome, ConditionOutcome::Unreachable { .. })), "{:?}", proof.conditions.iter().map(|c| c.outcome.name()).collect::<Vec<_>>());
}

const SWITCH: &str = "[A] When the switch is active, the switch shall not be active.\n[B] When the switch is not active, the switch shall be active.\n";

#[test]
fn the_alternating_switch_is_consistent_at_every_length() {
    // The trace active, not active, active, … satisfies both statements:
    // a required state holds at the next moment.
    for moments in 2..=6 {
        let analysis = certified_at(SWITCH, moments);
        assert!(errors(&analysis).is_empty(), "at {moments} moments: {:?}", analysis.diagnostics);
        assert_eq!(analysis.consistency.status, Status::Satisfiable, "at {moments} moments");
        let proof = analysis.proof.as_ref().unwrap();
        assert_eq!(proof.bounds.moments, moments);
        assert!(proof.conditions.iter().all(|c| matches!(c.outcome, ConditionOutcome::NoConflict { .. })));
    }
    // The same statements with one position for a trigger and its response would contradict.
    let collapsed = certified("[A] While the switch is active, the switch shall not be active.\n[B] The switch shall be active.\n");
    assert!(errors(&collapsed).contains(&"contradiction".to_string()));
    assert_eq!(collapsed.consistency.status, Status::Unsatisfiable);
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
    // the valve closes, then the pump starts, in each period.
    ("before and after", "[A] When the tank is full, the controller shall close the valve before the pump starts.\n[B] When the tank is full, the controller shall start the pump after the valve closes.\n"),
    // the siren sounds at each moment before the reset of its period.
    ("until", "[A] When the alarm triggers, the siren shall sound until the operator resets the alarm.\n[B] When the operator resets the alarm, the siren shall not sound.\n[C] While the alarm triggers, no operator resets the alarm.\n"),
    // the door is locked at the moments at which the key is absent.
    ("unless", "[A] When the door closes, the door shall become locked, unless the key is present.\n[B] While the key is present, the door shall not be locked.\n"),
];

#[test]
fn statements_that_a_periodic_trace_satisfies_are_consistent_at_every_length() {
    for (form, source) in PERIODIC {
        for moments in 2..=5 {
            let analysis = certified_at(source, moments);
            let relevant: Vec<String> = errors(&analysis).into_iter().filter(|c| c != "UNRESOLVED_TEMPORAL_SCOPE").collect();
            assert!(relevant.is_empty(), "{form} at {moments} moments: {:?}", analysis.diagnostics);
            assert_eq!(analysis.consistency.status, Status::Satisfiable, "{form} at {moments} moments");
            let proof = analysis.proof.as_ref().unwrap();
            assert!(proof.conditions.iter().all(|c| matches!(c.outcome, ConditionOutcome::NoConflict { .. })), "{form} at {moments} moments: {:?}", proof.conditions.iter().map(|c| c.outcome.name()).collect::<Vec<_>>());
            all_accepted(proof);
        }
        // The claim is printed with each result.
        let analysis = certified(source);
        assert!(analysis.consistency.assumptions.iter().any(|a| a.starts_with("the abstraction claim")));
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
    let throughout = certified("[A] While the room is archived, the API shall not store the message.\n[B] The API shall store the message.\n");
    assert_eq!(errors(&throughout), ["contradiction"]);
    assert_eq!(throughout.consistency.status, Status::Satisfiable);
}

const CHECKED: &str = "[T]\nWhen the door opens, the controller shall perform the following actions in order:\n    stop the motor;\n    sound the alarm;\n\n[F]\nWhen the door opens, the controller shall follow this flow:\n    step stop: stop the motor;\n    step sound: sound the alarm;\n\n    start stop\n    stop -> sound\n    finish sound\n\ncheck SAME:\n    relation equivalent\n    left [T]\n    right [F]\n    using definitions\n";

#[test]
fn a_check_is_decided_over_the_unrolled_formulas_at_the_bounds_of_the_run() {
    for moments in [2, 3, 5] {
        let analysis = certified_at(CHECKED, moments);
        assert_eq!(analysis.checks.iter().map(|c| c.result.as_str()).collect::<Vec<_>>(), ["proved"], "at {moments} moments: {:?}", analysis.diagnostics);
        let proof = analysis.proof.as_ref().unwrap();
        let claim = &proof.checks[0];
        assert_eq!((claim.environment.kind.as_str(), claim.environment.bounds.moments), ("check", moments));
        let CheckResult::Proved { environment, forward, backward } = &claim.result else { panic!("{}", claim.result.name()) };
        accepted(&proof.pool, environment, Status::Satisfiable);
        // One refutation for each formula of the other side.
        assert_eq!((forward.len(), backward.len()), (claim.not_right.len(), claim.not_left.len()));
        for question in forward.iter().chain(backward) {
            accepted(&proof.pool, question, Status::Unsatisfiable);
        }
        // The formulas speak of moments: the last one is the rest of the trace.
        let text: String = claim.left.iter().map(|&f| proof.pool[f].to_string()).collect();
        assert!(text.contains("@0") && text.contains(&format!("@{moments}")) && !text.contains(&format!("@{}", moments + 1)), "{text}");
    }
    // Two sides that differ are refuted with a witness of the difference.
    let differ = certified(&CHECKED.replace("step sound: sound the alarm;", "step sound: sound the horn;"));
    let proof = differ.proof.as_ref().unwrap();
    let CheckResult::Refuted { witness } = &proof.checks[0].result else { panic!("{}", proof.checks[0].result.name()) };
    accepted(&proof.pool, witness, Status::Satisfiable);
}

#[test]
fn a_comparison_a_choice_and_a_consistency_example_are_decided_over_the_trace() {
    let source = "[BASE]\nWhen the door opens, the alarm shall sound.\n\n[SAME]\nWhen the door opens, the alarm shall sound.\n\n[MORE]\nWhen the door opens, the lamp shall flash.\n\n[AGAINST]\nWhen the door opens, the alarm shall not sound.\n\nexample REDUNDANT:\n    kind comparison\n    base [BASE]\n    candidate [SAME]\n    expect redundant\n\nexample EXTENSION:\n    kind comparison\n    base [BASE]\n    candidate [MORE]\n    expect extension\n\nexample CONFLICT:\n    kind comparison\n    base [BASE]\n    candidate [AGAINST]\n    expect conflict\n\nexample SWITCH:\n    kind consistency\n    input \"When the switch is active, the switch shall not be active.\"\n    expect consistent\n\nexample BOTH:\n    kind consistency\n    input \"The API shall stop. The API shall not stop.\"\n    expect inconsistent\n";
    let analysis = certified(source);
    let failed: Vec<_> = analysis.diagnostics.iter().filter(|d| d.code.starts_with("example")).collect();
    assert!(failed.is_empty(), "{failed:?}");
    let proof = analysis.proof.as_ref().unwrap();
    let by_name = |name: &str| proof.comparisons.iter().find(|c| c.environment.name == name).unwrap();
    let ComparisonResult::Redundant { base, refutations } = &by_name("REDUNDANT").result else { panic!() };
    accepted(&proof.pool, base, Status::Satisfiable);
    assert!(!refutations.is_empty());
    refutations.iter().for_each(|q| accepted(&proof.pool, q, Status::Unsatisfiable));
    let ComparisonResult::Extension { with, without } = &by_name("EXTENSION").result else { panic!() };
    accepted(&proof.pool, with, Status::Satisfiable);
    accepted(&proof.pool, without, Status::Satisfiable);
    let ComparisonResult::Conflict { base, refutation } = &by_name("CONFLICT").result else { panic!() };
    accepted(&proof.pool, base, Status::Satisfiable);
    accepted(&proof.pool, refutation, Status::Unsatisfiable);
    assert!(proof.comparisons.iter().all(|c| c.environment.bounds.moments == 3 && c.expected.is_some()));
    // A consistency example has the rows of the status in its own environment.
    let example = |name: &str| proof.examples.iter().find(|e| e.name == name).unwrap();
    assert_eq!((example("SWITCH").status.status(), example("BOTH").status.status()), (Status::Satisfiable, Status::Unsatisfiable));
    assert!(example("SWITCH").pool.iter().any(|f| f.to_string().contains("@1")));
    all_accepted(proof);
    // The guards of a choice are read at one moment of the trace.
    let flow = "[STATUS] The result status is valid or invalid.\n[F] When a result arrives, the checker shall follow this flow:\n    step inspect: inspect the result;\n    step accept: publish the result;\n    step fail: reject the result;\n    start inspect\n    choose after inspect:\n        when the result status is valid -> accept\n        when the result status is invalid -> fail\n    finish accept\n    finish fail\n";
    let analysis = certified(flow);
    let proof = analysis.proof.as_ref().unwrap();
    assert_eq!(proof.choices.len(), 1, "{:?}", analysis.diagnostics);
    let choice = &proof.choices[0];
    let Exclusivity::Exclusive { refutations } = &choice.exclusive else { panic!() };
    refutations.iter().for_each(|q| accepted(&proof.pool, q, Status::Unsatisfiable));
    let Some(Coverage::Covered { refutation }) = &choice.covered else { panic!() };
    accepted(&proof.pool, refutation, Status::Unsatisfiable);
    assert!(choice.guards.iter().all(|&g| proof.pool[g].to_string().contains("@0")));
}

#[test]
fn a_satisfiable_result_has_an_outcome_for_every_question_with_its_certificates() {
    let source = "[K]\nThe room is active or archived.\n\n[A]\nWhile the room is archived, the API shall not store the message.\n\n[B]\nWhen a user sends a message, the API shall store the message, unless the room is archived.\n\n[C]\nWhen the size is at least 100, the API should compress the message.\n\n[D]\nThe timeout shall be less than the retry interval.\n\n[E]\nThe retry interval shall be at most 5 seconds.\n";
    let analysis = certified(source);
    assert!(errors(&analysis).is_empty(), "{:?}", analysis.diagnostics);
    let proof = analysis.proof.as_ref().unwrap();
    assert_eq!(proof.status.status(), Status::Satisfiable);
    // One outcome for the condition of each entry that has one, a recommendation as a hard constraint.
    let conditional: Vec<usize> = proof.entries.iter().enumerate().filter(|(_, e)| e.condition.is_some()).map(|(n, _)| n).collect();
    assert_eq!(proof.conditions.iter().map(|c| c.entry).collect::<Vec<_>>(), conditional);
    assert!(conditional.len() >= 3);
    for claim in &proof.conditions {
        let ConditionOutcome::NoConflict { witness } = &claim.outcome else { panic!("{}", claim.outcome.name()) };
        let entry = &proof.entries[claim.entry];
        assert!(witness.query.contains(&entry.formula) && witness.query.contains(&entry.condition.unwrap()));
        // No query leaves an entry out, and a recommendation is checked under its own condition.
        assert!(proof.entries.iter().all(|e| witness.query.contains(&e.formula)));
        assert!(proof.background.iter().all(|b| witness.query.contains(b)));
    }
    let recommendations = proof.recommendations.as_ref().unwrap();
    assert!(recommendations.dropped.is_empty());
    assert!(all_accepted(proof) >= 2 + conditional.len());
    // Each entry has its local reading and its formula over the trace.
    assert!(proof.entries.iter().all(|e| e.statement.is_some() && e.temporal.is_some() && proof.pool[e.formula].to_string().contains('@') || e.kind.as_str() == "hard"));
    assert_eq!(proof.bounds.moments, 3);
}

#[test]
fn a_finding_without_a_question_of_its_own_is_a_certified_comparison() {
    // Every kind of claim has a row.
    assert!(CLAIM_KINDS.iter().all(|(_, row)| *row));
    // A condition that the statements without normative force exclude: the
    // condition alone has a witness, and with those statements it is refuted.
    let excluded = certified("[D]\nThe door is open or closed.\n\n[A]\nWhile the door is ajar, the lamp shall be lit.\n");
    assert_eq!(excluded.diagnostics.iter().map(|d| d.code.as_str()).filter(|code| *code == "condition-unreachable" || *code == "contradiction").collect::<Vec<_>>(), ["condition-unreachable"]);
    let proof = excluded.proof.as_ref().unwrap();
    let claim = proof.comparisons.iter().find(|c| c.environment.name.starts_with("condition-unreachable: ")).expect("the exclusion is a comparison");
    let ComparisonResult::Conflict { base, refutation } = &claim.result else { panic!("the exclusion is no conflict") };
    accepted(&proof.pool, base, Status::Satisfiable);
    accepted(&proof.pool, refutation, Status::Unsatisfiable);
    // The witness is of the premises with the base, and the refutation adds the candidate.
    assert_eq!(base.query, claim.environment.premises.iter().chain(&claim.base).copied().collect::<Vec<_>>());
    assert_eq!(refutation.query, base.query.iter().chain(&claim.candidate).copied().collect::<Vec<_>>());
    assert!(proof.uncertified.is_empty(), "{:?}", proof.uncertified);
    // A result without such a finding lists nothing.
    assert!(certified(SWITCH).proof.as_ref().unwrap().uncertified.is_empty());
}

#[test]
fn the_situations_are_certified() {
    let hard = |proof: &Proof, question: &Question| proof.entries.iter().filter(|e| e.kind.as_str() == "hard").all(|e| question.query.contains(&e.formula));
    // Both conditions can hold together, and then the two statements cannot be kept.
    for text in ["[J1]\nWhen a user sends a message, the API shall store the message.\n\n[J2]\nWhile the room is archived, the API shall not store the message.\n", "[A]\nWhen the size is at least 100, the API shall stop.\n\n[B]\nWhen the size is at most 100, the API shall not stop.\n"] {
        let conflict = certified(text);
        assert_eq!(errors(&conflict), ["contradiction"], "{text}");
        assert_eq!(conflict.consistency.status, Status::Satisfiable);
        assert_eq!(conflict.consistency.verdict, "inconsistent");
        assert_eq!(conflict.conflicts[0].elements.len(), 2);
        let proof = conflict.proof.as_ref().unwrap();
        // The conditions hold together, each statement can be kept there alone, and the two cannot.
        let names: Vec<&str> = proof.answered.iter().map(|(name, _)| name.as_str()).collect();
        assert_eq!(names, ["situation 1: the conditions hold together", "situation 1: statement 1 can be kept alone", "situation 1: statement 2 can be kept alone", "situation 1: the statements cannot all be kept"]);
        for (_, question) in &proof.answered[..3] {
            accepted(&proof.pool, question, Status::Satisfiable);
        }
        let (_, refuted) = &proof.answered[3];
        accepted(&proof.pool, refuted, Status::Unsatisfiable);
        // What is refuted is the two statements under the conditions.
        assert!(hard(proof, refuted));
        assert!(proof.uncertified.is_empty(), "{:?}", proof.uncertified);
    }
    // No conflict: the statements are kept in each largest situation, and no situation lies outside each of them.
    let kept = certified("[K1]\nWhen a user sends a message, the API shall store the message.\n\n[K2]\nWhile the room is archived, the API shall log the message.\n");
    assert!(errors(&kept).is_empty());
    assert_eq!(kept.consistency.verdict, "consistent");
    let proof = kept.proof.as_ref().unwrap();
    let (cover_name, cover) = proof.answered.last().expect("the questions of the situations");
    assert_eq!(cover_name, "situations: every situation lies within a largest one");
    accepted(&proof.pool, cover, Status::Unsatisfiable);
    let largest = &proof.answered[..proof.answered.len() - 1];
    assert!(!largest.is_empty());
    for (name, question) in largest {
        assert!(name.starts_with("situations: the statements are kept in the situation "), "{name}");
        accepted(&proof.pool, question, Status::Satisfiable);
        assert!(hard(proof, question));
    }
    assert!(proof.uncertified.is_empty(), "{:?}", proof.uncertified);
    // A statement without normative force that excludes the situation settles the conflict.
    let excluded = certified("[J1]\nWhen a user sends a message, the API shall store the message.\n\n[J2]\nWhile the room is archived, the API shall not store the message.\n\n[J3]\nWhile the room is archived, no user sends a message.\n");
    assert!(errors(&excluded).is_empty(), "{:?}", errors(&excluded));
    assert_eq!(excluded.consistency.verdict, "consistent");
}
