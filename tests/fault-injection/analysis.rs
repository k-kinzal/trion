#[path = "../common/analysis.rs"]
mod common;

use common::{worker, SETTINGS};
use trion_analysis::{analyze, run_worker, Conclusion, Evidence, Execution, Observation, Record};
use trion_boolean::{solve, Reply, Request, Response, Term, EXACT};
use trion_cnl::{formalize, Grammar};

fn response(request: &Request, reply: Reply) -> Observation {
    Observation::Response(
        serde_json::to_string(&Response {
            request: request.id(),
            scope: request.scope,
            reply,
        })
        .unwrap(),
    )
}

#[test]
fn dropping_a_constraint_changes_the_answer_and_is_detected() {
    let input = formalize(
        "proposition P. proposition Q. assume P implies Q. assume P. entails Q.",
        Grammar::V1,
    )
    .unwrap();
    let checked = analyze(input.problem(), &EXACT, SETTINGS, worker);
    assert_eq!(checked.outcome().conclusion(), Conclusion::Entails);
    let record = analyze(input.problem(), &EXACT, SETTINGS, |request| {
        let mut broken = request.clone();
        broken.condition.remove(1);
        let reply = solve(&broken).unwrap().reply;
        assert_eq!(reply, Reply::Sat(vec![false, false]));
        response(request, reply)
    });
    assert_eq!(record.outcome().execution(), Execution::EvidenceRejected);
    assert_eq!(record.outcome().conclusion(), Conclusion::None);
}

#[test]
fn unknown_timeouts_and_malformed_output_do_not_become_success() {
    let input = formalize("entails false.", Grammar::V1).unwrap();
    for (observation, expected, evidence) in [
        (Observation::Timeout, Execution::Timeout, Evidence::None),
        (
            Observation::Response("{\"reply\":".into()),
            Execution::EvidenceRejected,
            Evidence::None,
        ),
        (
            Observation::BackendFailure("terminated".into()),
            Execution::BackendFailure,
            Evidence::None,
        ),
    ] {
        let checked = analyze(input.problem(), &EXACT, SETTINGS, |_| observation);
        assert_eq!(checked.outcome().execution(), expected);
        assert_eq!(checked.outcome().conclusion(), Conclusion::None);
        assert_eq!(*checked.outcome().evidence(), evidence);
    }
    let checked = analyze(input.problem(), &EXACT, SETTINGS, |request| {
        response(request, Reply::Unknown)
    });
    assert_eq!(checked.outcome().execution(), Execution::Undecided);
    assert_eq!(checked.outcome().conclusion(), Conclusion::None);
    assert_eq!(checked.outcome().evidence(), &Evidence::ExternalResponse);
    let wrong = analyze(input.problem(), &EXACT, SETTINGS, |request| {
        response(request, Reply::Unsat)
    });
    assert_eq!(wrong.outcome().execution(), Execution::EvidenceRejected);
}

#[test]
fn actual_worker_exit_and_timeout_are_observed() {
    const FIXTURE: &str = "TRION_TEST_WORKER_BEHAVIOR";
    match std::env::var(FIXTURE).as_deref() {
        Ok("exit") => std::process::exit(17),
        Ok("wait") => {
            std::thread::sleep(std::time::Duration::from_secs(10));
            return;
        }
        _ => {}
    }
    let input = formalize("entails false.", Grammar::V1).unwrap();
    let executable = std::env::current_exe().unwrap();
    let worker = |mode| {
        let mut command = std::process::Command::new(&executable);
        // Re-enter just this test in the child to exercise real process failures.
        command
            .args(["--exact", "actual_worker_exit_and_timeout_are_observed"])
            .env(FIXTURE, mode);
        command
    };

    let exited = analyze(input.problem(), &EXACT, SETTINGS, |request| {
        run_worker(&mut worker("exit"), request)
    });
    assert_eq!(exited.outcome().execution(), Execution::BackendFailure);
    assert_eq!(exited.outcome().conclusion(), Conclusion::None);
    assert!(
        matches!(exited.observation(), Observation::BackendFailure(reason) if reason.contains("17"))
    );

    let mut settings = SETTINGS;
    settings.backend.timeout_ms = 30;
    let timed = analyze(input.problem(), &EXACT, settings, |request| {
        run_worker(&mut worker("wait"), request)
    });
    assert_eq!(timed.outcome().execution(), Execution::Timeout);
    assert_eq!(timed.outcome().conclusion(), Conclusion::None);
}

#[test]
fn alien_evidence_is_refused_even_if_its_valuation_works() {
    let original = formalize("proposition P. entails P.", Grammar::V1).unwrap();
    let other_query = formalize("proposition P. entails true and P.", Grammar::V1).unwrap();
    let other_premises = formalize("proposition P. assume true. entails P.", Grammar::V1).unwrap();
    for other in [other_query, other_premises] {
        let previous = analyze(other.problem(), &EXACT, SETTINGS, worker);
        assert_eq!(previous.outcome().conclusion(), Conclusion::DoesNotEntail);
        let observation = previous.observation().clone();
        let copied = analyze(original.problem(), &EXACT, SETTINGS, |_| observation);
        assert_eq!(copied.outcome().execution(), Execution::EvidenceRejected);
        assert!(
            Record::replay(original.problem(), &serde_json::to_vec(&previous).unwrap()).is_err()
        );
    }
}

#[test]
fn replay_rejects_added_assumptions_and_fabricated_guarantees() {
    let input = formalize("proposition P. entails P.", Grammar::V1).unwrap();
    let snapshot = serde_json::to_vec(input.problem()).unwrap();
    let record = analyze(input.problem(), &EXACT, SETTINGS, worker);
    let original = serde_json::to_value(&record).unwrap();
    let mut change = original.clone();
    change["translation"]["detail"]["added_assumptions"] =
        serde_json::to_value(vec![Term::Literal {
            slot: 0,
            positive: true,
        }])
        .unwrap();
    assert!(Record::replay(input.problem(), &serde_json::to_vec(&change).unwrap()).is_err());
    let mut change = original.clone();
    change["outcome"]["conclusion"] = "entails".into();
    assert!(Record::replay(input.problem(), &serde_json::to_vec(&change).unwrap()).is_err());
    let mut change = original;
    change["outcome"]["execution"] = "timeout".into();
    assert!(Record::replay(input.problem(), &serde_json::to_vec(&change).unwrap()).is_err());
    assert_eq!(serde_json::to_vec(record.problem()).unwrap(), snapshot);
    assert_eq!(serde_json::to_vec(input.problem()).unwrap(), snapshot);
}

#[test]
fn bounded_and_missing_scope_responses_are_refused() {
    let input = formalize("proposition P. entails true.", Grammar::V1).unwrap();
    let full = analyze(input.problem(), &EXACT, SETTINGS, worker);
    assert_eq!(full.outcome().conclusion(), Conclusion::Entails);
    for scope in [None, Some(serde_json::json!({"bounded": 1}))] {
        let record = analyze(input.problem(), &EXACT, SETTINGS, |request| {
            let mut reply = serde_json::json!({ "request": request.id(), "reply": "unsat" });
            if let Some(scope) = scope {
                reply["scope"] = scope;
            }
            Observation::Response(reply.to_string())
        });
        assert_eq!(record.outcome().execution(), Execution::EvidenceRejected);
        assert_eq!(record.outcome().conclusion(), Conclusion::None);
    }
    let mut settings = SETTINGS;
    settings.backend.max_assignments = 1;
    let record = analyze(input.problem(), &EXACT, settings, |request| {
        response(request, Reply::Unsat)
    });
    assert_eq!(record.outcome().execution(), Execution::EvidenceRejected);
    assert_eq!(record.outcome().conclusion(), Conclusion::None);
}
