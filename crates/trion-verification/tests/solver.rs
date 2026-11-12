//! The contracts that sentences become, and the built-in solver beside an
//! external one.

mod common;
use common::*;
use std::io::Write;
use std::process::{Command, Stdio};
use trion_solver::Status;
use trion_verification::{analyze, smt2, Bounds, Options};

#[test]
fn every_sentence_becomes_a_contract() {
    let analysis = run("When the user leaves, status is Closed.\n");
    let contract = &analysis.model.constraints[0];
    assert_eq!(contract.assume.to_string(), "Event(user leave)");
    assert_eq!(contract.guarantee.to_string(), "Val(status, Closed)");
    assert_eq!(contract.formula().to_string(), "(Event(user leave) → Val(status, Closed))");
}

#[test]
fn modal_force_maps_to_formulas() {
    let formula = |s: &str| run(s).model.constraints[0].guarantee.to_string();
    assert_eq!(formula("The API shall stop."), "(Act(API|stop) ∧ ¬Forbid(API|stop) ∧ ¬Discouraged(API|stop))");
    assert_eq!(formula("The API shall not stop."), "(¬Act(API|stop) ∧ Forbid(API|stop))");
    assert_eq!(formula("The API may stop."), "¬Forbid(API|stop)");
    assert_eq!(formula("The API should stop."), "(¬Forbid(API|stop) ∧ ¬Discouraged(API|stop))");
}

#[test]
fn a_large_independent_set_solves_quickly() {
    let mut src = String::new();
    for i in 0..400 {
        src.push_str(&format!("When the event{i} fires, the node{i} shall run.\n"));
    }
    src.push_str("kind is A and B.\nkind is C.\n");
    let started = std::time::Instant::now();
    assert_eq!(run_codes(&src), ["contradiction"]);
    assert!(started.elapsed().as_secs() < 60, "{:?}", started.elapsed());
}

fn z3(smt2: &str) -> Option<String> {
    let mut child = Command::new("z3").args(["-in", "-smt2"]).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::null()).spawn().ok()?;
    child.stdin.take()?.write_all(smt2.as_bytes()).ok()?;
    let output = child.wait_with_output().ok()?;
    Some(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

#[test]
fn an_external_solver_agrees_with_the_built_in_solver() {
    let cases = [
        "room_type is Private.\nroom_type is Public.\n",
        "room_type is Private and Public.\nroom_type is Invalid.\n",
        "The API shall return foo.\nThe API shall not return foo.\n",
        "The API may return foo.\nThe API should not return foo.\n",
        "The timeout is at most 30 seconds.\nThe timeout is at least 1 minute.\n",
        "The timeout is at most 2 minutes.\nThe timeout is at least 90 seconds.\n",
        "The size is equal to 5 bytes.\nThe size is greater than 4 bytes.\n",
        "The API shall either accept x or reject x.\nThe API shall not accept x.\n",
        "The API shall either accept x or reject x.\nThe API shall not accept x.\nThe API shall not reject x.\n",
    ];
    let mut compared = 0;
    for src in cases {
        // The built-in solver decides the status; the external one is asked
        // the formulas that the status is decided over.
        let set = set(src);
        let analysis = analyze(&set, &Options::default());
        let expected = match analysis.consistency.status {
            Status::Satisfiable => "sat",
            Status::Unsatisfiable => "unsat",
            Status::Unknown => panic!("the built-in solver left {src} open"),
        };
        let Some(answer) = z3(&smt2(&set, &analysis, Bounds::default().trace_length)) else {
            eprintln!("z3 is not installed; the cross-check did not run");
            return;
        };
        assert_eq!(answer, expected, "{src}");
        compared += 1;
    }
    assert_eq!(compared, cases.len());
}
