//! The `trioc` command: it reads the MMT form that `trion` wrote, proves
//! each obligation, reports one result for each, and issues certificates
//! only for what it proved.

mod common;
use common::*;

const CONSISTENT: &str = "primitive API, message\n[STORE] The API shall store the message.\n[LOG] The API shall not log the message.\n";
const CONTRADICTORY: &str = "primitive API, message\n[STORE] The API shall store the message.\n[NEVER] The API shall not store the message.\n";

/// A package of one file, converted into `form`.
fn converted(statements: &str) -> Fixture {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", statements)]);
    let run = f.convert(&["--out", "form"]);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    f
}

#[test]
fn a_consistent_package_is_proved_and_a_contradiction_is_refuted_with_its_statements() {
    let good = converted(CONSISTENT).prove(&["form"]);
    assert_eq!(good.code, 0, "{}{}", good.stdout, good.stderr);
    assert!(good.stdout.trim_end().ends_with("\nproved"), "{}", good.stdout);
    let f = converted(CONTRADICTORY);
    let bad = f.prove(&["form"]);
    assert_eq!(bad.code, 1, "{}{}", bad.stdout, bad.stderr);
    assert!(bad.stdout.contains("error[contradiction]") && bad.stdout.contains("[STORE]") && bad.stdout.contains("[NEVER]"), "{}", bad.stdout);
    assert!(bad.stdout.trim_end().ends_with("not proved"), "{}", bad.stdout);
    // The result as JSON names the same finding.
    let json = f.prove(&["form", "--json"]).json();
    assert!(json["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "contradiction"), "{json}");
}

#[test]
fn a_certificate_is_issued_only_for_a_proved_obligation_and_another_solver_decides_it_again() {
    let f = converted(CONTRADICTORY);
    let run = f.prove(&["form", "--certificates", "certificates"]);
    assert_eq!(run.code, 1, "{}{}", run.stdout, run.stderr);
    // Consistency is refuted and has no certificate; compatibility is proved and has one.
    assert!(!f.path().join("certificates/consistency.smt2").exists());
    let script = f.read("certificates/compatibility.smt2");
    let expected: Vec<&str> = script.lines().next().unwrap().trim_start_matches("; the expected answers, in order: ").split_whitespace().collect();
    // z3 is no part of trioc: it checks what trioc wrote, here.
    let output = std::process::Command::new("z3").arg("-in").stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).spawn().and_then(|mut child| {
        use std::io::Write;
        child.stdin.take().unwrap().write_all(script.as_bytes())?;
        child.wait_with_output()
    });
    let output = output.expect("this test needs z3 on PATH");
    let answers: Vec<String> = String::from_utf8_lossy(&output.stdout).lines().map(|l| l.trim().to_string()).filter(|l| matches!(l.as_str(), "sat" | "unsat" | "unknown")).collect();
    assert_eq!(answers, expected, "{script}");
}

#[test]
fn a_format_that_trioc_does_not_know_is_an_error() {
    let f = converted(CONSISTENT);
    // A format that trioc does not know states nothing, and is an error.
    let run = f.prove(&["form", "--certificates", "certificates", "--format", "smt2,pdf"]);
    assert_eq!(run.code, 1, "{}{}", run.stdout, run.stderr);
    assert!(run.stdout.contains("error[certificate-pdf]"), "{}", run.stdout);
}

#[test]
fn a_package_that_declares_no_system_is_told_which_actors_are_taken_for_it() {
    // Responsibility follows the declaration; without one the actors that
    // the requirements speak about are the system, and the reader is told.
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", CONSISTENT)]);
    let run = f.convert(&[]);
    assert!(run.stdout.contains("warning[system-undeclared]") && run.stdout.contains("`system API`"), "{}", run.stdout);
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &format!("system API\n{CONSISTENT}"))]);
    let run = f.convert(&[]);
    assert!(!run.stdout.contains("system-undeclared"), "{}", run.stdout);
}
