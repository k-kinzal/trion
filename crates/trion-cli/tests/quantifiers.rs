//! A response that follows a quantity of the situation (plan W09).
//!
//! `for every load some capacity is greater` has no finite list of constant
//! responses. The claim is decided by a symbolic response, a term over what
//! the situation fixes, and the result names the term.

mod common;
use common::*;

const MANIFEST: (&str, &str) = ("trion.toml", "[package]\nname = \"x\"\n");

/// The terms that a response chooses in the consistency obligation of the
/// MMT form that `trion` writes for a fixture, as `trioc` reads it: every
/// other term is fixed by the situation.
fn chosen(f: &Fixture) -> Vec<String> {
    use trion_verification::ObligationQuestion;
    let run = f.convert(&["--out", "form"]);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let form = trioc_cli::mmt::Form::read(&f.read("form/source/specification.mmt")).unwrap();
    let consistency = form.obligations.obligations.iter().find(|o| o.name == "consistency").expect("a consistency obligation");
    let mut terms = Vec::new();
    let mut found = false;
    let mut questions = vec![&consistency.question];
    while let Some(q) = questions.pop() {
        match q {
            ObligationQuestion::ForAllExists { chosen, .. } => {
                found = true;
                terms.extend(chosen.iter().cloned());
            }
            ObligationQuestion::All { parts } | ObligationQuestion::Any { parts } => questions.extend(parts),
            ObligationQuestion::Not { part } => questions.push(part),
            ObligationQuestion::Satisfiable { .. } | ObligationQuestion::Unsatisfiable { .. } => {}
        }
    }
    assert!(found, "a question for all situations");
    terms
}

#[test]
fn a_capacity_above_every_load_is_a_response_that_follows_the_load() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", "primitive capacity, load\nenvironment load\n\n[A]\nWhile the load is at least 0, the capacity shall be greater than the load.\n")]);
    let report = f.verify(&["--json"]).json();
    assert_verified(&report);
    // The load is fixed by the situation, and the capacity is chosen for it.
    // (The engine named the response, `capacity := load + 0.001`; the proof
    // states that a response exists for each situation and names none.)
    let terms = chosen(&f);
    assert!(terms.iter().any(|t| t.starts_with("capacity@")) && !terms.iter().any(|t| t.starts_with("load@")), "{terms:?}");
    // Without the declaration the load is a term of the response, as the
    // guarantee speaks about it: the response chooses the load, and no
    // response has to follow anything.
    let undeclared = Fixture::new(&[MANIFEST, ("a.trion", "primitive capacity, load\n\n[A]\nWhile the load is at least 0, the capacity shall be greater than the load.\n")]);
    let terms = chosen(&undeclared);
    assert!(terms.iter().any(|t| t.starts_with("load@")), "{terms:?}");
}

/// Two bounds that no capacity meets for a load of the environment: the
/// situation has no response, and the claim is refuted and not left open.
#[test]
fn bounds_that_no_response_meets_for_a_given_load_are_a_conflict() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", "primitive capacity, load\nenvironment load\n\n[A]\nThe capacity shall be greater than the load.\n\n[B]\nThe capacity shall be less than the load.\n")]);
    let result = f.verify(&["--json"]);
    let report = result.json();
    assert_ne!(result.code, 0);
    assert_eq!(verdicts(&report).get("consistency").map(String::as_str), Some("refuted"), "{report}");
    assert!(unverified(&report).contains(&"consistency".to_string()), "{report}");
}
