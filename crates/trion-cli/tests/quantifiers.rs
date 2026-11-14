//! A response that follows a quantity of the situation (plan W09).
//!
//! `for every load some capacity is greater` has no finite list of constant
//! responses. The claim is decided by a symbolic response, a term over what
//! the situation fixes, and the result names the term.

mod common;
use common::*;

const MANIFEST: (&str, &str) = ("trion.toml", "[package]\nname = \"x\"\n");

#[test]
fn a_capacity_above_every_load_is_a_response_that_follows_the_load() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", "primitive capacity, load\nenvironment load\n\n[A]\nWhile the load is at least 0, the capacity shall be greater than the load.\n")]);
    let report = f.trion(&["verify", "--json"]).json();
    assert_verified(&report);
    let situations = report["consistency"]["situations"].as_str().unwrap();
    assert!(situations.contains("a response that follows the situation: capacity := load + 0.001"), "{situations}");
    // Without the declaration the load is a term of the response, as the
    // guarantee speaks about it: the response chooses the load, and no
    // response has to follow anything.
    let chosen = Fixture::new(&[MANIFEST, ("a.trion", "primitive capacity, load\n\n[A]\nWhile the load is at least 0, the capacity shall be greater than the load.\n")]);
    let report = chosen.trion(&["verify", "--json"]).json();
    assert!(!report["consistency"]["situations"].as_str().unwrap().contains("follows the situation"), "{}", report["consistency"]["situations"]);
}

/// Two bounds that no capacity meets for a load of the environment: the
/// situation has no response, and the claim is refuted and not left open.
#[test]
fn bounds_that_no_response_meets_for_a_given_load_are_a_conflict() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", "primitive capacity, load\nenvironment load\n\n[A]\nThe capacity shall be greater than the load.\n\n[B]\nThe capacity shall be less than the load.\n")]);
    let result = f.trion(&["verify", "--json"]);
    let report = result.json();
    assert_ne!(result.code, 0);
    assert_eq!(report["outcome"]["verified"], false);
    let claim = report["claims"].as_array().unwrap().iter().find(|c| c["claim"] == "situation_total").unwrap();
    assert_ne!(claim["verdict"], "proved", "{claim}");
}
