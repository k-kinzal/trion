//! Statements about individuals: a package that declares the types of its
//! individuals is read over them, one noun names one individual throughout
//! a statement, and a scenario is one concrete behaviour that the reference
//! evaluator and the formulas of the reading judge alike.
//!
//! The expectations are written from `spec/semantics/core.md` and from
//! `docs/practical/W12-requirements.md`, which fixes the behaviours of the
//! rooms example before any result was seen.

mod common;
use common::*;
use serde_json::{json, Value};

const MANIFEST: (&str, &str) = ("trion.toml", "[package]\nname = \"x\"\n");

const SEND: &str = r#"
individuals user, message
primitive system

[A]
When a user sends a message, the system shall store the message within 2 seconds.
"#;

fn scenario<'a>(report: &'a Value, name: &str) -> &'a Value {
    report["scenarios"].as_array().unwrap().iter().find(|s| s["name"] == name).unwrap_or_else(|| panic!("no scenario {name}: {}", report["scenarios"]))
}

fn judged(report: &Value, name: &str) -> (String, String, String) {
    let s = scenario(report, name);
    (s["reference"].as_str().unwrap().to_string(), s["generated"].as_str().unwrap().to_string(), s["verdict"].as_str().unwrap().to_string())
}

fn both(word: &str, verdict: &str) -> (String, String, String) {
    (word.to_string(), word.to_string(), verdict.to_string())
}

#[test]
fn the_rooms_example_is_verified_and_each_scenario_is_judged_as_its_requirement_expects() {
    let result = trion_in(&repo_root().join("examples/rooms"), &["verify", "--json"]);
    let report = result.json();
    assert_eq!(result.code, 0, "{}", report["outcome"]);
    assert_verified(&report);
    // The behaviours of docs/practical/W12-requirements.md, section 2.
    // M1 and M2 are the scenarios of a hundred postings (`measurements.trion`).
    let allowed = ["S1", "S4", "T1", "T5", "T8", "T10", "T13-OWNER", "T13-ADMINISTRATOR", "T14", "M1-SMALL", "M4", "M1"];
    let forbidden = ["S2", "S3", "T2", "T3", "T4", "T6", "T7", "T9", "T11", "T12", "T13", "T15", "M2-SMALL", "M2"];
    for name in allowed {
        assert_eq!(judged(&report, name), both("allowed", "proved"), "{name}");
    }
    for name in forbidden {
        assert_eq!(judged(&report, name), both("forbidden", "refuted"), "{name}");
    }
    assert_eq!(report["scenarios"].as_array().unwrap().len(), allowed.len() + forbidden.len());
    // A forbidden behaviour names the requirement that it fails.
    let fails = |name: &str| -> Vec<String> { scenario(&report, name)["violations"].as_array().unwrap().iter().map(|v| v["statement"].as_str().unwrap().to_string()).collect() };
    assert_eq!(fails("S2"), ["R01"]);
    assert_eq!(fails("S3"), ["R02"]);
    assert_eq!(fails("T3")[0], "R05", "the storing of another message answers no posting");
    assert_eq!(fails("T7"), ["R05", "R14"], "three seconds are within five and not within two");
    assert_eq!(fails("T9"), ["R10"]);
    assert_eq!(fails("T11"), ["R05", "R14", "R15"]);
    // M4: no posting. The shares of R14 and R15 have no value, and they are not counted as met.
    let without_a_value: Vec<&str> = scenario(&report, "M4")["undefined"].as_array().unwrap().iter().map(|u| u[0].as_str().unwrap()).collect();
    assert_eq!(without_a_value, ["R14", "R15"]);
    assert_eq!(scenario(&report, "M1-SMALL")["undefined"], json!([]));
    assert!(fails("M2-SMALL").contains(&"R14".to_string()));
    assert_eq!(fails("T13"), ["R12-OTHERS"]);
    assert!(fails("T15").contains(&"R07".to_string()), "the exception of R05 does not lift the prohibition of R07");
    // The range of each claim names the individuals and the moments.
    for claim in report["claims"].as_array().unwrap().iter().filter(|c| c["subject"].is_null() && c["verdict"] == "proved") {
        assert_eq!(claim["range"]["individuals"], 3, "{claim}");
        assert_eq!(claim["lifted"], false, "{claim}");
    }
}

/// A translation that is broken on purpose is found: the formulas of the
/// broken reading and the reference evaluator differ on a behaviour.
#[test]
fn a_seeded_fault_of_the_reading_is_found_by_a_scenario() {
    let rooms = repo_root().join("examples/rooms");
    // The deadline of one statement is also tried in a package of its own.
    // In the rooms example a share bounds the same deadline. The formulas
    // count the share for themselves, and the fault is seeded in the
    // counted instances too, so the late storing of M2-SMALL tells the
    // faulty reading from the meaning there as well. (While the count was
    // taken from the reference evaluator, the share hid this fault in the
    // rooms example.) A loosened bound of a share is found by a scenario
    // in which the share alone is failed: one of two postings answered,
    // where 75 percent are required.
    let late = repo_root().join("crates/trion-cli/fixtures/codes/scenario-differs/package");
    let share = repo_root().join("crates/trion-cli/fixtures/acceptance/A10-empty-population-and-unanswered/package");
    for (fault, differs_on) in [("reading-binds-another", "T1"), ("reading-drops-negation", "T13"), ("reading-moves-boundary", "LATE"), ("reading-moves-boundary", "M2-SMALL"), ("reading-swaps-quantifier", "T13"), ("reading-loosens-share", "UNANSWERED")] {
        let package = match differs_on {
            "LATE" => &late,
            "UNANSWERED" => &share,
            _ => &rooms,
        };
        let result = trion_with(package, &["verify", "--json"], &[("TRION_FAULT", fault)]);
        let report = result.json();
        assert_ne!(result.code, 0, "{fault}");
        assert_eq!(report["outcome"]["verified"], false, "{fault}");
        assert!(unverified(&report).contains(&"scenario-differs".to_string()), "{fault}: {:?}", unverified(&report));
        let s = scenario(&report, differs_on);
        assert_eq!(s["verdict"], "error", "{fault}: {s}");
        assert_ne!(s["reference"], s["generated"], "{fault}: {s}");
        // The claim of the scenario is an error, and it is not shown as decided.
        let claim = report["claims"].as_array().unwrap().iter().find(|c| c["subject"] == format!("scenario {differs_on}")).unwrap();
        assert_eq!(claim["verdict"], "error", "{fault}");
        assert_eq!(claim["reason"], "reading_differs_from_meaning", "{fault}");
    }
}

#[test]
fn one_noun_names_one_individual_in_the_condition_and_in_the_response() {
    let f = Fixture::new(&[MANIFEST, (
        "a.trion",
        &format!(
            "{SEND}
scenario SAME:
    given a user U1, a message M1
    at 0 ms: U1 sends M1.
    at 1 seconds: the system stores M1.
    expect allowed

scenario OTHER:
    given a user U1, a message M1, a message M2
    at 0 ms: U1 sends M1.
    at 1 seconds: the system stores M2.
    expect forbidden

scenario EACH:
    given a user U1, a message M1, a message M2
    at 0 ms: U1 sends M1.
    at 0 ms: U1 sends M2.
    at 1 seconds: the system stores M1.
    expect forbidden

scenario ON-TIME:
    given a user U1, a message M1
    at 0 ms: U1 sends M1.
    at 2 seconds: the system stores M1.
    expect allowed

scenario LATE:
    given a user U1, a message M1
    at 0 ms: U1 sends M1.
    at 2001 ms: the system stores M1.
    expect forbidden

scenario AGAIN:
    given a user U1, a message M1
    at 0 ms: U1 sends M1.
    at 1 seconds: the system stores M1.
    at 5 seconds: U1 sends M1.
    expect forbidden
"
        ),
    )]);
    let report = f.trion(&["verify", "--json"]).json();
    assert_verified(&report);
    assert_eq!(judged(&report, "SAME"), both("allowed", "proved"));
    assert_eq!(judged(&report, "OTHER"), both("forbidden", "refuted"));
    assert_eq!(judged(&report, "EACH"), both("forbidden", "refuted"));
    assert_eq!(judged(&report, "ON-TIME"), both("allowed", "proved"), "the end of a deadline is included");
    assert_eq!(judged(&report, "LATE"), both("forbidden", "refuted"));
    assert_eq!(judged(&report, "AGAIN"), both("forbidden", "refuted"), "a completion before an occurrence does not answer it");
    // The failing instance is named with its binding and its moment.
    let violation = &scenario(&report, "OTHER")["violations"][0];
    assert_eq!(violation["statement"], "A");
    assert_eq!(violation["moment"], 0);
    assert_eq!(violation["binding"], json!([["user", "user#1"], ["message", "message#1"]]));
    // The reading states the same binding as instances of the statement.
    let individuals = &report["individuals"];
    assert_eq!(individuals["version"], "0.1.0");
    let instances: Vec<&str> = individuals["instances"].as_array().unwrap().iter().map(|i| i["instance"].as_str().unwrap()).collect();
    assert_eq!(instances.len(), 9, "three users and three messages: {instances:?}");
    assert!(instances.contains(&"A/user#2,message#3"), "{instances:?}");
}

/// The record of a reading, against a structure that was written by hand
/// from the sentence: the variables, where each is named, the conditions,
/// the exception, the force and the response with its deadline.
#[test]
fn the_record_of_a_reading_states_the_variables_and_what_is_said_of_them() {
    let f = Fixture::new(&[MANIFEST, (
        "a.trion",
        r#"
individuals user, room, message
primitive system, member

[K]
Each member is a user.

[D]
A room is open or archived.

[R]
While a room is open, when a member of the room posts a message to the room, the system shall store the message within 2 seconds, unless the user is not a member of the room.
"#,
    )]);
    let report = f.trion(&["verify", "--json"]).json();
    let meanings = report["individuals"]["meanings"].as_array().unwrap();
    let r = meanings.iter().find(|m| m["statement"] == "R").unwrap_or_else(|| panic!("{}", report["individuals"]));
    let variables: Vec<(String, String, String)> = r["variables"].as_array().unwrap().iter().map(|v| (v["key"].as_str().unwrap().to_string(), v["carrier"].as_str().unwrap().to_string(), v["site"].as_str().unwrap().to_string())).collect();
    let v = |key: &str, carrier: &str| (key.to_string(), carrier.to_string(), "condition".to_string());
    assert_eq!(variables, [v("room", "room"), v("member", "user"), v("message", "message"), v("user", "user")]);
    // `a member of the room`: the member stands in the relation to the room.
    assert_eq!(r["restrictions"], json!([{"relation": "member", "owner_noun": "room", "owner": {"variable": 0}, "member": {"variable": 1}, "denied": false}]));
    assert_eq!(r["force"], "obligation");
    assert_eq!(r["frames"][0]["kind"], "while");
    assert_eq!(r["frames"][0]["conditions"], json!([{"form": "holds", "subject": {"variable": 0}, "value": "open", "denied": false}]));
    assert_eq!(r["frames"][1]["kind"], "when");
    assert_eq!(r["frames"][1]["conditions"], json!([{"form": "occurs", "denied": false, "pattern": {"actor": {"variable": 1}, "verb": "post", "particle": null, "object": {"variable": 2}, "roles": [["to", {"variable": 0}]]}}]));
    assert_eq!(r["exception"], json!({"form": "related", "relation": "member", "owner_noun": "room", "owner": {"variable": 0}, "member": {"variable": 3}, "denied": true}));
    assert_eq!(r["responses"], json!([{"form": "action", "pattern": {"actor": {"constant": "system"}, "verb": "store", "particle": null, "object": {"variable": 2}, "roles": []}, "deadline": {"thousandths": 2_000_000, "unit": "ms"}, "after": [], "before": []}]));
    // Each step names a rule of the semantic version.
    let rules: Vec<&str> = r["steps"].as_array().unwrap().iter().map(|s| s["rule"].as_str().unwrap()).collect();
    for rule in ["variable", "variable-of", "variable-again", "frame-while", "frame-when", "condition-holds", "condition-occurs", "condition-related", "exception", "force", "response-deadline", "response-action", "constant"] {
        assert!(rules.contains(&rule), "{rule}: {rules:?}");
    }
    // The enumeration is a statement about each room.
    let d = meanings.iter().find(|m| m["statement"] == "D").unwrap();
    assert_eq!(d["force"], "description");
    assert_eq!(d["responses"], json!([{"form": "values", "subject": {"variable": 0}, "values": ["open", "archived"]}]));
}

#[test]
fn a_statement_that_names_a_type_outside_the_typed_fragment_is_rejected() {
    // Old behaviour: `The system shall create a message.` was
    // rejected: "no rule of this version reads which individual a response
    // introduces". Now the response of an obligation chooses the
    // individual that `a` introduces (`a_response_chooses_the_individual_
    // that_it_introduces`); what stays outside is an individual that
    // `the` introduces.
    // Old behaviour: `The system may create a message.` was rejected too
    // ("no rule reads which individual advice or a permission is about"),
    // every relative clause on a declared type was rejected, and so was
    // every count before one. A permission now permits each individual, a
    // relative clause is a condition and a count names its individuals
    // (`individual_forms.rs`); what stays outside is an event in a
    // relative clause beside the event of the statement, and a count in
    // that event.
    for (sentence, part) in [
        ("The system shall create the message.", "the response names with `the` an individual that no condition names"),
        ("When a user that owns a room sends a message, the system shall store the message.", "a statement applies at one event"),
        ("When a new user sends a message, the system shall store the message.", "a modifier before a declared type"),
        ("When two users send a message, the system shall store the message.", "a count in the event of a statement"),
        ("When a user sends a message, the system shall store the message, even when the room is full.", "a concession"),
    ] {
        let f = Fixture::new(&[MANIFEST, ("a.trion", &format!("individuals user, message\nprimitive system, room\n\n[A]\n{sentence}\n"))]);
        let result = f.trion(&["verify", "--json"]);
        let report = result.json();
        assert_ne!(result.code, 0, "{sentence}");
        assert_eq!(report["outcome"]["verified"], false, "{sentence}");
        let unread: Vec<&str> = report["opaque"].as_array().unwrap().iter().chain(report["diagnostics"].as_array().unwrap()).filter(|d| d["code"] == "UNSUPPORTED_SEMANTICS").filter_map(|d| d["message"].as_str()).collect();
        assert!(unread.iter().any(|m| m.contains(part)), "{sentence}: {unread:?}");
    }
}

/// Without a declaration of individuals a package is read as before: one
/// representative of each type, and no instance.
#[test]
fn a_package_that_declares_no_individuals_keeps_its_reading() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", "primitive system, user, message\n\n[A]\nWhen a user sends a message, the system shall store the message.\n")]);
    let report = f.trion(&["verify", "--json"]).json();
    assert!(report["individuals"].is_null(), "{}", report["individuals"]);
    assert_eq!(report["scenarios"], json!([]));
    let gate = report["gates"].as_array().unwrap().iter().find(|g| g["name"] == "checker").unwrap();
    assert_eq!(gate["state"], "skipped");
    assert!(report["outcome"]["not_examined"].as_array().unwrap().iter().any(|n| n == "gate checker"), "{}", report["outcome"]);
}

#[test]
fn a_scenario_that_is_not_read_is_judged_of_nothing() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", &format!("{SEND}\nscenario BAD:\n    given a user U1, a message M1\n    at soon: U1 sends M1.\n    expect allowed\n"))]);
    let result = f.trion(&["verify", "--json"]);
    let report = result.json();
    assert_ne!(result.code, 0);
    assert_eq!(judged(&report, "BAD").2, "invalid");
    assert!(report_codes(&report).contains(&"parse-scenario".to_string()), "{:?}", report_codes(&report));
}

/// A relation between individuals is a fact of the domain and no state of a
/// moment: a condition on it selects the individuals that a statement is about.
#[test]
fn a_relation_between_individuals_selects_the_instances_of_a_statement() {
    let f = Fixture::new(&[MANIFEST, (
        "a.trion",
        r#"
individuals user, room
primitive system, member

[K]
Each member is a user.

[IN]
When a member of a room enters the room, the system shall admit the member to the room.

[OUT]
While a user is not a member of a room, when the user enters the room, the system shall not admit the user to the room.

scenario MEMBER:
    given a user U1, a room R1
    given U1 is a member of R1.
    at 0 ms: U1 enters R1.
    at 1 seconds: the system admits U1 to R1.
    expect allowed

scenario STRANGER:
    given a user U1, a room R1
    at 0 ms: U1 enters R1.
    at 1 seconds: the system admits U1 to R1.
    expect forbidden

scenario ELSEWHERE:
    given a user U1, a room R1, a room R2
    given U1 is a member of R2.
    at 0 ms: U1 enters R1.
    at 1 seconds: the system admits U1 to R1.
    expect forbidden
"#,
    )]);
    let report = f.trion(&["verify", "--json"]).json();
    assert_verified(&report);
    assert_eq!(judged(&report, "MEMBER"), both("allowed", "proved"));
    assert_eq!(judged(&report, "STRANGER"), both("forbidden", "refuted"));
    assert_eq!(judged(&report, "ELSEWHERE"), both("forbidden", "refuted"), "the membership of another room is no membership of this one");
}

/// The check of the reading derives the meaning of each statement again
/// and refuses what differs: a record that binds another variable, states
/// another unit, names no rule or lacks an instance, and a contract that
/// drops a negation, names another individual, moves a bound or stands for
/// one individual where the statement speaks of each.
#[test]
fn a_record_or_a_contract_that_differs_from_the_statement_is_refused() {
    let package = format!("{SEND}\nscenario STORED:\n    given a user U1, a message M1\n    at 0 ms: U1 sends M1.\n    at 1 seconds: the system stores M1.\n    expect allowed\n");
    let f = Fixture::new(&[MANIFEST, ("a.trion", &package)]);
    let sound = f.trion(&["verify", "--json"]).json();
    assert_verified(&sound);
    assert_eq!(sound["derivations"]["statements"], 1);
    assert_eq!(sound["derivations"]["contracts"], 9);
    assert_eq!(sound["derivations"]["of_instances"], 9);
    assert_eq!(sound["derivations"]["not_derived"], json!([]));
    for (fault, part) in [
        ("record-binds-another", "the responses of the record"),
        ("record-changes-unit", "the responses of the record"),
        ("record-names-no-rule", "names no rule of the semantic version"),
        ("record-drops-instance", "8 instances"),
        ("reading-binds-another", "the guarantee of the contract"),
        ("reading-drops-negation", "the guarantee of the contract"),
        ("reading-moves-boundary", "the bounds of the contract"),
        ("reading-swaps-quantifier", "0 contracts stand for the instance"),
    ] {
        let result = trion_with(f.path(), &["verify", "--json"], &[("TRION_FAULT", fault)]);
        let report = result.json();
        assert_ne!(result.code, 0, "{fault}");
        assert_eq!(report["outcome"]["verified"], false, "{fault}");
        let refusals: Vec<&str> = report["checker"].as_array().unwrap().iter().filter(|d| d["code"] == "derivation-refused").filter_map(|d| d["message"].as_str()).collect();
        assert!(refusals.iter().any(|m| m.contains(part)), "{fault}: {refusals:?}");
        let gate = report["gates"].as_array().unwrap().iter().find(|g| g["name"] == "checker").unwrap();
        assert_eq!(gate["state"], "failed", "{fault}");
    }
}

const SHARES: &str = r#"
individuals user, message
primitive system
measure postings

[HALF]
When a user posts a message, the system shall store the message within 2 seconds for at least 50 percent of postings.

[SLOW]
When a user posts a message, the system shall store the message within 5 seconds for at least 75 percent of postings.
"#;

/// A share is a count of the activations of its statement in one behaviour:
/// the population holds each activation, answered or not, and the bound is
/// compared in whole numbers. The share of an empty population has no value.
#[test]
fn a_share_is_a_count_of_the_activations_that_a_response_answers() {
    let f = Fixture::new(&[MANIFEST, (
        "a.trion",
        &format!(
            "{SHARES}
scenario ONE-OF-TWO:
    given a user U1, a message M1, a message M2
    at 0 ms: U1 posts M1.
    at 0 ms: U1 posts M2.
    at 1 seconds: the system stores M1.
    at 4 seconds: the system stores M2.
    expect allowed

scenario NONE-IN-TIME:
    given a user U1, a message M1, a message M2
    at 0 ms: U1 posts M1.
    at 0 ms: U1 posts M2.
    at 3 seconds: the system stores M1.
    at 4 seconds: the system stores M2.
    expect forbidden

scenario UNANSWERED:
    given a user U1, a message M1, a message M2
    at 0 ms: U1 posts M1.
    at 0 ms: U1 posts M2.
    at 1 seconds: the system stores M1.
    expect forbidden

scenario EMPTY:
    given a user U1, a message M1
    expect undefined
"
        ),
    )]);
    let report = f.trion(&["verify", "--json"]).json();
    assert_verified(&report);
    // One of two within two seconds is half; both within five is all.
    assert_eq!(judged(&report, "ONE-OF-TWO"), both("allowed", "proved"));
    // None within two seconds: the bound of [HALF] fails.
    assert_eq!(judged(&report, "NONE-IN-TIME"), both("forbidden", "refuted"));
    assert_eq!(scenario(&report, "NONE-IN-TIME")["violations"][0]["statement"], "HALF");
    // A posting without a response stays in the population: one of two is no 75 percent.
    assert_eq!(judged(&report, "UNANSWERED"), both("forbidden", "refuted"));
    assert_eq!(scenario(&report, "UNANSWERED")["violations"][0]["statement"], "SLOW");
    assert!(scenario(&report, "UNANSWERED")["violations"][0]["what"].as_str().unwrap().contains("1 of 2"));
    // No posting: the behaviour fails nothing, and the share has no value
    // in it. The statements are listed as neither met nor failed: an empty
    // population is no share of 100 percent.
    assert_eq!(judged(&report, "EMPTY"), both("allowed", "proved"));
    let without_a_value: Vec<&str> = scenario(&report, "EMPTY")["undefined"].as_array().unwrap().iter().map(|u| u[0].as_str().unwrap()).collect();
    assert_eq!(without_a_value, ["HALF", "SLOW"]);
    assert!(scenario(&report, "EMPTY")["undefined"][0][1].as_str().unwrap().contains("a share of an empty population"));
    assert_eq!(scenario(&report, "ONE-OF-TWO")["undefined"], json!([]));
    let claim = report["claims"].as_array().unwrap().iter().find(|c| c["subject"] == "scenario EMPTY").unwrap();
    assert!(claim["evidence"][0].as_str().unwrap().contains("not counted as met: the share of [HALF], [SLOW]"), "{claim}");
    // Old behaviour: a statement that bounds a share had no instance, and
    // the formulas took the value of the share from the count of the
    // reference evaluator: `assert_eq!(report["individuals"]["instances"],
    // json!([]))`. The formulas now count for themselves: each assignment
    // of the statement is an instance that says what one activation is and
    // what answers it. The instances are counted and none is a contract of
    // its own, and the check of the reading derives each of them again.
    let instances = report["individuals"]["instances"].as_array().unwrap();
    assert_eq!(instances.len(), 18, "two statements over three users and three messages");
    assert!(instances.iter().all(|i| i["statement"] == "HALF" || i["statement"] == "SLOW"), "{instances:?}");
    assert_eq!(report["derivations"]["contracts"], 18);
    assert_eq!(report["derivations"]["not_derived"], json!([]));
    let shares: Vec<&str> = report["individuals"]["shares"].as_array().unwrap().iter().map(|s| s["statement"].as_str().unwrap()).collect();
    assert_eq!(shares, ["HALF", "SLOW"]);
    let half = report["individuals"]["meanings"].as_array().unwrap().iter().find(|m| m["statement"] == "HALF").unwrap();
    assert_eq!(half["share"], json!({"bounding": "at_least", "thousandths": 50_000, "population": "postings"}));
}

/// The postings that are stored within two seconds are among those that are
/// stored within five: a larger share within the smaller deadline than
/// within the larger one is a share of no behaviour.
#[test]
fn the_shares_of_one_population_within_two_deadlines_are_ordered() {
    let narrow = format!("{SHARES}\n[FEW]\nWhen a user posts a message, the system shall store the message within 5 seconds for at most 40 percent of postings.\n");
    let f = Fixture::new(&[MANIFEST, ("a.trion", &narrow)]);
    let result = f.trion(&["verify", "--json"]);
    let report = result.json();
    assert_ne!(result.code, 0);
    assert!(unverified(&report).contains(&"contradiction".to_string()), "{:?}", unverified(&report));
    // The same bound on another population says nothing about this one.
    let other = format!("measure uploads\n{SHARES}\n[FEW]\nWhen a user posts a message, the system shall store the message within 5 seconds for at most 40 percent of uploads.\n");
    let f = Fixture::new(&[MANIFEST, ("a.trion", &other)]);
    assert_verified(&f.trion(&["verify", "--json"]).json());
    // `expect undefined` says that a share has no value: a behaviour in which each share has one fails it.
    let valued = format!("{SHARES}\nscenario VALUED:\n    given a user U1, a message M1\n    at 0 ms: U1 posts M1.\n    at 1 seconds: the system stores M1.\n    expect undefined\n");
    let f = Fixture::new(&[MANIFEST, ("a.trion", &valued)]);
    let report = f.trion(&["verify", "--json"]).json();
    assert!(unverified(&report).contains(&"scenario-failed".to_string()), "{:?}", unverified(&report));
}

/// The reading of a statement is shown where its author reads the result:
/// in the text of `verify`, in its JSON, and in the document. Each view is
/// made from the same record, and each names the domain and the semantic version.
#[test]
fn the_reading_of_a_statement_is_shown_in_each_view() {
    let rooms = repo_root().join("examples/rooms");
    let text = trion_in(&rooms, &["verify"]).stdout;
    assert!(text.contains("individuals: semantic version 0.1.0; domains of 3 individuals of each declared type (message, room, user)"), "{text}");
    let expected = [
        "reading [R05]:",
        "  about: each room; each member (an individual of `user`) that is a member of the room; each message",
        "  applies at each moment at which: the room is `open`",
        "  applies at each occurrence at which: [the member post the message to the room] occurs",
        "  does not apply where: the mode of the room is `maintenance`",
        "  requires: [the system store the message], completed at most 2000 ms after the occurrence (the end included)",
    ];
    assert!(text.contains(&expected.join("\n")), "{text}");
    assert!(text.contains("reading [R01]: a statement about the domain (related)"), "{text}");
    assert!(text.contains("  of: at least 99.000 percent of the activations of this statement in one behaviour (`postings`)"), "{text}");
    assert!(text.contains("scenario T3: forbidden for the reference evaluator, forbidden for the formulas of the reading (expected: forbidden)"), "{text}");
    assert!(text.contains("scenario M4: allowed for the reference evaluator, allowed for the formulas of the reading (expected: undefined); the share of [R14], [R15] has no value in it and is not counted as met"), "{text}");
    assert!(text.contains("the record of 17 of 17 typed statements and the contract of 321 of 321 instances were derived again and agree"), "{text}");
    // What `verified` covers: the bounds, and the scenarios apart from the bounded claims.
    assert!(text.contains("covers: within traces of 3 moments, domains of 3 individuals:"), "{text}");
    assert!(text.contains("no result is lifted beyond these bounds; 26 scenarios are judged as expected"), "{text}");
    assert!(text.trim_end().ends_with("verified"), "{text}");
    // The JSON report holds the same lines.
    let report = trion_in(&rooms, &["verify", "--json"]).json();
    let r05 = report["readings"].as_array().unwrap().iter().find(|r| r["statement"] == "R05").unwrap();
    let lines: Vec<&str> = r05["lines"].as_array().unwrap().iter().map(|l| l.as_str().unwrap()).collect();
    assert_eq!(lines, expected[1..].iter().map(|l| l.trim_start()).collect::<Vec<_>>());
    assert_eq!(r05["version"], "0.1.0");
    // The document shows the readings and the scenarios in its status.
    let html = trion_in(&rooms, &["doc"]).stdout;
    assert!(html.contains("readings over individuals"), "the document holds no readings");
    assert!(html.contains("[R05] While a room is open, when a member of the room posts a message to the room"), "the document does not set the sentence beside its reading");
    assert!(html.contains("scenario T3: forbidden for the reference evaluator, forbidden for the formulas of the reading"));
    assert!(html.contains("individuals: semantic version 0.1.0; domains of 3 individuals of each declared type"));
}

/// The formulas count a share for themselves. Written from the rule before
/// the run: with four postings, three answered in time are 75 percent; two
/// are 50 percent. An upper bound counts the completions.
#[test]
fn the_formulas_count_the_activations_of_a_share() {
    const HEAD: &str = "individuals user, message\nprimitive system\nmeasure postings\nmeasure uploads\n";
    let posted = "    given a user U1, a message M1, a message M2, a message M3, a message M4\n    at 0 ms: U1 posts M1.\n    at 0 ms: U1 posts M2.\n    at 0 ms: U1 posts M3.\n    at 0 ms: U1 posts M4.\n";
    let stored = |messages: &[&str]| messages.iter().map(|m| format!("    at 1 seconds: the system stores {m}.\n")).collect::<String>();
    let package = |statement: &str, expect: [&str; 3]| {
        format!(
            "{HEAD}\n{statement}\n\nscenario THREE:\n{posted}{}    expect {}\n\nscenario TWO:\n{posted}{}    expect {}\n\nscenario NONE:\n{posted}    expect {}\n",
            stored(&["M1", "M2", "M3"]),
            expect[0],
            stored(&["M1", "M2"]),
            expect[1],
            expect[2]
        )
    };
    let agree = |report: &Value, name: &str, word: &str| {
        let s = scenario(report, name);
        assert_eq!((s["reference"].as_str().unwrap(), s["generated"].as_str().unwrap()), (word, word), "{name}: {s}");
    };
    // At least 75 percent: three of four meet it, two of four and none of four do not.
    let lower = Fixture::new(&[MANIFEST, ("a.trion", &package("[MOST]\nWhen a user posts a message, the system shall store the message within 2 seconds for at least 75 percent of postings.", ["allowed", "forbidden", "forbidden"]))]);
    let report = lower.trion(&["verify", "--json"]).json();
    assert_verified(&report);
    agree(&report, "THREE", "allowed");
    agree(&report, "TWO", "forbidden");
    agree(&report, "NONE", "forbidden");
    // At most 50 percent: three of four exceed it, two of four and none of four do not.
    let upper = Fixture::new(&[MANIFEST, ("a.trion", &package("[FEW]\nWhen a user posts a message, the system shall store the message within 2 seconds for at most 50 percent of postings.", ["forbidden", "allowed", "allowed"]))]);
    let report = upper.trion(&["verify", "--json"]).json();
    assert_verified(&report);
    agree(&report, "THREE", "forbidden");
    agree(&report, "TWO", "allowed");
    agree(&report, "NONE", "allowed");
    // A bound that is half of what the statement says is refused by the
    // check of the reading, and a scenario tells it from the meaning.
    let result = trion_with(lower.path(), &["verify", "--json"], &[("TRION_FAULT", "reading-loosens-share")]);
    let report = result.json();
    assert_ne!(result.code, 0);
    let refusals: Vec<&str> = report["checker"].as_array().unwrap().iter().filter(|d| d["code"] == "derivation-refused").filter_map(|d| d["message"].as_str()).collect();
    assert!(refusals.iter().any(|m| m.contains("the bound of the contract")), "{refusals:?}");
    let two = scenario(&report, "TWO");
    assert_eq!((two["reference"].as_str().unwrap(), two["generated"].as_str().unwrap(), two["verdict"].as_str().unwrap()), ("forbidden", "allowed", "error"), "{two}");
}

/// A share of a hundred postings. Written from the rule before the run:
/// two messages are posted fifty times each, ten seconds apart, so the
/// population is a hundred activations and no storing lies in the window of
/// another posting. Ninety-nine storings in time are 99 percent and meet
/// `at least 99 percent`; ninety-eight are 98 percent and do not. A posting
/// that nothing answers stays in the population.
#[test]
fn a_share_of_a_hundred_postings_is_counted() {
    const HEAD: &str = "individuals user, message\nprimitive system\nmeasure postings\n";
    let behaviour = |unanswered: usize| {
        let mut text = String::from("    given a user U1, a message M1, a message M2\n");
        let mut posting = 0;
        for round in 0..50 {
            let at = round * 10_000;
            for message in ["M1", "M2"] {
                text.push_str(&format!("    at {at} ms: U1 posts {message}.\n"));
            }
            for message in ["M1", "M2"] {
                posting += 1;
                if posting > unanswered {
                    text.push_str(&format!("    at {} ms: the system stores {message}.\n", at + 1000));
                }
            }
        }
        text
    };
    let package = format!(
        "{HEAD}\n[MOST]\nWhen a user posts a message, the system shall store the message within 2 seconds for at least 99 percent of postings.\n\nscenario NINETY-NINE:\n{}    expect allowed\n\nscenario NINETY-EIGHT:\n{}    expect forbidden\n",
        behaviour(1),
        behaviour(2)
    );
    let f = Fixture::new(&[MANIFEST, ("a.trion", &package)]);
    let report = f.trion(&["verify", "--json"]).json();
    assert_verified(&report);
    for (name, word) in [("NINETY-NINE", "allowed"), ("NINETY-EIGHT", "forbidden")] {
        let s = scenario(&report, name);
        assert_eq!((s["reference"].as_str().unwrap(), s["generated"].as_str().unwrap()), (word, word), "{name}: {s}");
    }
    let said: Vec<&str> = scenario(&report, "NINETY-EIGHT")["violations"].as_array().unwrap().iter().filter_map(|v| v["what"].as_str()).collect();
    assert!(said.iter().any(|what| what.contains("98 of 100 `postings` are answered")), "{said:?}");
    // A reading with half the bound takes ninety-eight of a hundred for enough: the scenario tells it from the meaning.
    let result = trion_with(f.path(), &["verify", "--json"], &[("TRION_FAULT", "reading-loosens-share")]);
    assert_ne!(result.code, 0);
    let fewer = scenario(&result.json(), "NINETY-EIGHT").clone();
    assert_eq!((fewer["reference"].as_str().unwrap(), fewer["generated"].as_str().unwrap(), fewer["verdict"].as_str().unwrap()), ("forbidden", "allowed", "error"), "{fewer}");
}

/// A measure names one population. Two statements that apply under other
/// conditions count other activations: one name for both would order the
/// shares of two populations as the shares of one.
#[test]
fn one_measure_names_the_activations_of_one_condition() {
    const HEAD: &str = "individuals user, message\nprimitive system\nmeasure postings\nmeasure deletions\n";
    let posting = "[A]\nWhen a user posts a message, the system shall store the message within 2 seconds for at least 50 percent of postings.\n";
    let other = Fixture::new(&[MANIFEST, ("a.trion", &format!("{HEAD}\n{posting}\n[B]\nWhen a user deletes a message, the system shall store the message within 5 seconds for at most 40 percent of postings.\n"))]);
    let result = other.trion(&["verify", "--json"]);
    let report = result.json();
    assert_ne!(result.code, 0);
    let named = report["opaque"].as_array().unwrap().iter().any(|d| d["code"] == "UNSUPPORTED_SEMANTICS" && d["message"].as_str().unwrap().contains("the measure `postings` names the activations of [A]"));
    assert!(named, "{}", report["opaque"]);
    // With a measure of its own the second statement counts its own population, and both bounds hold.
    let apart = Fixture::new(&[MANIFEST, ("a.trion", &format!("{HEAD}\n{posting}\n[B]\nWhen a user deletes a message, the system shall store the message within 5 seconds for at most 40 percent of deletions.\n"))]);
    assert_verified(&apart.trion(&["verify", "--json"]).json());
}

/// The claim that a behaviour keeps every contract rests on a model of
/// formulas. The model is written down as a complete behaviour in the terms
/// of the statements, and the reference evaluator judges it.
#[test]
fn the_behaviour_behind_contract_sat_is_judged_by_the_reference_evaluator() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", SEND)]);
    let report = f.trion(&["verify", "--json"]).json();
    assert_verified(&report);
    let witness = &report["witness"];
    assert_eq!(witness["state"], "accepted", "{witness}");
    // A statement applies in it: a user sends a message at the first
    // moment, and the system stores that message at a later one. Nothing
    // else happens: what no statement needs is left out.
    let moments = witness["behaviour"]["moments"].as_array().unwrap();
    let sent = moments[0]["occurrences"].as_array().unwrap();
    assert_eq!(sent.len(), 1, "{witness}");
    assert_eq!(sent[0]["verb"], "send");
    let stored: Vec<&Value> = moments[1..].iter().flat_map(|m| m["occurrences"].as_array().unwrap()).collect();
    assert_eq!(stored.len(), 1, "{witness}");
    assert_eq!((stored[0]["verb"].as_str().unwrap(), &stored[0]["object"]), ("store", &sent[0]["object"]), "{witness}");
    let claim = report["claims"].as_array().unwrap().iter().find(|c| c["claim"] == "contract_sat").unwrap();
    assert!(claim["evidence"].as_array().unwrap().iter().any(|e| e.as_str().unwrap().starts_with("as a concrete behaviour (accepted): ")), "{claim}");
    // A reading that takes a later completion for one in time accepts a
    // behaviour that the statement refuses: the claim is an error, and the
    // package is not verified.
    let late = repo_root().join("crates/trion-cli/fixtures/codes/witness-refused/package");
    let result = trion_with(&late, &["verify", "--json"], &[("TRION_FAULT", "reading-moves-boundary")]);
    let report = result.json();
    assert_ne!(result.code, 0);
    assert!(unverified(&report).contains(&"witness-refused".to_string()), "{:?}", unverified(&report));
    assert_eq!(report["witness"]["state"], "refused");
    let claim = report["claims"].as_array().unwrap().iter().find(|c| c["claim"] == "contract_sat").unwrap();
    assert_eq!((claim["verdict"].as_str().unwrap(), claim["reason"].as_str().unwrap()), ("error", "reading_differs_from_meaning"), "{claim}");
    // Without the fault the same package is verified, with moments that the deadline admits.
    let sound = trion_in(&late, &["verify", "--json"]).json();
    assert_verified(&sound);
    assert_eq!(sound["witness"]["state"], "accepted");
}

/// A reading that differs from the meaning only on a behaviour that no
/// scenario states is found on the behaviours next to the scenarios.
#[test]
fn the_reading_and_the_meaning_agree_next_to_the_scenarios() {
    let package = format!("{SEND}\nscenario STORED:\n    given a user U1, a message M1, a message M2\n    at 0 ms: U1 sends M1.\n    at 1 seconds: the system stores M1.\n    expect allowed\n");
    let f = Fixture::new(&[MANIFEST, ("a.trion", &package)]);
    let report = f.trion(&["verify", "--json", "--properties"]).json();
    assert_verified(&report);
    let variations = &report["variations"];
    let made = variations["behaviours"].as_u64().unwrap();
    // The storing left out, moved, about the other message; a later moment.
    assert!(made >= 6, "{variations}");
    assert_eq!(variations["agreed"].as_u64().unwrap(), made, "{variations}");
    assert_eq!(variations["undecided"], json!([]));
    // The situation of the scenario is the sending without the storing.
    // The formulas give a response to it, and the reference evaluator
    // accepts the behaviour with that response.
    assert_eq!((variations["situations"].as_u64(), variations["answered"].as_u64()), (Some(1), Some(1)), "{variations}");
    assert_eq!((&variations["unanswered"], &variations["open"]), (&json!([]), &json!([])), "{variations}");
    // Without `--properties` the variations are not made, and the gate says so.
    let plain = f.trion(&["verify", "--json"]).json();
    assert_eq!(plain["variations"], Value::Null);
    assert!(plain["outcome"]["not_examined"].as_array().unwrap().iter().any(|what| what == "gate properties"));
    // The stated scenario stores the message after one second, which a
    // deadline of two seconds and one of three both admit: the scenario
    // does not tell a moved deadline from the stated one. The variation
    // with the storing later by a deadline does.
    let result = trion_with(f.path(), &["verify", "--json", "--properties"], &[("TRION_FAULT", "reading-moves-boundary")]);
    let report = result.json();
    assert_ne!(result.code, 0);
    assert_eq!(scenario(&report, "STORED")["verdict"], "proved");
    let found: Vec<&str> = report["properties"].as_array().unwrap().iter().filter(|d| d["code"] == "scenario-differs").filter_map(|d| d["message"].as_str()).collect();
    assert!(found.iter().any(|m| m.contains("each later moment 2000 ms later") && m.contains("finds the behaviour forbidden and the formulas of the reading find it allowed")), "{found:?}");
    let gate = report["gates"].as_array().unwrap().iter().find(|g| g["name"] == "properties").unwrap();
    assert_eq!(gate["state"], "failed");
}

/// `a` or `an` that first names an individual in what an obligation
/// requires: the response chooses the individual. Written from the rule
/// before the run: some ticket answers a report, whichever it is; no
/// ticket, or a ticket after the deadline, answers none; one ticket may
/// answer two reports.
#[test]
fn a_response_chooses_the_individual_that_it_introduces() {
    // The statements say that there is a ticket. Old behaviour: the
    // package was verified without [SOME], because the analysis let the
    // response choose which individuals there are. The individuals of the
    // domain are given, so a domain without a ticket is a situation in
    // which no ticket can be created, and the package says that it does
    // not occur.
    const TICKETS: &str = "individuals user, message, ticket\nprimitive system\n\n[SOME]\nThere is a ticket.\n\n[T]\nWhen a user reports a message, the system shall create a ticket within 2 seconds.\n";
    let scenarios = "
scenario MADE:
    given a user U1, a message M1, a ticket K1
    at 0 ms: U1 reports M1.
    at 1 seconds: the system creates K1.
    expect allowed

scenario NONE:
    given a user U1, a message M1, a ticket K1
    at 0 ms: U1 reports M1.
    expect forbidden

scenario LATE:
    given a user U1, a message M1, a ticket K1
    at 0 ms: U1 reports M1.
    at 3 seconds: the system creates K1.
    expect forbidden

scenario ANY:
    given a user U1, a message M1, a ticket K1, a ticket K2
    at 0 ms: U1 reports M1.
    at 1 seconds: the system creates K2.
    expect allowed

scenario ONE-FOR-TWO:
    given a user U1, a message M1, a message M2, a ticket K1
    at 0 ms: U1 reports M1.
    at 0 ms: U1 reports M2.
    at 1 seconds: the system creates K1.
    expect allowed
";
    let f = Fixture::new(&[MANIFEST, ("a.trion", &format!("{TICKETS}{scenarios}"))]);
    let report = f.trion(&["verify", "--json", "--properties"]).json();
    assert_verified(&report);
    for (name, word, verdict) in [("MADE", "allowed", "proved"), ("NONE", "forbidden", "refuted"), ("LATE", "forbidden", "refuted"), ("ANY", "allowed", "proved"), ("ONE-FOR-TWO", "allowed", "proved")] {
        assert_eq!(judged(&report, name), both(word, verdict), "{name}");
    }
    // The reading and the meaning agree next to these scenarios as well.
    assert_eq!(report["variations"]["agreed"], report["variations"]["behaviours"], "{}", report["variations"]);
    // The record: the ticket is chosen, and an instance binds the user and the message.
    let record = report["individuals"]["meanings"].as_array().unwrap().iter().find(|m| m["statement"] == "T").unwrap();
    let sites: Vec<(&str, &str)> = record["variables"].as_array().unwrap().iter().map(|v| (v["key"].as_str().unwrap(), v["site"].as_str().unwrap())).collect();
    assert_eq!(sites, [("user", "condition"), ("message", "condition"), ("ticket", "chosen")]);
    assert!(record["steps"].as_array().unwrap().iter().any(|s| s["rule"] == "variable-some"), "{record}");
    let reading = report["readings"].as_array().unwrap().iter().find(|r| r["statement"] == "T").unwrap();
    assert!(reading["lines"][0].as_str().unwrap().contains("some ticket, chosen by the response"), "{reading}");
    let instances = report["individuals"]["instances"].as_array().unwrap();
    assert_eq!(instances.len(), 9, "three users and three messages: {instances:?}");
    assert!(instances.iter().all(|i| i["binding"].as_array().unwrap().len() == 2));
    // `the` introduces no individual.
    // Old behaviour: `may create a ticket` and `should create a ticket`
    // were rejected as well ("no rule reads which individual advice or a
    // permission is about"). Advice now chooses its individual as an
    // obligation does, and a permission permits each individual
    // (`individual_forms.rs`).
    let other = Fixture::new(&[MANIFEST, ("a.trion", "individuals user, message, ticket\nprimitive system\n\n[T]\nWhen a user reports a message, the system shall create the ticket.\n")]).trion(&["verify", "--json"]).json();
    assert!(unverified(&other).contains(&"UNSUPPORTED_SEMANTICS".to_string()), "{:?}", unverified(&other));
}

/// `a member of the room` in a response is some member; `each member of
/// the room` is each. One behaviour tells the two statements apart.
#[test]
fn a_chosen_individual_stands_in_the_relation_that_names_it() {
    let package = |determiner: &str, expect: [&str; 3]| {
        format!(
            "individuals user, room\nprimitive system, member\n\nEach member is a user.\n\n[HAS]\nEach room has at least one member.\n\n[N]\nWhen a user enters a room, the system shall notify {determiner} member of the room within 2 seconds.\n
scenario ONE-OF-TWO:
    given a user U1, a user U2, a user U3, a room R1
    given U2 is a member of R1.
    given U3 is a member of R1.
    at 0 ms: U1 enters R1.
    at 1 seconds: the system notifies U2.
    expect {}

scenario OUTSIDER:
    given a user U1, a user U2, a user U3, a room R1
    given U2 is a member of R1.
    at 0 ms: U1 enters R1.
    at 1 seconds: the system notifies U3.
    expect {}

scenario BOTH:
    given a user U1, a user U2, a user U3, a room R1
    given U2 is a member of R1.
    given U3 is a member of R1.
    at 0 ms: U1 enters R1.
    at 1 seconds: the system notifies U2.
    at 1 seconds: the system notifies U3.
    expect {}
",
            expect[0], expect[1], expect[2]
        )
    };
    // Some member: one of the two is enough; one who is no member is none.
    // ([HAS] says that a room has a member: without it, a room without
    // members is a situation in which no member can be notified. Old
    // behaviour: the package was verified without it.)
    let some = Fixture::new(&[MANIFEST, ("a.trion", &package("a", ["allowed", "forbidden", "allowed"]))]).trion(&["verify", "--json"]).json();
    assert_verified(&some);
    assert_eq!(judged(&some, "ONE-OF-TWO"), both("allowed", "proved"));
    assert_eq!(judged(&some, "OUTSIDER"), both("forbidden", "refuted"));
    assert_eq!(judged(&some, "BOTH"), both("allowed", "proved"));
    // Each member: one of the two is not enough.
    // A reading that lets the response choose any user accepts the
    // notifying of one who is no member: the scenario OUTSIDER tells it
    // from the meaning.
    let f = Fixture::new(&[MANIFEST, ("a.trion", &package("a", ["allowed", "forbidden", "allowed"]))]);
    let result = trion_with(f.path(), &["verify", "--json"], &[("TRION_FAULT", "reading-chooses-any")]);
    let faulty = result.json();
    assert_ne!(result.code, 0);
    let outsider = scenario(&faulty, "OUTSIDER");
    assert_eq!((outsider["reference"].as_str().unwrap(), outsider["generated"].as_str().unwrap(), outsider["verdict"].as_str().unwrap()), ("forbidden", "allowed", "error"), "{outsider}");
    // In OUTSIDER the one member is not notified, so that fails as well.
    let each = Fixture::new(&[MANIFEST, ("a.trion", &package("each", ["forbidden", "forbidden", "allowed"]))]).trion(&["verify", "--json"]).json();
    assert_verified(&each);
    assert_eq!(judged(&each, "ONE-OF-TWO"), both("forbidden", "refuted"));
    assert_eq!(judged(&each, "OUTSIDER"), both("forbidden", "refuted"));
    assert_eq!(judged(&each, "BOTH"), both("allowed", "proved"));
}
