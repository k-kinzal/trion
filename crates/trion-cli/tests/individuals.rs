//! Statements about individuals: a package that declares the types of its
//! individuals is read over them, one noun names one individual throughout
//! a statement, and a scenario is one concrete behaviour that the reference
//! evaluator and the formulas of the reading judge alike.
//!
//! The expectations are written from `spec/semantics/core.md`. Each test
//! holds the package that it reads.

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

/// What the formulas of the reading say of a behaviour that a judgement
/// does not take: the other word.
fn other(word: &str) -> &'static str {
    if word == "forbidden" { "allowed" } else { "forbidden" }
}

/// The finding of the checker that the reference evaluator and the
/// formulas of the reading judge the scenario `name` differently.
fn differs<'a>(report: &'a Value, name: &str) -> Option<&'a Value> {
    let at = format!("scenario {name}");
    // A variation of the scenario is reported as a behaviour next to it ("on the behaviour of …").
    report["checker"].as_array().unwrap().iter().find(|d| d["code"] == "scenario-differs" && d["message"].as_str().unwrap().starts_with("the reference evaluator finds") && d["refs"].as_array().unwrap().iter().any(|r| r["id"] == at))
}

/// The two words of a difference on the scenario `name`: what the
/// reference evaluator finds of the behaviour, and what the formulas find.
fn difference(report: &Value, name: &str) -> (String, String) {
    let found = differs(report, name).unwrap_or_else(|| panic!("no difference on {name}: {}", report["checker"]));
    let message = found["message"].as_str().unwrap();
    let word = |cue: &str| message.split(cue).nth(1).and_then(|rest| rest.split([' ', ':']).next()).unwrap().to_string();
    (word("finds the behaviour "), word("find it "))
}

/// How the scenario `name` is judged: by the reference evaluator, by the
/// formulas of the reading, and the verdict of its obligation, which asks
/// the formulas for what the scenario expects. A scenario that is not read
/// has no obligation and is `invalid`.
///
/// The formulas say what the scenario expects where its obligation is
/// proved, and the other word where it is refuted; the reference evaluator
/// says the same, unless the checker finds that it differs and names both.
fn judged(report: &Value, name: &str) -> (String, String, String) {
    let obligation = format!("scenario/{name}");
    let Some(stated) = report["obligations"].as_array().unwrap().iter().find(|o| o["name"] == obligation) else {
        let at = format!("scenario {name}");
        let invalid = report["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "scenario-invalid" && d["refs"].as_array().unwrap().iter().any(|r| r["id"] == at));
        let verdict = if invalid { "invalid" } else { "absent" };
        return (verdict.to_string(), verdict.to_string(), verdict.to_string());
    };
    let expected = if stated["proposition"].as_str().unwrap().ends_with("breaks a statement") { "forbidden" } else { "allowed" };
    let verdict = verdicts(report).get(&obligation).cloned().unwrap_or_else(|| "absent".to_string());
    let generated = match verdict.as_str() {
        "proved" => expected,
        "refuted" => other(expected),
        _ => "undecided",
    };
    let reference = match differs(report, name) {
        // "the reference evaluator finds the behaviour W and the formulas …"
        Some(d) => d["message"].as_str().unwrap().split("finds the behaviour ").nth(1).and_then(|rest| rest.split(' ').next()).unwrap().to_string(),
        None => generated.to_string(),
    };
    (reference, generated.to_string(), verdict)
}

/// Both judges say `word`, and the obligation of the scenario, which asks
/// for `word`, is proved.
fn both(word: &str) -> (String, String, String) {
    (word.to_string(), word.to_string(), "proved".to_string())
}

/// Statements whose faulty readings differ on a behaviour: a response
/// to a posting, a prohibition, and a share of the postings.
const FAULTED: &str = r#"
individuals user, message
primitive system
measure postings

[STORE]
When a user sends a message, the system shall store the message within 2 seconds.

[KEEP]
The system shall not delete a message.

[MOST]
When a user posts a message, the system shall store the message within 2 seconds for at least 75 percent of postings.

scenario STORED:
    given a user U1, a message M1
    at 0 ms: U1 sends M1.
    at 1 seconds: the system stores M1.
    expect allowed

scenario DELETED:
    given a message M1
    at 0 ms: the system deletes M1.
    expect forbidden

scenario SECOND:
    given a user U1, a message M1, a message M2
    at 0 ms: U1 sends M2.
    expect forbidden

scenario LATE:
    given a user U1, a message M1
    at 0 ms: U1 sends M1.
    at 3 seconds: the system stores M1.
    expect forbidden

scenario UNANSWERED:
    given a user U1, a message M1, a message M2
    at 0 ms: U1 posts M1.
    at 0 ms: U1 posts M2.
    at 1 seconds: the system stores M1.
    expect forbidden
"#;

/// A translation that is broken on purpose is found: the formulas of the
/// broken reading and the reference evaluator differ on a behaviour.
/// Written from the faults before the run: a response that speaks of
/// another message is not met by the storing of the sent one; a prohibition
/// that forbids nothing allows the deleting; a deadline that ends a second
/// later admits the storing after three seconds; a statement that holds for
/// one message says nothing of the second; and half of 75 percent is met by
/// one of two postings.
#[test]
fn a_seeded_fault_of_the_reading_is_found_by_a_scenario() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", FAULTED)]);
    let sound = f.verify(&["--json"]).json();
    assert_verified(&sound);
    for (name, word) in [("STORED", "allowed"), ("DELETED", "forbidden"), ("SECOND", "forbidden"), ("LATE", "forbidden"), ("UNANSWERED", "forbidden")] {
        assert_eq!(judged(&sound, name), both(word), "{name}");
    }
    for (fault, differs_on) in [("reading-binds-another", "STORED"), ("reading-drops-negation", "DELETED"), ("reading-moves-boundary", "LATE"), ("reading-swaps-quantifier", "SECOND"), ("reading-loosens-share", "UNANSWERED")] {
        let result = verify_with(f.path(), &["--json"], &[("TRION_FAULT", fault)]);
        let report = result.json();
        assert_ne!(result.code, 0, "{fault}");
        // The difference is an error of the conversion: the package is not
        // converted, and no obligation of it is shown as decided.
        assert!(unverified(&report).contains(&"scenario-differs".to_string()), "{fault}: {:?}", unverified(&report));
        assert_eq!(report["conforms"], false, "{fault}");
        assert!(report["proof"].is_null(), "{fault}: {}", report["proof"]);
        let found = differs(&report, differs_on).unwrap_or_else(|| panic!("{fault}: no difference on {differs_on}: {}", report["checker"]));
        let message = found["message"].as_str().unwrap();
        let words: Vec<&str> = ["finds the behaviour ", "find it "].iter().map(|cue| message.split(cue).nth(1).and_then(|rest| rest.split([' ', ':']).next()).unwrap()).collect();
        assert_ne!(words[0], words[1], "{fault}: {message}");
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
    let report = f.verify(&["--json"]).json();
    assert_verified(&report);
    assert_eq!(judged(&report, "SAME"), both("allowed"));
    assert_eq!(judged(&report, "OTHER"), both("forbidden"));
    assert_eq!(judged(&report, "EACH"), both("forbidden"));
    assert_eq!(judged(&report, "ON-TIME"), both("allowed"), "the end of a deadline is included");
    assert_eq!(judged(&report, "LATE"), both("forbidden"));
    assert_eq!(judged(&report, "AGAIN"), both("forbidden"), "a completion before an occurrence does not answer it");
    // Retired: the failing instance of a scenario, with its binding and its
    // moment (`violations`). The conversion reports of the reference
    // evaluator only where it differs from the formulas, and the proof of
    // the scenario names no instance.
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
    let report = f.verify(&["--json"]).json();
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
        let result = f.verify(&["--json"]);
        let report = result.json();
        assert_ne!(result.code, 0, "{sentence}");
        assert_eq!(report["conforms"], false, "{sentence}");
        let unread: Vec<&str> = report["opaque"].as_array().unwrap().iter().chain(report["diagnostics"].as_array().unwrap()).filter(|d| d["code"] == "UNSUPPORTED_SEMANTICS").filter_map(|d| d["message"].as_str()).collect();
        assert!(unread.iter().any(|m| m.contains(part)), "{sentence}: {unread:?}");
    }
}

/// Without a declaration of individuals a package is read as before: one
/// representative of each type, and no instance.
#[test]
fn a_package_that_declares_no_individuals_keeps_its_reading() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", "primitive system, user, message\n\n[A]\nWhen a user sends a message, the system shall store the message.\n")]);
    let report = f.verify(&["--json"]).json();
    assert!(report["individuals"].is_null(), "{}", report["individuals"]);
    // No scenario is an obligation, and the checker reads nothing: no record
    // is derived again and no behaviour is judged by the reference evaluator.
    assert!(report["obligations"].as_array().unwrap().iter().all(|o| o["property"] != "scenario"), "{}", report["obligations"]);
    let checked = &report["checked"];
    assert_eq!((&checked["derivations"]["statements"], &checked["witness"], &checked["scenarios"]), (&json!(0), &Value::Null, &json!(0)), "{checked}");
}

#[test]
fn a_scenario_that_is_not_read_is_judged_of_nothing() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", &format!("{SEND}\nscenario BAD:\n    given a user U1, a message M1\n    at soon: U1 sends M1.\n    expect allowed\n"))]);
    let result = f.verify(&["--json"]);
    let report = result.json();
    assert_ne!(result.code, 0);
    // The scenario is no obligation, and the package is not converted.
    assert!(report["obligations"].as_array().unwrap().iter().all(|o| o["name"] != "scenario/BAD"), "{}", report["obligations"]);
    assert_eq!(report["conforms"], false);
    assert!(report["proof"].is_null(), "{}", report["proof"]);
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
    let report = f.verify(&["--json"]).json();
    assert_verified(&report);
    assert_eq!(judged(&report, "MEMBER"), both("allowed"));
    assert_eq!(judged(&report, "STRANGER"), both("forbidden"));
    assert_eq!(judged(&report, "ELSEWHERE"), both("forbidden"), "the membership of another room is no membership of this one");
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
    let sound = f.verify(&["--json"]).json();
    assert_verified(&sound);
    let derivations = &sound["checked"]["derivations"];
    assert_eq!(derivations["statements"], 1);
    assert_eq!(derivations["contracts"], 9);
    assert_eq!(derivations["of_instances"], 9);
    assert_eq!(derivations["not_derived"], json!([]));
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
        let result = verify_with(f.path(), &["--json"], &[("TRION_FAULT", fault)]);
        let report = result.json();
        assert_ne!(result.code, 0, "{fault}");
        // A refusal is an error of the conversion: nothing is converted or proved.
        assert_eq!(report["conforms"], false, "{fault}");
        let refusals: Vec<&str> = report["checker"].as_array().unwrap().iter().filter(|d| d["code"] == "derivation-refused").filter_map(|d| d["message"].as_str()).collect();
        assert!(refusals.iter().any(|m| m.contains(part)), "{fault}: {refusals:?}");
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
    let report = f.verify(&["--json"]).json();
    assert_verified(&report);
    // One of two within two seconds is half; both within five is all.
    assert_eq!(judged(&report, "ONE-OF-TWO"), both("allowed"));
    // None within two seconds: the bound of [HALF] fails.
    assert_eq!(judged(&report, "NONE-IN-TIME"), both("forbidden"));
    // A posting without a response stays in the population: one of two is no 75 percent.
    assert_eq!(judged(&report, "UNANSWERED"), both("forbidden"));
    // No posting: the behaviour fails nothing, and the share has no value
    // in it: an empty population is no share of 100 percent. `expect
    // undefined` is an obligation only where the reference evaluator finds
    // a share without a value; elsewhere it is `scenario-failed`
    // (`the_shares_of_one_population_within_two_deadlines_are_ordered`).
    assert_eq!(judged(&report, "EMPTY"), both("allowed"));
    // Retired: which statement a scenario fails (`violations`, `1 of 2`),
    // and which shares have no value in it (`undefined`, the evidence of
    // the claim). The conversion reports of the reference evaluator only
    // where it differs from the formulas, and the proof names no statement.
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
    assert_eq!(report["checked"]["derivations"]["contracts"], 18);
    assert_eq!(report["checked"]["derivations"]["not_derived"], json!([]));
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
    let result = f.verify(&["--json"]);
    let report = result.json();
    assert_ne!(result.code, 0);
    assert!(unverified(&report).contains(&"contradiction".to_string()), "{:?}", unverified(&report));
    // The same bound on another population says nothing about this one.
    let other = format!("measure uploads\n{SHARES}\n[FEW]\nWhen a user posts a message, the system shall store the message within 5 seconds for at most 40 percent of uploads.\n");
    let f = Fixture::new(&[MANIFEST, ("a.trion", &other)]);
    assert_verified(&f.verify(&["--json"]).json());
    // `expect undefined` says that a share has no value: a behaviour in which each share has one fails it.
    let valued = format!("{SHARES}\nscenario VALUED:\n    given a user U1, a message M1\n    at 0 ms: U1 posts M1.\n    at 1 seconds: the system stores M1.\n    expect undefined\n");
    let f = Fixture::new(&[MANIFEST, ("a.trion", &valued)]);
    let report = f.verify(&["--json"]).json();
    assert!(unverified(&report).contains(&"scenario-failed".to_string()), "{:?}", unverified(&report));
}

/// The reading of a statement is shown where its author reads the result:
/// in the text of `verify`, in its JSON, and in the document. Each view is
/// made from the same record, and each names the domain and the semantic version.
#[test]
fn the_reading_of_a_statement_is_shown_in_each_view() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", FAULTED)]);
    let expected = [
        "reading [STORE]:",
        "  about: each user; each message",
        "  applies at each occurrence at which: [the user send the message] occurs",
        "  requires: [the system store the message], completed at most 2000 ms after the occurrence (the end included)",
    ];
    // The JSON report holds the lines of each reading.
    let report = f.verify(&["--json"]).json();
    assert_verified(&report);
    let store = report["readings"].as_array().unwrap().iter().find(|r| r["statement"] == "STORE").unwrap();
    let lines: Vec<&str> = store["lines"].as_array().unwrap().iter().map(|l| l.as_str().unwrap()).collect();
    assert_eq!(lines, expected[1..].iter().map(|l| l.trim_start()).collect::<Vec<_>>());
    assert_eq!(store["version"], "0.1.0");
    // Three statements; three users and three messages give nine instances
    // of STORE and of MOST, and three messages three of KEEP: each record
    // and each contract is derived again and agrees.
    let derivations = &report["checked"]["derivations"];
    assert_eq!((&derivations["statements"], &derivations["of_statements"], &derivations["contracts"], &derivations["of_instances"]), (&json!(3), &json!(3), &json!(21), &json!(21)), "{derivations}");
    // The document shows the readings in its status; the judgements of the
    // scenarios are results of the proof, and the document claims none.
    let html = f.document(&[]).stdout;
    assert!(html.contains("readings over individuals"), "the document holds no readings");
    assert!(html.contains("[STORE] When a user sends a message, the system shall store the message within 2 seconds."), "the document does not set the sentence beside its reading");
    assert!(!html.contains("scenario LATE: forbidden for the reference evaluator"));
    assert!(html.contains("individuals: semantic version 0.1.0; domains of 3 individuals of each declared type"));
    // The text states the bound of every result, and that none holds beyond it.
    let text = f.verify(&[]).stdout;
    assert!(text.contains("within traces of 3 moments, domains of 3 individuals:") && text.contains("no result holds beyond its bound"), "{text}");
    assert!(text.trim_end().ends_with("\nproved"), "{text}");
    // Retired: the judgement of each scenario by both judges in the text
    // (`scenario LATE: forbidden for the reference evaluator, …`, with the
    // shares without a value); a scenario is an obligation, and its result
    // is the verdict of the proof.
    // The text of the conversion shows each reading, as the JSON and the document do.
    assert!(text.contains("individuals: semantic version 0.1.0; domains of 3 individuals of each declared type (message, user)"), "{text}");
    assert!(text.contains(&expected.join("\n")), "{text}");
    assert!(text.contains("reading [KEEP]:\n  about: each message\n  applies: to the behaviour as a whole\n  forbids: [the system delete the message]"), "{text}");
    assert!(text.contains("  of: at least 75.000 percent of the activations of this statement in one behaviour (`postings`)"), "{text}");
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
    let agree = |report: &Value, name: &str, word: &str| assert_eq!(judged(report, name), both(word), "{name}");
    // At least 75 percent: three of four meet it, two of four and none of four do not.
    let lower = Fixture::new(&[MANIFEST, ("a.trion", &package("[MOST]\nWhen a user posts a message, the system shall store the message within 2 seconds for at least 75 percent of postings.", ["allowed", "forbidden", "forbidden"]))]);
    let report = lower.verify(&["--json"]).json();
    assert_verified(&report);
    agree(&report, "THREE", "allowed");
    agree(&report, "TWO", "forbidden");
    agree(&report, "NONE", "forbidden");
    // At most 50 percent: three of four exceed it, two of four and none of four do not.
    let upper = Fixture::new(&[MANIFEST, ("a.trion", &package("[FEW]\nWhen a user posts a message, the system shall store the message within 2 seconds for at most 50 percent of postings.", ["forbidden", "allowed", "allowed"]))]);
    let report = upper.verify(&["--json"]).json();
    assert_verified(&report);
    agree(&report, "THREE", "forbidden");
    agree(&report, "TWO", "allowed");
    agree(&report, "NONE", "allowed");
    // A bound that is half of what the statement says is refused by the
    // check of the reading, and a scenario tells it from the meaning.
    let result = verify_with(lower.path(), &["--json"], &[("TRION_FAULT", "reading-loosens-share")]);
    let report = result.json();
    assert_ne!(result.code, 0);
    let refusals: Vec<&str> = report["checker"].as_array().unwrap().iter().filter(|d| d["code"] == "derivation-refused").filter_map(|d| d["message"].as_str()).collect();
    assert!(refusals.iter().any(|m| m.contains("the bound of the contract")), "{refusals:?}");
    assert_eq!(difference(&report, "TWO"), ("forbidden".to_string(), "allowed".to_string()));
    assert_eq!(report["conforms"], false);
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
    let report = f.verify(&["--json"]).json();
    assert_verified(&report);
    for (name, word) in [("NINETY-NINE", "allowed"), ("NINETY-EIGHT", "forbidden")] {
        assert_eq!(judged(&report, name), both(word), "{name}");
    }
    // Retired: the count that the reference evaluator gives for a failed
    // share (`98 of 100 `postings` are answered`); the conversion reports of
    // the reference evaluator only where it differs from the formulas.
    // A reading with half the bound takes ninety-eight of a hundred for enough: the scenario tells it from the meaning.
    let result = verify_with(f.path(), &["--json"], &[("TRION_FAULT", "reading-loosens-share")]);
    assert_ne!(result.code, 0);
    assert_eq!(difference(&result.json(), "NINETY-EIGHT"), ("forbidden".to_string(), "allowed".to_string()));
}

/// A measure names one population. Two statements that apply under other
/// conditions count other activations: one name for both would order the
/// shares of two populations as the shares of one.
#[test]
fn one_measure_names_the_activations_of_one_condition() {
    const HEAD: &str = "individuals user, message\nprimitive system\nmeasure postings\nmeasure deletions\n";
    let posting = "[A]\nWhen a user posts a message, the system shall store the message within 2 seconds for at least 50 percent of postings.\n";
    let other = Fixture::new(&[MANIFEST, ("a.trion", &format!("{HEAD}\n{posting}\n[B]\nWhen a user deletes a message, the system shall store the message within 5 seconds for at most 40 percent of postings.\n"))]);
    let result = other.verify(&["--json"]);
    let report = result.json();
    assert_ne!(result.code, 0);
    let named = report["opaque"].as_array().unwrap().iter().any(|d| d["code"] == "UNSUPPORTED_SEMANTICS" && d["message"].as_str().unwrap().contains("the measure `postings` names the activations of [A]"));
    assert!(named, "{}", report["opaque"]);
    // With a measure of its own the second statement counts its own population, and both bounds hold.
    let apart = Fixture::new(&[MANIFEST, ("a.trion", &format!("{HEAD}\n{posting}\n[B]\nWhen a user deletes a message, the system shall store the message within 5 seconds for at most 40 percent of deletions.\n"))]);
    assert_verified(&apart.verify(&["--json"]).json());
}

/// The claim that a behaviour keeps every contract rests on a model of
/// formulas. The model is written down as a complete behaviour in the terms
/// of the statements, and the reference evaluator judges it.
#[test]
fn the_behaviour_behind_contract_sat_is_judged_by_the_reference_evaluator() {
    let f = Fixture::new(&[MANIFEST, ("a.trion", SEND)]);
    let report = f.verify(&["--json"]).json();
    assert_verified(&report);
    assert_eq!(report["checked"]["witness"], "accepted", "{}", report["checked"]);
    // Retired: the behaviour of the witness itself (a sending at the first
    // moment and the storing of that message at a later one, and nothing
    // else) and the claim `contract_sat` that cited it. The conversion
    // states only how the reference evaluator judges the witness.
    // A reading that takes a later completion for one in time accepts a
    // behaviour that the statement refuses: the claim is an error, and the
    // package is not verified.
    let late = repo_root().join("crates/trion-cli/fixtures/codes/witness-refused/package");
    let result = verify_with(&late, &["--json"], &[("TRION_FAULT", "reading-moves-boundary")]);
    let report = result.json();
    assert_ne!(result.code, 0);
    assert!(unverified(&report).contains(&"witness-refused".to_string()), "{:?}", unverified(&report));
    assert_eq!(report["checked"]["witness"], "refused");
    // The refusal is an error of the conversion: nothing is proved.
    assert_eq!(report["conforms"], false);
    assert!(report["proof"].is_null(), "{}", report["proof"]);
    // Without the fault the same package is verified, with moments that the deadline admits.
    let sound = verify_in(&late, &["--json"]).json();
    assert_verified(&sound);
    assert_eq!(sound["checked"]["witness"], "accepted");
}

/// A reading that differs from the meaning only on a behaviour that no
/// scenario states is found on the behaviours next to the scenarios.
#[test]
fn the_reading_and_the_meaning_agree_next_to_the_scenarios() {
    let package = format!("{SEND}\nscenario STORED:\n    given a user U1, a message M1, a message M2\n    at 0 ms: U1 sends M1.\n    at 1 seconds: the system stores M1.\n    expect allowed\n");
    let f = Fixture::new(&[MANIFEST, ("a.trion", &package)]);
    let report = f.verify(&["--json", "--properties"]).json();
    assert_verified(&report);
    let variations = &report["checked"]["variations"];
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
    // Without `--properties` the variations are not made, and the report says so.
    let plain = f.verify(&["--json"]).json();
    assert_eq!(plain["checked"]["variations"], Value::Null);
    // The stated scenario stores the message after one second, which a
    // deadline of two seconds and one of three both admit: the scenario
    // does not tell a moved deadline from the stated one. The variation
    // with the storing later by a deadline does.
    let result = verify_with(f.path(), &["--json", "--properties"], &[("TRION_FAULT", "reading-moves-boundary")]);
    let report = result.json();
    assert_ne!(result.code, 0);
    // The stated scenario is judged alike by both.
    assert!(differs(&report, "STORED").is_none(), "{}", report["checker"]);
    let found: Vec<&str> = report["checker"].as_array().unwrap().iter().filter(|d| d["code"] == "scenario-differs").filter_map(|d| d["message"].as_str()).collect();
    assert!(found.iter().any(|m| m.contains("each later moment 2000 ms later") && m.contains("finds the behaviour forbidden and the formulas of the reading find it allowed")), "{found:?}");
    // The difference is an error of the conversion.
    assert_eq!(report["conforms"], false);
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
    let report = f.verify(&["--json", "--properties"]).json();
    assert_verified(&report);
    for (name, word) in [("MADE", "allowed"), ("NONE", "forbidden"), ("LATE", "forbidden"), ("ANY", "allowed"), ("ONE-FOR-TWO", "allowed")] {
        assert_eq!(judged(&report, name), both(word), "{name}");
    }
    // The reading and the meaning agree next to these scenarios as well.
    let variations = &report["checked"]["variations"];
    assert!(variations["behaviours"].as_u64().is_some(), "the variations were not made: {}", report["checked"]);
    assert_eq!(variations["agreed"], variations["behaviours"], "{variations}");
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
    let other = Fixture::new(&[MANIFEST, ("a.trion", "individuals user, message, ticket\nprimitive system\n\n[T]\nWhen a user reports a message, the system shall create the ticket.\n")]).verify(&["--json"]).json();
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
    let some = Fixture::new(&[MANIFEST, ("a.trion", &package("a", ["allowed", "forbidden", "allowed"]))]).verify(&["--json"]).json();
    assert_verified(&some);
    assert_eq!(judged(&some, "ONE-OF-TWO"), both("allowed"));
    assert_eq!(judged(&some, "OUTSIDER"), both("forbidden"));
    assert_eq!(judged(&some, "BOTH"), both("allowed"));
    // Each member: one of the two is not enough.
    // A reading that lets the response choose any user accepts the
    // notifying of one who is no member: the scenario OUTSIDER tells it
    // from the meaning.
    let f = Fixture::new(&[MANIFEST, ("a.trion", &package("a", ["allowed", "forbidden", "allowed"]))]);
    let result = verify_with(f.path(), &["--json"], &[("TRION_FAULT", "reading-chooses-any")]);
    let faulty = result.json();
    assert_ne!(result.code, 0);
    assert_eq!(difference(&faulty, "OUTSIDER"), ("forbidden".to_string(), "allowed".to_string()));
    assert_eq!(faulty["conforms"], false);
    // In OUTSIDER the one member is not notified, so that fails as well.
    let each = Fixture::new(&[MANIFEST, ("a.trion", &package("each", ["forbidden", "forbidden", "allowed"]))]).verify(&["--json"]).json();
    assert_verified(&each);
    assert_eq!(judged(&each, "ONE-OF-TWO"), both("forbidden"));
    assert_eq!(judged(&each, "OUTSIDER"), both("forbidden"));
    assert_eq!(judged(&each, "BOTH"), both("allowed"));
}
