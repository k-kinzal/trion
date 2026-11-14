//! The forms that the reading over individuals reads beside the plain
//! statement: an individual that advice or a permission introduces, a
//! relative clause, `no`, a count and a composition.
//!
//! Each expectation is written from the rule of `spec/semantics/core.md`
//! before the run, and each scenario is judged by the reference evaluator
//! and by the formulas of the reading: the test asserts both.

mod common;
use common::*;
use serde_json::Value;

const MANIFEST: (&str, &str) = ("trion.toml", "[package]\nname = \"x\"\n");

fn scenario<'a>(report: &'a Value, name: &str) -> &'a Value {
    report["scenarios"].as_array().unwrap().iter().find(|s| s["name"] == name).unwrap_or_else(|| panic!("no scenario {name}: {}", report["scenarios"]))
}

/// Both judges say `word` of each named scenario.
fn alike(text: &str, expected: &[(&str, &str)]) -> Value {
    let f = Fixture::new(&[MANIFEST, ("a.trion", text)]);
    let report = f.trion(&["verify", "--json", "--properties"]).json();
    for (name, word) in expected {
        let s = scenario(&report, name);
        assert_eq!((s["reference"].as_str().unwrap(), s["generated"].as_str().unwrap()), (*word, *word), "{name}: {s}");
    }
    assert_eq!(report["variations"]["agreed"], report["variations"]["behaviours"], "{}", report["variations"]);
    report
}

/// Both judges say `word` of each named scenario, and the package is verified.
fn agree(text: &str, expected: &[(&str, &str)]) -> Value {
    let report = alike(text, expected);
    let errors: Vec<String> = ["diagnostics", "checker", "opaque"].iter().flat_map(|list| report[*list].as_array().cloned().unwrap_or_default()).filter(|d| d["severity"] == "error").map(|d| format!("{}: {}", d["code"], d["message"])).collect();
    assert!(unverified(&report).is_empty(), "{:?}: {errors:#?}", unverified(&report));
    assert_verified(&report);
    report
}

fn record<'a>(report: &'a Value, statement: &str) -> &'a Value {
    report["individuals"]["meanings"].as_array().unwrap().iter().find(|m| m["statement"] == statement).unwrap_or_else(|| panic!("no record of {statement}: {}", report["individuals"]["outside"]))
}

fn sites(record: &Value) -> Vec<(String, String)> {
    record["variables"].as_array().unwrap().iter().map(|v| (v["key"].as_str().unwrap().to_string(), v["site"].as_str().unwrap().to_string())).collect()
}

const WHO: &str = "individuals user, room\nprimitive system, member, administrator\n\n[KIND-MEMBER]\nEach member is a user.\n\n[KIND-ADMINISTRATOR]\nEach administrator is a user.\n\n[BAN]\nWhile a user is an administrator, the system shall not notify the user.\n";

const ENTERED: &str = "
scenario NO-ADMINISTRATOR:
    given a user U1, a user U2, a room R1
    given U1 is a member of R1.
    given U2 is a member of R1.
    at 0 ms: U1 enters R1.
    expect allowed

scenario ONE-ADMINISTRATOR:
    given a user U1, a user U2, a room R1
    given U1 is a member of R1.
    given U2 is a member of R1.
    given U1 is an administrator.
    at 0 ms: U1 enters R1.
    expect {one}

scenario ALL-ADMINISTRATORS:
    given a user U1, a user U2, a room R1
    given U1 is a member of R1.
    given U2 is a member of R1.
    given U1 is an administrator.
    given U2 is an administrator.
    at 0 ms: U1 enters R1.
    expect forbidden
";

/// Advice chooses its individual as an obligation does. Written from the
/// rule before the run: advice is met where some member of the room may be
/// notified. With one member that the system shall not notify, the other
/// meets it; where each member is one that the system shall not notify, no
/// individual that the advice may choose can be notified, and the
/// behaviour stands against the statements. Advice requires no action: a
/// behaviour without a notification meets it.
#[test]
fn advice_chooses_the_individual_that_it_introduces() {
    let text = format!("{WHO}\n[ADVISE]\nWhen a user enters a room, the system should notify a member of the room.\n{}", ENTERED.replace("{one}", "allowed"));
    let report = agree(&text, &[("NO-ADMINISTRATOR", "allowed"), ("ONE-ADMINISTRATOR", "allowed"), ("ALL-ADMINISTRATORS", "forbidden")]);
    let advise = record(&report, "ADVISE");
    assert_eq!(sites(advise), [("user".to_string(), "condition".to_string()), ("room".to_string(), "condition".to_string()), ("member".to_string(), "chosen".to_string())]);
    assert!(advise["steps"].as_array().unwrap().iter().any(|s| s["rule"] == "variable-some"), "{advise}");
}

/// A permission permits each individual that `a` names. Written from the
/// rule before the run: `may notify a member of the room` permits the
/// notification of each member, so one member that the system shall not
/// notify is permitted and forbidden at once. The statements allow a
/// member that is an administrator, so the package itself is reported as
/// contradictory in that situation.
#[test]
fn a_permission_names_any_individual() {
    let text = format!("{WHO}\n[PERMIT]\nWhen a user enters a room, the system may notify a member of the room.\n{}", ENTERED.replace("{one}", "forbidden"));
    let report = alike(&text, &[("NO-ADMINISTRATOR", "allowed"), ("ONE-ADMINISTRATOR", "forbidden"), ("ALL-ADMINISTRATORS", "forbidden")]);
    assert!(unverified(&report).contains(&"contradiction".to_string()), "{:?}", unverified(&report));
    let permit = record(&report, "PERMIT");
    assert_eq!(sites(permit), [("user".to_string(), "condition".to_string()), ("room".to_string(), "condition".to_string()), ("member".to_string(), "response".to_string())]);
    assert!(permit["steps"].as_array().unwrap().iter().any(|s| s["rule"] == "variable-any"), "{permit}");
}

/// The parts of a record that say what a statement means.
fn meant(record: &Value) -> Value {
    let mut parts = serde_json::Map::new();
    for part in ["variables", "restrictions", "frames", "exception", "force", "choice", "responses", "share"] {
        parts.insert(part.to_string(), record[part].clone());
    }
    Value::Object(parts)
}

/// The record of the statement `[S]` of a package of the given declarations.
fn read_as(head: &str, statement: &str) -> Value {
    let f = Fixture::new(&[MANIFEST, ("a.trion", &format!("{head}\n[S]\n{statement}\n"))]);
    let report = f.trion(&["verify", "--json"]).json();
    meant(record(&report, "S"))
}

const ROOMS: &str = "individuals user, room, message\nprimitive system, member, administrator, mode\n\n[KIND-MEMBER]\nEach member is a user.\n\n[KIND-ADMINISTRATOR]\nEach administrator is a user.\n";

/// A relative clause is a condition of the statement. Written from the
/// rule before the run: the statement with the clause means what the
/// statement with the condition means, so the two have one record, and a
/// behaviour is judged by the condition: the posting of a member is to be
/// stored, the posting of a user that is no member is not.
#[test]
fn a_relative_clause_is_a_condition_of_the_statement() {
    for (with_clause, with_condition) in [
        // A relation, a kind and a state at the moment at which the statement applies.
        ("A user that is a member of a room may post a message to the room.", "While a user is a member of a room, the user may post a message to the room."),
        ("A user that is an administrator may archive each room.", "While a user is an administrator, the user may archive each room."),
        ("The system shall not store a message that is archived.", "While a message is archived, the system shall not store the message."),
        ("When a user posts a message to a room whose mode is maintenance, the system shall reject the message.", "While the mode of a room is maintenance, when a user posts a message to the room, the system shall reject the message."),
        // An event: the statement applies at it.
        ("The system shall store each message that a member of a room posts to the room.", "When a member of a room posts a message to the room, the system shall store the message."),
        ("A user who posts a message shall confirm the message.", "When a user posts a message, the user shall confirm the message."),
    ] {
        assert_eq!(read_as(ROOMS, with_clause), read_as(ROOMS, with_condition), "{with_clause}");
    }
    let text = format!(
        "{ROOMS}\n[STORE]\nThe system shall store each message that a member of a room posts to the room.\n
scenario MEMBER-STORED:
    given a user U1, a room R1, a message M1
    given U1 is a member of R1.
    at 0 ms: U1 posts M1 to R1.
    at 1 seconds: the system stores M1.
    expect allowed

scenario MEMBER-UNSTORED:
    given a user U1, a room R1, a message M1
    given U1 is a member of R1.
    at 0 ms: U1 posts M1 to R1.
    expect forbidden

scenario OUTSIDER-UNSTORED:
    given a user U1, a room R1, a message M1
    at 0 ms: U1 posts M1 to R1.
    expect allowed
"
    );
    let report = agree(&text, &[("MEMBER-STORED", "allowed"), ("MEMBER-UNSTORED", "forbidden"), ("OUTSIDER-UNSTORED", "allowed")]);
    let steps = record(&report, "STORE")["steps"].as_array().unwrap().clone();
    assert!(steps.iter().any(|s| s["rule"] == "variable-that" && s["yields"] == "When a member of a room posts the message to the room"), "{steps:?}");
    // A state: the statement applies at the moments at which it holds.
    let text = format!(
        "{ROOMS}\n[KEEP]\nThe system shall not store a message that is archived.\n
scenario ARCHIVED-STORED:
    given a message M1
    at 0 ms: M1 is archived.
    at 0 ms: the system stores M1.
    expect forbidden

scenario STORED-BEFORE:
    given a message M1
    at 0 ms: the system stores M1.
    at 1 seconds: M1 is archived.
    expect allowed
"
    );
    let report = agree(&text, &[("ARCHIVED-STORED", "forbidden"), ("STORED-BEFORE", "allowed")]);
    let steps = record(&report, "KEEP")["steps"].as_array().unwrap().clone();
    assert!(steps.iter().any(|s| s["rule"] == "variable-that" && s["yields"] == "While the message is archived"), "{steps:?}");
    // What stays outside: an event beside the event of the statement, and
    // a state of an individual that the response chooses.
    for outside in ["When a user enters a room, the system shall log each message that the user posts.", "When a user enters a room, the system shall notify a member that is active."] {
        let other = Fixture::new(&[MANIFEST, ("a.trion", &format!("{ROOMS}\n[S]\n{outside}\n"))]).trion(&["verify", "--json"]).json();
        assert!(unverified(&other).contains(&"UNSUPPORTED_SEMANTICS".to_string()), "{outside}: {:?}", unverified(&other));
    }
    // A relative clause before the verb of a condition ends where its
    // predicate ends. Old behaviour: `that is a` was taken for the whole
    // clause and `member` for the verb of the condition; an article alone
    // is no predicate, so the clause now holds `a member of a room`.
    for (with_clause, with_condition) in [
        ("When a user that is a member of a room posts a message to the room, the system shall store the message within 2 seconds.", "While a user is a member of a room, when the user posts a message to the room, the system shall store the message within 2 seconds."),
        ("When a user that is an administrator posts a message to a room, the system shall store the message.", "While a user is an administrator, when the user posts a message to a room, the system shall store the message."),
    ] {
        assert_eq!(read_as(ROOMS, with_clause), read_as(ROOMS, with_condition), "{with_clause}");
    }
}

/// `no` denies the statement of each individual. Written from the rule
/// before the run: `No user shall archive a room.` is `Each user shall not
/// archive a room.`, and `shall store no message` is `shall not store
/// each message`. (`No user may …` is no sentence: the grammar asks for
/// `shall not`.)
#[test]
fn no_denies_the_statement_of_each_individual() {
    let each = read_as(ROOMS, "Each user shall not archive a room.");
    assert_eq!(read_as(ROOMS, "No user shall archive a room."), each);
    assert_eq!(read_as(ROOMS, "The system shall store no message."), read_as(ROOMS, "The system shall not store each message."));
    let text = format!(
        "{ROOMS}\n[KEEP]\nNo user shall archive a room.\n
scenario ARCHIVED:
    given a user U1, a room R1
    at 0 ms: U1 archives R1.
    expect forbidden

scenario KEPT:
    given a user U1, a room R1
    at 0 ms: U1 enters R1.
    expect allowed
"
    );
    agree(&text, &[("ARCHIVED", "forbidden"), ("KEPT", "allowed")]);
    // `no` beside a denied verb denies twice.
    let twice = Fixture::new(&[MANIFEST, ("a.trion", &format!("{ROOMS}\n[S]\nNo user shall not archive a room.\n"))]).trion(&["verify", "--json"]).json();
    assert!(!twice["outcome"]["verified"].as_bool().unwrap());
}

/// A count names so many different individuals. Written from the rule
/// before the run: `two members` are a member and a second member, and
/// they are two individuals. A room with two members may not be closed and
/// a room with one may; `notify two members of the room` is met by the
/// notification of two members and by nothing less, and a room with one
/// member has no two members to notify.
#[test]
fn a_count_names_different_individuals() {
    assert_eq!(read_as(ROOMS, "While two users are members of a room, the system shall not close the room."), read_as(ROOMS, "While a user is a member of a room and a second user is a member of the room, the system shall not close the room."));
    assert_eq!(
        read_as(ROOMS, "When a user posts a message to a room, the system shall notify two members of the room."),
        read_as(ROOMS, "When a user posts a message to a room, the system shall notify a member of the room and notify a second member of the room.")
    );
    let people = "    given a user U1, a user U2, a user U3, a room R1, a message M1\n";
    let text = format!(
        "{ROOMS}\n[QUORUM]\nWhile two users are members of a room, the system shall not close the room.\n
scenario TWO-MEMBERS-CLOSED:
{people}    given U1 is a member of R1.
    given U2 is a member of R1.
    at 0 ms: the system closes R1.
    expect forbidden

scenario ONE-MEMBER-CLOSED:
{people}    given U1 is a member of R1.
    at 0 ms: the system closes R1.
    expect allowed
"
    );
    let report = agree(&text, &[("TWO-MEMBERS-CLOSED", "forbidden"), ("ONE-MEMBER-CLOSED", "allowed")]);
    // Two variables of one noun are two individuals: of three users, six pairs and no user beside itself.
    let quorum: Vec<&Value> = report["individuals"]["instances"].as_array().unwrap().iter().filter(|i| i["statement"] == "QUORUM").collect();
    assert_eq!(quorum.len(), 3 * 2 * 3, "a user, another user and a room: {quorum:?}");
    assert!(quorum.iter().all(|i| i["binding"][0][1] != i["binding"][2][1]), "{quorum:?}");
    // The statements say that a room has two members: without that, a room
    // with one member is a situation in which no two members can be notified.
    let text = format!(
        "{ROOMS}\n[HAS]\nEach room has at least two members.\n\n[NOTIFY]\nWhen a user posts a message to a room, the system shall notify two members of the room.\n
scenario TWO-NOTIFIED:
{people}    given U1 is a member of R1.
    given U2 is a member of R1.
    given U3 is a member of R1.
    at 0 ms: U3 posts M1 to R1.
    at 1 seconds: the system notifies U1.
    at 1 seconds: the system notifies U3.
    expect allowed

scenario ONE-NOTIFIED:
{people}    given U1 is a member of R1.
    given U2 is a member of R1.
    at 0 ms: U3 posts M1 to R1.
    at 1 seconds: the system notifies U1.
    expect forbidden

scenario ONE-MEMBER:
{people}    given U1 is a member of R1.
    at 0 ms: U3 posts M1 to R1.
    at 1 seconds: the system notifies U1.
    at 1 seconds: the system notifies U2.
    expect forbidden
"
    );
    let report = agree(&text, &[("TWO-NOTIFIED", "allowed"), ("ONE-NOTIFIED", "forbidden"), ("ONE-MEMBER", "forbidden")]);
    // The contract of each instance, with its choices, is derived again.
    assert_eq!(report["derivations"]["contracts"], report["derivations"]["of_instances"], "{}", report["derivations"]);
    // A count in the event, before the subject or in what is forbidden names no individuals one by one.
    for outside in ["When two users post a message to a room, the system shall store the message.", "The system shall not notify two members of a room."] {
        let other = Fixture::new(&[MANIFEST, ("a.trion", &format!("{ROOMS}\n[S]\n{outside}\n"))]).trion(&["verify", "--json"]).json();
        assert!(unverified(&other).contains(&"UNSUPPORTED_SEMANTICS".to_string()), "{outside}: {:?}", unverified(&other));
    }
}

/// A composition of actions. Written from the rule before the run: `in
/// order` requires each action, each strictly after the one before it;
/// `one or more of` requires one of them.
#[test]
fn a_composition_requires_its_actions_as_it_says() {
    let ordered = format!(
        "{ROOMS}\n[KEEP]\nWhen a user posts a message to a room, the system shall perform the following actions in order:\n    validate the message;\n    store the message;\n
scenario IN-ORDER:
    given a user U1, a room R1, a message M1
    at 0 ms: U1 posts M1 to R1.
    at 1 seconds: the system validates M1.
    at 2 seconds: the system stores M1.
    expect allowed

scenario REVERSED:
    given a user U1, a room R1, a message M1
    at 0 ms: U1 posts M1 to R1.
    at 1 seconds: the system stores M1.
    at 2 seconds: the system validates M1.
    expect forbidden

scenario AT-ONCE:
    given a user U1, a room R1, a message M1
    at 0 ms: U1 posts M1 to R1.
    at 1 seconds: the system validates M1.
    at 1 seconds: the system stores M1.
    expect forbidden

scenario ONLY-FIRST:
    given a user U1, a room R1, a message M1
    at 0 ms: U1 posts M1 to R1.
    at 1 seconds: the system validates M1.
    expect forbidden
"
    );
    let report = agree(&ordered, &[("IN-ORDER", "allowed"), ("REVERSED", "forbidden"), ("AT-ONCE", "forbidden"), ("ONLY-FIRST", "forbidden")]);
    assert!(record(&report, "KEEP")["steps"].as_array().unwrap().iter().any(|s| s["rule"] == "choice-order"), "{}", record(&report, "KEEP"));
    let some = format!(
        "{ROOMS}\n[TELL]\nWhen a user posts a message to a room, the system shall perform one or more of the following actions:\n    store the message;\n    reject the message;\n
scenario STORED:
    given a user U1, a room R1, a message M1
    at 0 ms: U1 posts M1 to R1.
    at 1 seconds: the system stores M1.
    expect allowed

scenario BOTH:
    given a user U1, a room R1, a message M1
    at 0 ms: U1 posts M1 to R1.
    at 1 seconds: the system stores M1.
    at 1 seconds: the system rejects M1.
    expect allowed

scenario NEITHER:
    given a user U1, a room R1, a message M1
    at 0 ms: U1 posts M1 to R1.
    expect forbidden
"
    );
    agree(&some, &[("STORED", "allowed"), ("BOTH", "allowed"), ("NEITHER", "forbidden")]);
}
