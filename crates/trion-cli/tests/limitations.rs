//! Limits of the reading that are crossed. Each test runs its reproducer as
//! the body of `namespace p.x:` in a package `p`.
//!
//! A statement that shares no term with another one is ungrounded, and an
//! ungrounded package is not converted; where a reproducer is ungrounded only
//! because it is short, its terms are declared primitives.
//!
//! Retired with the engine of `trioc check`, because the proof of the MMT
//! form does not state them: the elements, derivation and condition of a
//! conflict, the explanation of coverage, the assumptions of a result, the
//! list of situations examined, the advice in the message of a conflict, and
//! a count of errors in the text. A contradiction names the requirements
//! that cannot all be kept, not the definitions and descriptions that they
//! are read with; an incompatibility names no statement.

mod common;
use common::*;
use serde_json::Value;

fn package(body: &str) -> Fixture {
    let indented: String = body.lines().map(|line| if line.is_empty() { "\n".to_string() } else { format!("    {line}\n") }).collect();
    Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\nentry = \"a.trion\"\n"), ("a.trion", &format!("package p edition \"1\"\n\nnamespace p.x:\n{indented}"))])
}

fn check(body: &str) -> Value {
    package(body).verify(&["--json"]).json()
}

/// The verdict of an obligation of a report.
fn verdict(report: &Value, obligation: &str) -> String {
    verdicts(report).get(obligation).cloned().unwrap_or_else(|| "absent".to_string())
}

#[test]
fn a_state_change_is_no_contradiction() {
    let report = check("primitive door, open, closed\n[T1]\nWhen the door is open, the door shall become closed.\n");
    assert!(analysis_codes(&report).is_empty(), "{report}");
    assert_eq!(verdict(&report, "consistency"), "proved", "{report}");
    // The exclusivity of values still holds within one state. The door is
    // the system's, and a system that never opens it keeps both vacuously
    // (AGENTS.md, limit 2): the environment must be able to bring the
    // trigger about.
    let two = "primitive door, open, closed\n[T1]\nWhen the door is open, the door shall become closed.\n\n[T2]\nWhen the door is open, the door shall become locked.\n";
    assert_eq!(verdict(&check(two), "consistency"), "proved");
    let knocked = check(&format!("{two}\n[O]\nWhen the user knocks, the door shall be open.\n"));
    assert!(analysis_codes(&knocked).contains(&"contradiction".to_string()), "{knocked}");
}

#[test]
fn an_action_raises_the_event_that_waits_for_it() {
    let f = package("[B1]\nThe API shall store the message.\n\n[B2]\nWhen the API stores the message, the API shall log the message.\n");
    let smt = f.inspect(&["model", "--smt2"]).stdout;
    // The output is the decided formulas: the axiom stands at each moment of the trace.
    assert!(asserts_subterm(&smt, "(=> |Act(x::API_store message@0)| |Event(x::API store message@0)|)"), "{smt}");
    let model = f.inspect(&["model"]).stdout;
    assert!(model.contains("assume:    Event(x::API store message)"), "{model}");
    // The event holds when the action completes, so B1 makes B2 owe the log.
    let report = check("[B1]\nThe API shall store the message.\n\n[B2]\nWhen the API stores the message, the API shall log the message.\n\n[B3]\nThe API shall not log the message.\n");
    assert!(report_codes(&report).contains(&"contradiction".to_string()), "{report}");
}

#[test]
fn a_deadline_and_a_delay_of_one_action_are_one_quantity() {
    let report = check("[D1]\nWhen a request arrives, the API shall respond within 5 seconds.\n\n[D2]\nWhen a request arrives, the API shall respond after 10 seconds.\n");
    assert_eq!(report_codes(&report), ["contradiction"], "{report}");
    let compatible = check("[D1]\nWhen a request arrives, the API shall respond within 5 seconds.\n\n[D2]\nWhen a request arrives, the API shall respond after 2 seconds.\n");
    assert!(report_codes(&compatible).is_empty(), "{compatible}");
}

#[test]
fn time_is_read_from_the_sentence_and_not_kept_in_the_action_name() {
    let f = package("primitive API, request, message, user\n[L1]\nWhen a request arrives, the API shall eventually respond.\n\n[L2]\nThe API shall retain the message until the user deletes the message.\n");
    let report = f.verify(&["--json"]).json();
    assert!(analysis_codes(&report).is_empty(), "{report}");
    let model = f.inspect(&["model"]).stdout;
    assert!(model.contains("Act(x::API|respond)"), "{model}");
    assert!(model.contains("Act(x::API|retain message)"), "{model}");
    assert!(!model.contains("eventually respond") && !model.contains("retain message until"), "{model}");
    assert!(model.contains("eventually complete(x::API|respond)"), "{model}");
    assert!(model.contains("until event Event(x::user delete message): the response holds at every moment before the first moment of the event"), "{model}");
    // The result is a result about traces of a stated length.
    assert_eq!(report["proof"]["subject"]["moments"], 3, "{report}");
    // `eventually respond` and `respond` are one action: a ban on it conflicts.
    let banned = check("[L1]\nWhen a request arrives, the API shall eventually respond.\n\n[N]\nThe API shall not respond.\n");
    assert_eq!(analysis_codes(&banned), ["contradiction"], "{banned}");
    // `retain … until …` and `retain` are one action too.
    let dropped = check("[L2]\nThe API shall retain the message until the user deletes the message.\n\n[N]\nThe API shall not retain the message.\n");
    assert_eq!(analysis_codes(&dropped), ["contradiction"], "{dropped}");
}

#[test]
fn a_no_subject_denies_its_description() {
    let f = package("[U3]\nNo member of a room is the owner of the room.\n");
    let model = f.inspect(&["model"]).stdout;
    assert!(model.contains("guarantee: ¬Dom(x::room member, room owner)"), "{model}");
    // The statement now contradicts its opposite. Both describe rooms, which
    // no statement gives to the system: together they allow no environment.
    let report = check("[U3]\nNo member of a room is the owner of the room.\n\n[U4]\nThe member of a room is the owner of the room.\n");
    assert_eq!(report_codes(&report), ["incompatible"], "{report}");
    // `No` and `never` together affirm.
    let double = package("[U5]\nNo member of a room is never the owner of the room.\n").inspect(&["model"]).stdout;
    assert!(double.contains("guarantee: Dom(x::room member, room owner)"), "{double}");
}

#[test]
fn a_list_of_objects_is_one_action_for_each_object() {
    let a1 = "primitive language, sentence composition, shared condition, diagram notation\n[A1]\nThe language shall support sentence composition, shared conditions, and diagram notation.\n";
    let report = check(&format!("{a1}\n[A2]\nThe language shall not support sentence composition.\n"));
    assert_eq!(report_codes(&report), ["contradiction"], "{report}");
    // The list abbreviates one requirement for each object, and the conflict
    // names the requirement that is denied: the first part of the statement.
    let conflict = report["diagnostics"].as_array().unwrap().iter().find(|d| d["code"] == "contradiction").unwrap();
    let refs = conflict["refs"].as_array().unwrap();
    assert!(refs.iter().any(|r| r["id"] == "A1/1" && r["text"] == "The language shall support sentence composition."), "{conflict}");
    assert!(!refs.iter().any(|r| r["id"] == "A1/2" || r["id"] == "A1/3"), "{conflict}");
    let model = package(a1).inspect(&["model"]).stdout;
    for object in ["sentence composition", "shared condition", "diagram notation"] {
        assert!(model.contains(&format!("Act(x::language|support {object})")), "{model}");
    }
    // Every item counts, the last one too.
    assert_eq!(report_codes(&check(&format!("{a1}\n[A3]\nThe language shall not support diagram notation.\n"))), ["contradiction"]);
    // A required choice between objects is met by one of them.
    let choice = "[C1]\nThe API shall accept a token or a password.\n";
    assert!(!report_codes(&check(&format!("{choice}\n[C2]\nThe API shall not accept a token.\n"))).contains(&"contradiction".to_string()));
    assert_eq!(report_codes(&check(&format!("{choice}\n[C2]\nThe API shall not accept a token.\n\n[C3]\nThe API shall not accept a password.\n"))), ["contradiction"]);
    // A prohibition and a permission reach each object.
    assert_eq!(report_codes(&check("primitive API, token, password\n[D1]\nThe API shall not store a token or a password.\n\n[D2]\nThe API shall store a password.\n")), ["contradiction"]);
    assert_eq!(report_codes(&check("primitive API, token, password\n[E1]\nThe API may store a token and a password.\n\n[E2]\nThe API shall not store a password.\n")), ["contradiction"]);
    // An item of a composition and a relation read their lists the same way.
    let list = "[F1]\nThe API shall perform all of the following actions:\n    log the call and the caller;\n\n[F2]\nThe API shall not log the caller.\n";
    assert_eq!(report_codes(&check(list)), ["contradiction"]);
    let relation = package("[G1]\nEach room has a name and an owner.\n").inspect(&["model"]).stdout;
    assert!(relation.contains("Act(x::room|has name)") && relation.contains("Act(x::room|has owner)"), "{relation}");
}

#[test]
fn a_part_without_a_reading_is_reported() {
    // A comparison with one quantity is read as arithmetic; a list on its right side is not.
    let report = check("[V1]\nThe timeout is less than the retry interval and the limit.\n\n[H1]\nThe API shall use some key.\n\n[R1]\nThe API shall keep the message because the user sent it.\n\n[S1]\nThe API shall stop.\n");
    let opaque = report["opaque"].as_array().unwrap();
    let said = |part: &str| opaque.iter().find(|d| d["message"].as_str().unwrap().contains(part)).unwrap_or_else(|| panic!("{part}: {report}"));
    assert_eq!(said("`less than` is a comparison")["refs"][0]["id"], "V1");
    assert!(said("`less than` is a comparison")["message"].as_str().unwrap().contains("that is no bound of one quantity"));
    assert_eq!(said("`some` is a quantifier")["refs"][0]["id"], "H1");
    assert_eq!(said("`because` is a conjunction")["refs"][0]["id"], "R1");
    // An unread part is an error: nothing passes a check unread.
    assert!(opaque.iter().all(|d| d["code"] == "UNSUPPORTED_SEMANTICS" && d["severity"] == "error"), "{report}");
    // A statement that is read in full is not listed.
    assert!(opaque.iter().all(|d| d["refs"][0]["id"] != "S1"));
    // An action is reported once, however many atoms name it.
    assert_eq!(opaque.iter().filter(|d| d["refs"][0]["id"] == "H1").count(), 1);
    let text = package("[V1]\nThe timeout is less than the retry interval and the limit.\n").verify(&[]);
    assert_eq!(text.code, 1);
    assert!(text.stdout.contains("error[UNSUPPORTED_SEMANTICS]"), "{}", text.stdout);
}

#[test]
fn a_statement_that_constrains_nothing_is_reported() {
    let l1 = "[L1]\nThe trion language shall build on a controlled natural language.\n";
    let ids = |report: &Value| report["ungrounded"].as_array().unwrap().iter().map(|d| d["refs"][0]["id"].as_str().unwrap().to_string()).collect::<Vec<_>>();
    let report = check(l1);
    assert_eq!(ids(&report), ["L1"], "{report}");
    let said = report["ungrounded"][0]["message"].as_str().unwrap();
    assert!(said.contains("excludes no interpretation") && said.contains("`x::controlled natural language`") && said.contains("`x::trion language`"), "{said}");
    assert_eq!(report["ungrounded"][0]["code"], "ungrounded");
    // An ungrounded statement does not conform: nothing of the package is
    // converted or proved, and nothing is left `unknown` in its place.
    assert!(report["proof"].is_null(), "{report}");
    assert_eq!(unverified(&report), ["ungrounded"], "{report}");
    assert!(analysis_codes(&report).is_empty());
    // The table of the entry: only the literal negation shares an atom with A1.
    let a1 = "[A1]\nThe language shall support sentence composition.\n";
    assert_eq!(ids(&check(a1)), ["A1"]);
    let negation = check(&format!("{a1}\n[A2]\nThe language shall not support sentence composition.\n"));
    assert_eq!(analysis_codes(&negation), ["contradiction"]);
    assert!(ids(&negation).is_empty(), "{negation}");
    for other in ["The language shall not support composed sentences.", "The language shall reject sentence composition.", "Each statement shall contain exactly one action."] {
        let report = check(&format!("{a1}\n[A2]\n{other}\n"));
        assert!(analysis_codes(&report).is_empty(), "{other}");
        assert_eq!(ids(&report), ["A1", "A2"], "{other}: {report}");
    }
    // A kind is not a meaning: a `term` declaration grounds nothing.
    assert_eq!(ids(&check(&format!("term trion language: entity\n{l1}"))), ["L1"]);
    // A primitive is accepted without a definition, and a definition grounds its term.
    let grounded = format!("primitive controlled natural language\nThe trion language means the language of the trion package.\n{l1}");
    assert!(ids(&check(&grounded)).is_empty(), "{}", check(&grounded));
    // A statement without normative force describes its terms: it says which situations can occur.
    let described = format!("The trion language is a controlled natural language.\n{l1}");
    assert!(ids(&check(&described)).is_empty(), "{}", check(&described));
    // Alone it is no statement that constrains nothing: it constrains the situations.
    assert!(ids(&check("[D]\nEach room has exactly one owner.\n")).is_empty());
    // Each statement that constrains nothing is an error of the check.
    let many: String = (0..12).map(|i| format!("[N{i}]\nThe part{i} shall hold the item{i}.\n\n")).collect();
    let counted = package(&many).verify(&[]).stdout;
    assert_eq!(counted.matches("error[ungrounded]").count(), 12, "{counted}");
    assert!(counted.trim_end().ends_with("does not conform"), "{counted}");
    assert_eq!(package(&many).verify(&[]).code, 1);
}

#[test]
fn two_quantities_are_compared_with_each_other() {
    let body = "[V1]\nThe timeout is less than the retry interval.\n\n[V2]\nThe retry interval is at most 5 seconds.\n\n[V3]\nThe timeout is at least 10 seconds.\n";
    // The statements describe quantities that no statement gives to the
    // system: they are assumptions, and together they allow no environment.
    let report = check(body);
    assert_eq!(report_codes(&report), ["incompatible"], "{report}");
    assert_eq!(verdict(&report, "compatibility"), "refuted");
    // The relation is an atom over both quantities, not a value with a long name.
    let model = package(body).inspect(&["model"]).stdout;
    assert!(model.contains("guarantee: x::timeout − x::retry interval < 0 ms"), "{model}");
    assert!(!model.contains("Dom(x::timeout, less than retry interval)"), "{model}");
    // All three statements are needed: any two of them hold together.
    for kept in ["[V1]\nThe timeout is less than the retry interval.\n\n[V2]\nThe retry interval is at most 5 seconds.\n", "[V2]\nThe retry interval is at most 5 seconds.\n\n[V3]\nThe timeout is at least 10 seconds.\n"] {
        let report = check(kept);
        assert!(report_codes(&report).is_empty(), "{report}");
        assert_eq!(verdict(&report, "compatibility"), "proved");
    }
    // With room between the bounds, the three statements hold together.
    let report = check(&body.replace("at least 10 seconds", "at least 3 seconds"));
    assert!(report_codes(&report).is_empty(), "{report}");
    // An external solver reads the same relation.
    let smt = package(body).inspect(&["model", "--smt2"]).stdout;
    assert!(asserts_subterm(&smt, "(< (+ (* (- 1) |num:x::retry interval@0:ms|) |num:x::timeout@0:ms|) 0)"), "{smt}");
}

#[test]
fn sums_multiples_and_differences_of_quantities_are_read() {
    // The quantities are described and no statement gives them to the
    // system: bounds that cannot all hold allow no environment.
    let contradicts = |body: &str| {
        let report = check(body);
        assert_eq!(analysis_codes(&report), ["incompatible"], "{body}: {report}");
    };
    contradicts("[A]\nThe timeout is at most twice the limit.\n\n[B]\nThe limit is at most 5 seconds.\n\n[C]\nThe timeout is at least 11 seconds.\n");
    contradicts("[A]\nThe margin is at least half the limit.\n\n[B]\nThe limit is at least 10 seconds.\n\n[C]\nThe margin is at most 4 seconds.\n");
    contradicts("[A]\nThe quota is at most 3 times the limit.\n\n[B]\nThe limit is at most 2 seconds.\n\n[C]\nThe quota is at least 7 seconds.\n");
    contradicts("[A]\nThe timeout plus the delay is at most 30 seconds.\n\n[B]\nThe timeout is at least 20 seconds.\n\n[C]\nThe delay is at least 15 seconds.\n");
    contradicts("[A]\nThe timeout exceeds the limit by 5 seconds.\n\n[B]\nThe limit is at least 10 seconds.\n\n[C]\nThe timeout is at most 12 seconds.\n");
    contradicts("[A]\nThe timeout exceeds the retry interval.\n\n[B]\nThe retry interval is at least 10 seconds.\n\n[C]\nThe timeout is at most 5 seconds.\n");
    contradicts("[A]\nThe size is between the minimum and the maximum.\n\n[B]\nThe minimum is at least 10 MB.\n\n[C]\nThe size is at most 5 MB.\n");
    contradicts("[A]\nThe first bound is less than the second bound.\n\n[B]\nThe second bound is less than the third bound.\n\n[C]\nThe third bound is less than the first bound.\n");
    // Each form has a solution when its bounds leave room.
    for body in [
        "[A]\nThe timeout is at most twice the limit.\n\n[B]\nThe limit is at most 5 seconds.\n\n[C]\nThe timeout is at least 10 seconds.\n",
        "[A]\nThe timeout plus the delay is at most 30 seconds.\n\n[B]\nThe timeout is at least 20 seconds.\n\n[C]\nThe delay is at least 10 seconds.\n",
        "[A]\nThe timeout exceeds the limit by 5 seconds.\n\n[B]\nThe limit is at least 10 seconds.\n\n[C]\nThe timeout is at most 15 seconds.\n",
    ] {
        let report = check(body);
        assert!(analysis_codes(&report).is_empty(), "{body}: {report}");
        assert_eq!(verdict(&report, "compatibility"), "proved", "{body}");
    }
    // A relation in a condition decides which statements meet.
    // The prohibition holds while the relation holds, and nothing says that
    // the relation ever fails: the two statements cannot both be kept there.
    let met = check("[A]\nWhile the load is at most the capacity, the API shall not reject requests.\n\n[B]\nThe API shall reject requests.\n");
    assert_eq!(analysis_codes(&met), ["contradiction"], "{met}");
    let apart = check("[A]\nWhile the load is greater than the capacity, the API shall reject requests.\n\n[B]\nWhile the load is at most the capacity, the API shall not reject requests.\n");
    assert!(analysis_codes(&apart).is_empty(), "{apart}");
}

#[test]
fn quantities_of_one_comparison_share_one_unit() {
    let report = check("[A]\nThe timeout is less than the size.\n\n[B]\nThe timeout is at most 5 seconds.\n\n[C]\nThe size is at least 10 bytes.\n");
    assert_eq!(report_codes(&report), ["unit-mismatch"], "{report}");
    // A relation carries the unit of one quantity to the other.
    let model = package("[A]\nThe timeout is less than the retry interval.\n\n[B]\nThe retry interval is at most 5 minutes.\n").inspect(&["model"]).stdout;
    assert!(model.contains("x::timeout − x::retry interval < 0 ms"), "{model}");
}

#[test]
fn the_duration_of_an_action_is_at_most_its_elapsed_time() {
    let report = check("[A]\nWhen a request arrives, the API shall process the request within 5 seconds.\n\n[B]\nWhen a request arrives, the API shall process the request for at least 10 seconds.\n");
    assert!(report_codes(&report).contains(&"contradiction".to_string()), "{report}");
    let fits = check("[A]\nWhen a request arrives, the API shall process the request within 5 seconds.\n\n[B]\nWhen a request arrives, the API shall process the request for at least 2 seconds.\n");
    assert!(report_codes(&fits).is_empty(), "{fits}");
}

/// The errors of a report, of the conversion and of the proof, with the
/// identifiers of the statements that each one names.
fn m_errors(report: &Value) -> Vec<(String, Vec<String>)> {
    ["diagnostics", "opaque", "ungrounded", "inexpressible", "checker"]
        .iter()
        .flat_map(|list| report[*list].as_array().cloned().unwrap_or_default())
        .filter(|d| d["severity"] == "error")
        .map(|d| (d["code"].as_str().unwrap().to_string(), d["refs"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap().to_string()).collect()))
        .collect()
}

/// `true` when the statement `id`, or a part of it, is a requirement: a
/// contract that the system is responsible for.
fn required(report: &Value, id: &str) -> bool {
    report["contracts"].as_array().unwrap().iter().any(|c| (c["statement"]["id"] == id || c["statement"]["id"].as_str().unwrap().starts_with(&format!("{id}/"))) && matches!(c["role"].as_str(), Some("guarantee" | "permission")))
}

/// The statements `members` cannot all hold, and the finding names exactly
/// them: the requirements together with the definitions and descriptions
/// that they are read with. Where requirements are among them, no system
/// keeps them (a contradiction); where none is a requirement, the
/// descriptions allow no environment (an incompatibility).
fn m_conflict(body: &str, members: &[&str]) {
    let report = check(body);
    let errors = m_errors(&report);
    assert_eq!(errors.len(), 1, "{body}: {report}");
    let requirements = members.iter().any(|m| required(&report, m));
    if requirements {
        assert_eq!(errors[0].0, "contradiction", "{report}");
    } else {
        assert_eq!(errors[0].0, "incompatible", "{report}");
        assert_eq!(verdict(&report, "compatibility"), "refuted", "{report}");
    }
    let mut named = errors[0].1.clone();
    named.sort();
    let mut expected: Vec<String> = members.iter().map(|m| m.to_string()).collect();
    expected.sort();
    assert_eq!(named, expected, "{body}: {report}");
}

fn m_consistent(body: &str) {
    let report = check(body);
    assert!(m_errors(&report).is_empty(), "{body}: {report}");
    assert_eq!(verdict(&report, "consistency"), "proved", "{body}");
    assert_eq!(verdict(&report, "compatibility"), "proved", "{body}");
}

#[test]
fn a_definition_carries_a_conflict_to_the_defined_term() {
    // The reproducer of entry 10: a prohibition on users reaches guests.
    m_conflict("[F1]\nA guest means a user without an account.\n\n[F2]\nThe guest shall log in.\n\n[F3]\nThe user shall not log in.\n", &["F1", "F2", "F3"]);
    // Without the definition the two terms are unrelated.
    m_consistent("primitive guest, user\n[F2]\nThe guest shall log in.\n\n[F3]\nThe user shall not log in.\n");
    // A synonym is the same thing in both directions, as an alias is.
    m_conflict("[F1]\nA guest means a user.\n\n[F2]\nThe guest shall not log in.\n\n[F3]\nThe user shall log in.\n", &["F1", "F2", "F3"]);
    // A genus is wider than the term: what a guest may not do, another user may.
    m_consistent("[F1]\nA guest means a user without an account.\n\n[F2]\nThe guest shall not log in.\n\n[F3]\nThe user may log in.\n");
    // The term also stands where an action names it as its object.
    m_conflict("[F1]\nA guest means a user without an account.\n\n[D]\nThe API shall not delete users.\n\n[E]\nThe API shall delete the guest.\n", &["D", "E", "F1"]);
    // A definition obliges nobody: alone it is consistent and asks for no action.
    m_consistent("[F1]\nA guest means a user without an account.\n");
    // The difference is compiled: a guest that exists has no account.
    m_conflict("[F1]\nA guest means a user without an account.\n\n[G1]\nThere is a guest.\n\n[G2]\nEach guest has an account.\n", &["F1", "G1", "G2"]);
}

#[test]
fn a_defined_state_means_what_its_definition_says() {
    // The second reproducer of entry 10. The room accepts messages or not,
    // so whether it is archived is the system's: a system that never lets
    // it be archived keeps F5 vacuously, and nothing requires the trigger
    // (AGENTS.md, limit 2).
    let archived = "[F4]\nAn archived room means a room that accepts no messages.\n\n[F5]\nWhile the room is archived, the room shall accept messages.\n";
    m_consistent(archived);
    // Once a statement requires the trigger, the definition and F5 contradict.
    m_conflict(&format!("{archived}\n[R]\nThe room shall be archived.\n"), &["F4", "F5", "R"]);
    // In another state the room is free to accept messages.
    let active = "[F4]\nAn archived room means a room that accepts no messages.\n\n[F6]\nWhile the room is active, the room shall accept messages.\n";
    m_consistent(active);
    m_consistent(&format!("{active}\n[F7]\nWhile the room is active, the room is never archived.\n"));
    // The definition is the meaning of a term, not an obligation.
    let model = package(archived).inspect(&["model", "--json"]).json();
    let kinds: Vec<&str> = model["constraints"].as_array().unwrap().iter().map(|c| c["kind"].as_str().unwrap()).collect();
    assert_eq!(kinds, ["Spec", "Axiom"], "{model}");
}

#[test]
fn an_inclusion_carries_what_holds_of_the_wider_concept() {
    m_conflict("[I]\nEach guest is a user.\n\n[F2]\nThe guest shall log in.\n\n[F3]\nThe user shall not log in.\n", &["F2", "F3", "I"]);
    m_conflict("[I]\nA guest is a kind of user.\n\n[F2]\nThe guest shall log in.\n\n[F3]\nThe user shall not log in.\n", &["F2", "F3", "I"]);
    // An inclusion has one direction: an obligation of guests is no obligation of users.
    m_consistent("[I]\nEach guest is a user.\n\n[F2]\nThe guest shall not log in.\n\n[F3]\nThe user may log in.\n");
    // Inclusions chain.
    m_conflict("[I]\nEach guest is a user.\n\n[J]\nEach user is a person.\n\n[N]\nNo guest is a person.\n", &["I", "J", "N"]);
    // A description with a place or a part is no inclusion: the place has no
    // reading, and the statement is rejected rather than read as one.
    let lobby = check("[I]\nEach guest is a user in the lobby.\n\n[F2]\nThe guest shall log in.\n\n[F3]\nThe user shall not log in.\n");
    let codes: Vec<String> = m_errors(&lobby).into_iter().map(|(code, _)| code).collect();
    assert!(codes.contains(&"UNSUPPORTED_SEMANTICS".to_string()) && !codes.contains(&"contradiction".to_string()), "{lobby}");
}

#[test]
fn an_exclusion_is_stated_and_never_guessed() {
    let notation = "[N1]\nThe notation of the trion language is a controlled natural language.\n\n[N2]\nThe notation of the trion language is English.\n";
    // Two values of an open domain exclude nothing, as before.
    m_consistent(notation);
    // A stated exclusion makes them a contradiction.
    m_conflict(&format!("{notation}\n[E]\nNo controlled natural language is English.\n"), &["E", "N1", "N2"]);
    // Two values of an open domain exclude nothing, so one thing can be
    // both, with or without a stated inclusion.
    let both = "[A]\nWhile the visitor is a guest, the visitor is a user.\n";
    m_consistent(&format!("{both}\n[G]\nThe visitor is a guest.\n"));
    m_consistent(&format!("[I]\nEach guest is a user.\n\n{both}"));
    // Where a guest exists, a user exists.
    m_conflict("[I]\nEach guest is a user.\n\n[G]\nThere is a guest.\n\n[U]\nEach user has exactly one account.\n\n[V]\nEach user has exactly two accounts.\n", &["G", "I", "U", "V"]);
    // An inclusion and an exclusion of the same two concepts cannot both hold.
    m_conflict("[I]\nEach guest is a member.\n\n[N]\nNo guest is a member.\n", &["I", "N"]);
}

#[test]
fn two_actions_exclude_each_other_once_a_statement_says_so() {
    let both = "[S1]\nWhen a request arrives, the API shall reject the request.\n\n[S2]\nWhen a request arrives, the API shall accept the request.\n";
    // The reproducer of entry 11: unrelated until the exclusion is stated.
    m_consistent(both);
    m_conflict(&format!("[X]\nNo request is both accepted and rejected.\n\n{both}"), &["S1", "S2", "X"]);
    // One of the two alone is fine, and so is another action on the request.
    m_consistent("[X]\nNo request is both accepted and rejected.\n\n[S1]\nWhen a request arrives, the API shall reject the request.\n\n[S3]\nWhen a request arrives, the API shall log the request.\n");
    // The statement lists no values of the request.
    let model = package("[X]\nNo request is both accepted and rejected.\n").inspect(&["model", "--json"]).json();
    assert!(model["closed_domains"].as_object().unwrap().is_empty(), "{model}");
}

#[test]
fn the_details_of_a_statement_must_refine_it() {
    // A detail that requires less than its statement is reported: the
    // statement is the reference of its details, and their equivalence is
    // no axiom.
    let detailed = "[A]\nThe language shall support sentence composition.\n    detailed by [C1], [C2]\n\n[C1]\nThe parser shall read the action list.\n\n[C2]\nThe formalizer shall keep the operator.\n";
    // A document that keeps both exists, so a requirement of the statement
    // is missing from its details as well.
    let report = check(detailed);
    assert_eq!(m_errors(&report).iter().map(|(code, _)| code.as_str()).collect::<Vec<_>>(), ["detail-not-refining", "detail-incomplete"], "{report}");
    assert_eq!(verdict(&report, "refinement/A"), "refuted", "{report}");
    // Details that require what the statement requires, where it applies, refine it.
    let refining = "[A]\nWhen a user sends a message, the API shall store the message.\n    detailed by [C1]\n\n[C1]\nWhen a user sends a message, the API shall store the message and log the message.\n";
    let report = check(refining);
    assert!(m_errors(&report).is_empty(), "{report}");
    assert_eq!(verdict(&report, "refinement/A"), "proved", "{report}");
    // A detail that applies in fewer situations than its statement does not refine it.
    let narrower = "[A]\nThe API shall store the message.\n    detailed by [C1]\n\n[C1]\nWhile the room is open, the API shall store the message.\n";
    assert_eq!(m_errors(&check(narrower)).iter().map(|(code, _)| code.as_str()).collect::<Vec<_>>(), ["detail-not-refining", "detail-incomplete"]);
    // A refinement names statements of the package, and no statement details itself.
    let unknown = check("[A]\nThe language shall support sentence composition.\n    detailed by [Z9]\n");
    assert_eq!(m_errors(&unknown)[0].0, "UNRESOLVED_REFERENCE", "{unknown}");
    let cycle = check("[A]\nThe language shall support sentence composition.\n    detailed by [B]\n\n[B]\nThe parser shall read the action list.\n    detailed by [A]\n");
    assert!(m_errors(&cycle).iter().any(|(code, _)| code == "CYCLIC_REFINEMENT"), "{cycle}");
    let malformed = check("[A]\nThe language shall support sentence composition.\n    detailed by C1\n");
    assert_eq!(m_errors(&malformed)[0].0, "parse-refinement", "{malformed}");
}

const DOOR: &str = "[D1]\nThe door shall be open.\n\n[D2]\nWhile the alarm is active, the door shall be closed.\n";

fn p_codes(body: &str) -> Vec<String> {
    report_codes(&check(body))
}

/// As `p_codes`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn p_codes_of_the_analysis(body: &str) -> Vec<String> {
    analysis_codes(&check(body))
}

#[test]
fn a_priority_line_is_rejected_because_the_contracts_are_a_conjunction() {
    // A statement only removes behaviours: no line lets it lift or narrow another.
    for line in ["    overrides [D1]\n", "    default\n"] {
        let report = check(&format!("{DOOR}{line}"));
        let codes = analysis_codes(&report);
        assert!(codes.contains(&"priority-unsupported".to_string()), "{line}: {codes:?}");
        // The line does not conform, so the package is not converted and nothing is proved.
        assert!(report["proof"].is_null(), "{line}: {report}");
    }
    assert!(p_codes_of_the_analysis("[S1]\nThe API should log the token.\n    weight 5\n").contains(&"priority-unsupported".to_string()));
    // Without the line the conflict stays: nothing narrows D1. The exception
    // is written into the statement that has it.
    let report = check(DOOR);
    assert_eq!(report_codes(&report), ["contradiction"], "{report}");
    assert!(p_codes("[D1]\nThe door shall be open, unless the alarm is active.\n\n[D2]\nWhile the alarm is active, the door shall be closed.\n").is_empty());
    // A general permission is not narrowed by a prohibition: where both apply they contradict.
    assert!(p_codes("[P]\nThe API may stop.\n\n[N]\nWhile the door is open, the API shall not stop.\n").contains(&"contradiction".to_string()));
    assert!(check(DOOR)["priorities"].is_null());
}

#[test]
fn a_property_beyond_one_model_is_named_by_its_kind() {
    let report = check("[H1]\nThe API shall respond deterministically.\n\n[G1]\nThe API shall be secure.\n\n[G2]\nThe API shall respond quickly.\n");
    let found: Vec<(String, String)> = report["inexpressible"].as_array().unwrap().iter().map(|d| (d["refs"][0]["id"].as_str().unwrap().to_string(), d["message"].as_str().unwrap().to_string())).collect();
    let kind = |id: &str| found.iter().find(|(at, _)| at == id).map(|(_, message)| message.as_str()).unwrap_or_default();
    assert!(kind("H1").contains("a relation between runs") && kind("H1").contains("test"), "{found:?}");
    assert!(kind("G1").contains("`secure` states a quality without a measure") && kind("G1").contains("define the term"), "{found:?}");
    assert!(kind("G2").contains("`quickly` states a quality without a measure"), "{found:?}");
    assert_eq!(found.len(), 3, "{found:?}");
    // The analysis itself reports nothing, and the package is not verified:
    // each statement is accepted, and what it requires has no meaning. The
    // reports were warnings that no gate read, and a package of nothing but
    // such statements was verified.
    assert!(analysis_codes(&report).is_empty(), "{report}");
    assert_eq!(report["conforms"], false, "{report}");
    assert!(unverified(&report).contains(&"inexpressible-property".to_string()), "{report}");
    assert_eq!(report["inexpressible"].as_array().unwrap().iter().filter(|d| d["code"] == "inexpressible-property" && d["severity"] == "error").count(), 3, "{report}");
    let run = package("[G1]\nThe API shall be secure.\n").verify(&[]);
    assert_eq!(run.code, 1, "{}", run.stdout);
    assert!(run.stdout.contains("error[inexpressible-property]") && run.stdout.trim_end().ends_with("does not conform"), "{}", run.stdout);
    // An optimum and a share of the cases are named too.
    let more = check("[O1]\nThe API shall respond as fast as possible.\n\n[P1]\nThe API shall usually respond.\n");
    let kinds: Vec<&str> = more["inexpressible"].as_array().unwrap().iter().map(|d| d["message"].as_str().unwrap()).collect();
    assert!(kinds.iter().any(|m| m.contains("an optimum or a preference")) && kinds.iter().any(|m| m.contains("a proportion or a probability")), "{kinds:?}");
    // A defined quality, a state of a closed domain and a measured response are not reported.
    let grounded = check("A secure API means an API that encrypts each message.\n\n[G1]\nThe API shall be secure.\n\n[S]\nThe mode is fast or slow.\n\n[M]\nWhen a request arrives, the API shall respond within 200 ms.\n");
    assert_eq!(grounded["inexpressible"].as_array().unwrap().len(), 0, "{grounded}");
}

#[test]
fn recommendations_that_cannot_all_be_followed_are_reported() {
    let body = "primitive API, token, log\n[H]\nThe API shall not log the token.\n\n[S1]\nThe API should log the token.\n\n[S2]\nThe API should compress the log.\n\n[S3]\nThe API should not compress the log.\n\n[S4]\nThe API should sign the log.\n";
    let report = check(body);
    // A recommendation that cannot be followed is reported, and the hard constraints hold.
    assert!(analysis_codes(&report).iter().all(|c| c == "recommendation-violation") && !analysis_codes(&report).is_empty(), "{report}");
    assert_eq!(verdict(&report, "consistency"), "proved");
    // Recommendations that all fit leave nothing to report.
    assert!(check("[S2]\nThe API should compress the log.\n\n[S4]\nThe API should sign the log.\n")["preference"].is_null());
}

// Entries 14, 16 and 17: conditions together, moments, and the environment.

/// The statements of each contradiction of a report, sorted.
fn e_conflicts(report: &Value) -> Vec<Vec<String>> {
    m_errors(report)
        .into_iter()
        .filter(|(code, _)| code == "contradiction")
        .map(|(_, mut ids)| {
            ids.sort();
            ids
        })
        .collect()
}

const J: &str = "[J1]\nWhen a user sends a message, the API shall store the message.\n\n[J2]\nWhile the room is archived, the API shall not store the message.\n";

#[test]
fn two_conditions_that_can_hold_together_make_one_situation() {
    let report = check(J);
    // A behaviour keeps both statements where the conditions never meet, and
    // nothing says that they never meet: the specification is inconsistent.
    assert_eq!(analysis_codes(&report), ["contradiction"], "{report}");
    assert_eq!(verdict(&report, "consistency"), "refuted");
    assert_eq!(e_conflicts(&report), [["J1", "J2"]]);
    let run = package(J).verify(&[]);
    assert_eq!(run.code, 1);
    // The report names the situation: what holds in it, as far as the conflict needs it.
    assert!(run.stdout.contains("Val(x::room@") && run.stdout.contains("archived)") && run.stdout.contains("Event(x::user send message@") && run.stdout.contains("the environment can bring that about"), "{}", run.stdout);
    // Statements about different things are in no conflict.
    let apart = check("primitive API, bell, room, message, archived\n[K1]\nWhen the bell rings, the API shall stop.\n\n[K2]\nWhile the room is archived, the API shall not store the message.\n");
    assert!(analysis_codes(&apart).is_empty(), "{apart}");
    assert_eq!(verdict(&apart, "consistency"), "proved");
}

#[test]
fn an_exception_or_an_exclusion_of_the_conditions_settles_the_conflict() {
    // The exception names the other condition, and a statement without a
    // modal verb can say that the two conditions never hold together: either
    // settles the moment of the sending. Over the trace neither settles the
    // conflict: the message is sent while the room is open, the environment
    // archives the room at the next moment and keeps it archived, and no
    // moment is left at which [J1] can store the message and [J2] allows it.
    let unless = J.replace("shall store the message.", "shall store the message, unless the room is archived.");
    assert_eq!(e_conflicts(&check(&unless)), [["J1", "J2"]]);
    let excluded = format!("{J}\n[J3]\nWhile the room is archived, no user sends a message.\n");
    assert_eq!(e_conflicts(&check(&excluded)), [["J1", "J2"]]);
    // A closed enumeration separates two states of one attribute.
    let states = "[K]\nThe room state is active or archived.\n\n[S1]\nWhile the room state is active, the API shall store the message.\n\n[S2]\nWhile the room state is archived, the API shall not store the message.\n";
    assert!(report_codes(&check(states)).is_empty());
    // Two open states of one attribute exclude each other as well; two attributes do not.
    let attributes = "[S1]\nWhile the room is active, the API shall store the message.\n\n[S2]\nWhile the door is locked, the API shall not store the message.\n";
    assert_eq!(e_conflicts(&check(attributes)), [["S1", "S2"]]);
}

#[test]
fn a_prohibition_under_a_condition_meets_an_obligation_where_the_condition_holds() {
    let body = "[A]\nWhile the room is archived, the API shall not store the message.\n\n[B]\nThe API shall store the message.\n";
    let report = check(body);
    // The API may store the message at a moment at which the room is not
    // archived; nothing says that such a moment exists, and the environment
    // keeps the room archived: the two cannot be kept there.
    assert_eq!(verdict(&report, "consistency"), "refuted");
    assert_eq!(e_conflicts(&report), [["A", "B"]]);
    // A prohibition without a condition contradicts the obligation in every behaviour.
    let always = check("[A]\nThe API shall not store the message.\n\n[B]\nThe API shall store the message.\n");
    assert_eq!(report_codes(&always), ["contradiction"]);
    assert_eq!(verdict(&always, "consistency"), "refuted");
    assert!(always["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "contradiction" && d["message"].as_str().unwrap().contains("in every situation")), "{always}");
}

#[test]
fn a_statement_that_ends_or_forbids_a_situation_is_in_no_conflict_there() {
    // The door does not stay open, so the lamp need not be lit and unlit at once.
    let ends = "[K]\nThe door is open or closed.\n\n[A]\nWhile the door is open, the lamp shall be lit.\n\n[B]\nWhile the door is closed, the lamp shall not be lit.\n\n[C]\nWhen the door is open, the door shall become closed.\n\n[D]\nWhen the door is closed, the door shall become open.\n";
    assert!(e_conflicts(&check(ends)).is_empty());
    // A prohibition and what follows its breach do not contradict each
    // other. The prohibition is on the user, so it is an assumption, and it
    // leaves no environment in which the trigger of the second statement
    // occurs: the second statement requires nothing, and compatibility,
    // not consistency, fails (AGENTS.md, limit 2: vacuity is no fifth
    // property).
    let report = check(E);
    assert_eq!(report_codes(&report), ["incompatible"], "{report}");
    assert_eq!(verdict(&report, "consistency"), "proved");
    let named: Vec<&str> = report["diagnostics"].as_array().unwrap().iter().filter(|d| d["code"] == "incompatible").flat_map(|d| d["refs"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap())).collect();
    assert_eq!(named, ["E1", "E2"], "{report}");
}

#[test]
fn a_deadline_and_a_delay_relate_two_moments() {
    let late = "[D1]\nWhen a request arrives, the API shall respond within 5 seconds.\n\n[D2]\nWhen a request arrives, the API shall respond after 10 seconds.\n";
    assert_eq!(report_codes(&check(late)), ["contradiction"]);
    let fits = late.replace("after 10 seconds", "after 2 seconds");
    assert!(report_codes(&check(&fits)).is_empty());
    // A deadline that names its origin is measured from the last occurrence
    // of that event, so it does not bound the time since another trigger.
    // The environment decides both: where the user sends the request at the
    // moment it arrives, the response is due within 5 seconds of both, and
    // [T2] forbids it before 10 seconds.
    let named = "[T1]\nWhen a request arrives, the API shall respond within 5 seconds after the user sends the request.\n\n[T2]\nWhen a request arrives, the API shall respond after 10 seconds.\n";
    let report = check(named);
    assert_eq!(report_codes(&report), ["contradiction"], "{report}");
    let conflict = report["diagnostics"].as_array().unwrap().iter().find(|d| d["code"] == "contradiction").unwrap();
    let message = conflict["message"].as_str().unwrap();
    assert!(message.contains("request arrive@") && message.contains("the environment can bring that about"), "{message}");
}

#[test]
fn an_adverb_of_time_before_the_verb_is_no_verb() {
    let f = package("[L1]\nWhen a request arrives, the API shall eventually respond.\n\n[L2]\nWhen a request arrives, the API shall immediately log the request.\n");
    let expansion = f.inspect(&["expand", "--json"]).stdout;
    assert!(!expansion.contains("\"verb\":\"eventually\""), "{expansion}");
    let model = f.inspect(&["model"]).stdout;
    assert!(model.contains("Act(x::API|respond)") && model.contains("Act(x::API|log request)"), "{model}");
    assert!(!model.contains("eventually") || model.contains("eventually complete"), "{model}");
    // The adverb changes nothing about which action a prohibition denies.
    let report = check("[L1]\nWhen a request arrives, the API shall eventually respond.\n\n[L3]\nWhen a request arrives, the API shall not respond.\n");
    assert_eq!(report_codes(&report), ["contradiction"]);
}

const E: &str = "[E1]\nThe user shall not send a message.\n\n[E2]\nWhen the user sends a message, the API shall store the message.\n";

#[test]
fn a_declaration_decides_who_controls_an_actor() {
    let report = check(E);
    assert_eq!(report["control"]["environment"], serde_json::json!(["x::user"]), "{report}");
    assert_eq!(report["control"]["system"], serde_json::json!(["x::API"]), "{report}");
    let declared = check(&format!("system user\n\n{E}"));
    assert_eq!(declared["control"]["system"], serde_json::json!(["x::API", "x::user"]));
    let outside = check("environment API\n\n[B1]\nThe API shall store the message.\n");
    assert_eq!(outside["control"]["environment"], serde_json::json!(["x::API"]));
}

#[test]
fn a_response_before_what_the_environment_decides_cannot_be_kept() {
    let report = check("primitive API, room, message, user\n[C1]\nThe API shall lock the room before the user sends a message.\n\n[C0]\nWhen the user sends a message, the API shall store the message.\n");
    assert_eq!(analysis_codes(&report), ["unrealizable"], "{report}");
    let found = report["diagnostics"].as_array().unwrap().iter().find(|d| d["code"] == "unrealizable").unwrap();
    assert_eq!(found["refs"][0]["id"], "C1");
    assert!(found["message"].as_str().unwrap().contains("the environment can act before the response can come"), "{found}");
    assert_eq!(verdict(&report, "consistency"), "proved", "{report}");
    // Before an action of the system itself, the system can keep the order.
    let own = check("primitive API, room, message\n[C2]\nThe API shall lock the room before the API stores the message.\n\n[C3]\nThe API shall store the message.\n");
    assert!(analysis_codes(&own).is_empty(), "{own}");
}

/// Whether an assertion of the SMT-LIB script `text` holds `wanted` (read as
/// an SMT-LIB term) as a subterm: the abstract syntax is compared, not the
/// text.
fn asserts_subterm(text: &str, wanted: &str) -> bool {
    use trion_verification::proof::smtlib::command::{Command, Script};
    use trion_verification::proof::smtlib::Term;
    let script = Script::parse(text).unwrap_or_else(|e| panic!("not SMT-LIB: {e}\n{text}"));
    let wanted = Term::parse(wanted).unwrap();
    let mut stack: Vec<&Term> = script.commands().iter().filter_map(|c| if let Command::Assert(t) = c { Some(t) } else { None }).collect();
    while let Some(term) = stack.pop() {
        if *term == wanted {
            return true;
        }
        if let Term::Application(_, args) = term {
            stack.extend(args.iter());
        }
    }
    false
}
