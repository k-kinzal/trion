//! Statements about the individuals of a type, read over a bounded domain. Each test runs its
//! reproducer as the body of `namespace p.x:` in a package `p`.

mod common;
use common::*;
use serde_json::Value;

fn package(body: &str) -> Fixture {
    let indented: String = body.lines().map(|line| if line.is_empty() { "\n".to_string() } else { format!("    {line}\n") }).collect();
    Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\nentry = \"a.trion\"\n"), ("a.trion", &format!("package p\n\nnamespace p.x:\n{indented}"))])
}

fn check(body: &str) -> Value {
    package(body).verify(&["--json"]).json()
}

/// The statements of each conflict that the proof names, sorted: a
/// contradiction names its statements, an incompatibility names none.
fn conflicts(report: &Value) -> Vec<Vec<String>> {
    report["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|d| d["code"] == "contradiction" || d["code"] == "incompatible")
        .map(|d| {
            let mut ids: Vec<String> = d["refs"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap().to_string()).collect();
            ids.sort();
            ids.dedup();
            ids
        })
        .collect()
}

fn verdict(report: &Value, obligation: &str) -> Option<String> {
    verdicts(report).get(obligation).cloned()
}

fn consistent(body: &str) {
    let report = check(body);
    assert!(conflicts(&report).is_empty(), "{body}\n{report}");
    assert_eq!(verdict(&report, "consistency").as_deref(), Some("proved"), "{body}\n{report}");
    assert_eq!(verdict(&report, "compatibility").as_deref(), Some("proved"), "{body}\n{report}");
}

/// The body without the statements `ids`: each statement is a block that
/// begins with its label.
fn without(body: &str, id: &str) -> String {
    body.split("\n\n").filter(|block| !block.trim_start().starts_with(&format!("[{id}]"))).collect::<Vec<_>>().join("\n\n")
}

/// The statements describe individuals that no statement gives to the
/// system: they are assumptions, and together they allow no environment.
/// The incompatibility names no statements, so each of `members` is shown
/// to be needed: without it, an environment exists.
fn contradicts(body: &str, members: &[&str]) {
    let report = check(body);
    assert_eq!(verdict(&report, "compatibility").as_deref(), Some("refuted"), "{body}\n{report}");
    assert!(report_codes(&report).contains(&"incompatible".to_string()), "{body}\n{report}");
    for member in members {
        let rest = check(&without(body, member));
        assert_eq!(verdict(&rest, "compatibility").as_deref(), Some("proved"), "{body}\nwithout {member}:\n{rest}");
    }
}

const ROOMS: &str = "[U1]\nEach room has exactly one owner.\n\n[U2]\nThe owner of each room is a member of the room.\n\n[U3]\nThere is a room.\n";

#[test]
fn the_owner_of_a_room_is_one_of_the_members_of_that_room() {
    consistent(ROOMS);
    // The one owner is a member, so a room cannot be without members.
    contradicts(&format!("{ROOMS}\n[U4]\nEach room has no member.\n"), &["U1", "U2", "U3", "U4"]);
    // Without the inclusion the owner and the members are unrelated.
    consistent("[U1]\nEach room has exactly one owner.\n\n[U3]\nThere is a room.\n\n[U4]\nEach room has no member.\n");
    // The other spelling of the inclusion reads the same.
    contradicts("[U1]\nEach room has exactly one owner.\n\n[M1]\nThe owner of a room is one of the members of the room.\n\n[U3]\nThere is a room.\n\n[C2]\nThe number of members of each room is at most 0.\n", &["U1", "M1", "U3", "C2"]);
    // Nothing is claimed while no room exists.
    consistent("[U1]\nEach room has exactly one owner.\n\n[U2]\nThe owner of each room is a member of the room.\n\n[U4]\nEach room has no member.\n");
}

#[test]
fn no_two_rooms_have_the_same_name() {
    let rooms = "[N1]\nNo two rooms have the same name.\n\n[N2]\nEach room has exactly one name.\n\n[N3]\nThere are at least two rooms.\n";
    consistent(rooms);
    // Two rooms need two names, and one label cannot be both.
    contradicts(&format!("{rooms}\n[N4]\nEach name is a label.\n\n[N5]\nThe number of labels is at most 1.\n"), &["N1", "N2", "N3", "N4", "N5"]);
    // One room needs one name only.
    consistent("[N1]\nNo two rooms have the same name.\n\n[N2]\nEach room has exactly one name.\n\n[N3]\nThere is a room.\n\n[N4]\nEach name is a label.\n\n[N5]\nThe number of labels is at most 1.\n");
}

#[test]
fn a_statement_about_some_individual_is_not_about_all_of_them() {
    contradicts("[S1]\nSome accepted sentence denotes no expression.\n\n[S2]\nEach accepted sentence denotes exactly one expression.\n", &["S1", "S2"]);
    // One room without an owner and another room with one can both exist.
    consistent("[S1]\nSome room has no owner.\n\n[S2]\nSome room has an owner.\n\n[S3]\nThere is a room.\n");
    // In a domain of one room they cannot.
    let one = package("[S1]\nSome room has no owner.\n\n[S2]\nSome room has an owner.\n").verify(&["--json", "--scope", "1"]).json();
    assert_eq!(conflicts(&one).len(), 1, "{one}");
    assert_eq!(verdict(&one, "compatibility").as_deref(), Some("refuted"), "{one}");
}

#[test]
fn the_members_of_a_room_are_counted() {
    contradicts("[C1]\nEach room has at least two members.\n\n[C2]\nThe number of members of each room is at most 1.\n\n[C3]\nThere is a room.\n", &["C1", "C2", "C3"]);
    consistent("[C1]\nEach room has at least two members.\n\n[C2]\nThe number of members of each room is at most 2.\n\n[C3]\nThere is a room.\n");
    // The individuals of a type are counted the same way.
    contradicts("[P1]\nThere are at least two rooms.\n\n[P2]\nThe number of rooms is at most 1.\n", &["P1", "P2"]);
}

#[test]
fn a_total_is_the_sum_over_the_individuals_that_exist() {
    let sizes = "[A1]\nThe total size of all attachments is at most 10 MB.\n\n[A2]\nThe size of each attachment is at least 20 MB.\n";
    // Whether the two conflict depends on whether an attachment exists.
    consistent(sizes);
    contradicts(&format!("{sizes}\n[A3]\nThere is an attachment.\n"), &["A1", "A2", "A3"]);
    consistent("[A1]\nThe total size of all attachments is at most 10 MB.\n\n[A2]\nThe size of each attachment is at least 4 MB.\n\n[A3]\nThere are at least two attachments.\n");
    contradicts("[A1]\nThe total size of all attachments is at most 10 MB.\n\n[A2]\nThe size of each attachment is at least 4 MB.\n\n[A3]\nThere are at least 3 attachments.\n", &["A1", "A2", "A3"]);
}

#[test]
fn a_condition_that_no_individual_can_meet_is_found() {
    let denotation = "[MODEL-TEXT-DENOTATION]\nEach normative statement denotes exactly one expression.\n\n[MODEL-UNSUPPORTED]\nWhen an accepted construct has no supported formal interpretation,\nthe compiler shall report \"UNSUPPORTED_SEMANTICS\"\nand shall identify the affected verification obligations.\n";
    let inclusion = "\n[I1]\nEach accepted construct is a normative statement.\n";
    let identity = "\n[I2]\nThe supported formal interpretation of a construct means the expression that the construct denotes.\n";
    // An accepted construct that is a normative statement has an expression,
    // and that expression is its interpretation: the condition cannot be met.
    let report = check(&format!("{denotation}{inclusion}{identity}"));
    // The three statements without a modal verb exclude the condition: it is
    // no contradiction, and the statement under the condition requires
    // nothing. No environment that the descriptions allow meets the
    // assumption of a statement, and compatibility says so.
    assert!(!report_codes(&report).contains(&"contradiction".to_string()), "{report}");
    assert_eq!(verdict(&report, "consistency").as_deref(), Some("proved"), "{report}");
    assert_eq!(verdict(&report, "compatibility").as_deref(), Some("refuted"), "{report}");
    // Each of the two links is needed: nothing is guessed from the spelling.
    consistent(&format!("{denotation}{inclusion}"));
    consistent(&format!("{denotation}{identity}"));
    consistent(denotation);
}

#[test]
fn a_definition_reaches_each_member_that_exists() {
    let guests = "[F1]\nA guest means a user without an account.\n\n[G2]\nEach guest has an account.\n";
    consistent(guests);
    contradicts(&format!("{guests}\n[G3]\nThere is a guest.\n"), &["F1", "G2", "G3"]);
    // The individuals of the defined term are individuals of its genus.
    contradicts("[F1]\nA guest means a user without an account.\n\n[G1]\nThere are at least two guests.\n\n[G2]\nThe number of users is at most 1.\n", &["F1", "G1", "G2"]);
}

#[test]
fn a_result_about_individuals_names_the_size_of_its_domains() {
    let f = package(ROOMS);
    let text = f.verify(&[]).stdout;
    assert!(text.contains("domains of 3 individuals"), "{text}");
    assert!(f.verify(&["--scope", "2"]).stdout.contains("domains of 2 individuals"));
    assert_eq!(f.verify(&["--json"]).json()["proof"]["subject"]["individuals"], 3);
    // A package that relates no individuals is not bounded by a domain.
    let plain = package("primitive API\n\n[A]\nThe API shall stop.\n").verify(&[]).stdout;
    assert!(plain.trim_end().ends_with("\nproved"), "{plain}");
    assert!(!plain.contains("individuals"), "{plain}");
    // A statement that counts four rooms is read over four rooms, whatever bound is asked for.
    let many = package("[P1]\nThere are at least 4 rooms.\n\n[P2]\nEach room has exactly one owner.\n");
    let report = many.verify(&["--scope", "2"]).stdout;
    assert!(report.contains("obligation consistency (consistency): proved") && report.contains("domains of 4 individuals"), "{report}");
    assert!(!conflicts(&package("[P1]\nThere are at least 4 rooms.\n\n[P2]\nEach room has exactly one owner.\n\n[P3]\nSome room has no owner.\n").verify(&["--json"]).json()).is_empty());
    // The model shows the individuals.
    let model = f.inspect(&["model"]).stdout;
    assert!(model.contains("x::owner(x::room#1, x::owner#1) → x::member(x::room#1, x::member#1)"), "{model}");
}
