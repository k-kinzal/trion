//! A statement is read with its own words, the declarations and the
//! definitions, and with nothing else that stands around it. What other
//! statements add is a relation between the entries. Each test runs its
//! reproducer as the body of `namespace p.x:` in a package `p`.

mod common;
use common::*;
use serde_json::Value;

fn package(body: &str) -> Fixture {
    let indented: String = body.lines().map(|line| if line.is_empty() { "\n".to_string() } else { format!("    {line}\n") }).collect();
    Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\nentry = \"a.trion\"\n"), ("a.trion", &format!("package p edition \"1\"\n\nnamespace p.x:\n{indented}"))])
}

fn model(body: &str) -> String {
    package(body).inspect(&["model"]).stdout
}

fn model_json(body: &str) -> Value {
    package(body).inspect(&["model", "--json"]).json()
}

fn check(body: &str) -> Value {
    package(body).verify(&["--json"]).json()
}

/// Whether the properties of the reading hold: `passed` when `--properties`
/// finds none of them broken, `failed` with the findings otherwise. A broken
/// property is an error of the checker, and the package does not convert.
fn properties(body: &str) -> String {
    let report = package(body).verify(&["--json", "--properties"]).json();
    const PROPERTIES: [&str; 4] = ["relation-not-local", "order-dependent", "round-trip-differs", "context-dependent"];
    let broken: Vec<&Value> = report["checker"].as_array().unwrap().iter().filter(|d| PROPERTIES.contains(&d["code"].as_str().unwrap_or_default())).collect();
    format!("{}: {broken:?}", if broken.is_empty() { "passed" } else { "failed" })
}

/// The kinds of the constraints of one statement, in the order of the model.
fn kinds(model: &Value, id: &str) -> Vec<String> {
    let constraints = model.get("constraints").or_else(|| model["model"].get("constraints")).and_then(Value::as_array).cloned().unwrap_or_default();
    constraints.iter().filter(|c| c["refs"][0]["id"] == id).map(|c| c["kind"].as_str().unwrap_or_default().to_string()).collect()
}

fn applied(model: &Value) -> Vec<(String, String, Vec<String>)> {
    let list = model.get("applied").or_else(|| model["model"].get("applied")).and_then(Value::as_array).cloned().unwrap_or_default();
    list.iter().map(|a| (a["kind"].as_str().unwrap_or_default().to_string(), a["subject"]["id"].as_str().unwrap_or_default().to_string(), a["rests_on"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap_or_default().to_string()).collect())).collect()
}

const TERMS: &str = "primitive user\nprimitive message\nprimitive room\nprimitive parser\nprimitive report\n\n";

#[test]
fn the_number_of_a_word_is_decided_by_its_ending_and_the_declarations() {
    // A plural names what its singular names, whether or not another statement uses the singular.
    let alone = model(&format!("{TERMS}[A] The parser shall read messages.\n"));
    assert!(alone.contains("Act(x::parser|read message)"), "{alone}");
    let both = model(&format!("{TERMS}[A] The parser shall read messages.\n[B] The parser shall not read a message.\n"));
    assert!(both.contains("Act(x::parser|read message)") && both.contains("Forbid(x::parser|read message)"), "{both}");
    // A word in `-ss`, `-us` or `-is` is no plural.
    let kept = model(&format!("{TERMS}[A] The parser shall read the status of the class.\n"));
    assert!(kept.contains("class status") || kept.contains("status of class"), "{kept}");
    // A declared word keeps its spelling, and its plural is that word.
    let declared = model(&format!("{TERMS}primitive alias\n[A] The parser shall read aliases.\n[B] The parser shall read an alias.\n"));
    assert!(declared.contains("Act(x::parser|read alias)") && !declared.contains("aliase"), "{declared}");
    // A capital that only opens the sentence is no part of the name.
    let opening = model(&format!("{TERMS}[A] Messages shall reach the user.\n"));
    assert!(opening.contains("x::message|reach"), "{opening}");
}

#[test]
fn a_verb_form_is_read_by_the_verbs_of_the_language() {
    // `organizes` and `saved` are forms of verbs that the language knows, with no other statement to say so.
    let third = model(&format!("{TERMS}primitive section\nprimitive content\nEach section organizes content.\n"));
    assert!(third.contains("organize content"), "{third}");
    let passive = model(&format!("{TERMS}[A] The report shall be saved by the parser.\n"));
    assert!(passive.contains("Act(x::parser|save report)"), "{passive}");
}

#[test]
fn a_bare_participle_is_the_passive_of_an_action_and_establishes_a_named_state() {
    let alone = model(&format!("{TERMS}[R] The room shall be archived.\n"));
    assert!(alone.contains("Act(x::room|be archived)"), "{alone}");
    // With a statement that names the state, the reading of [R] is the same and a relation joins the two.
    let body = format!("{TERMS}[M] The user may delete the message.\n[R] The room shall be archived.\n[P] While the room is archived, the user shall not delete the message.\n");
    let json = model_json(&body);
    assert_eq!(kinds(&json, "R"), ["Spec", "Carried"], "{json}");
    assert!(model(&body).contains("(Act(x::room|be archived) → Val(x::room, archived))"));
    assert!(applied(&json).contains(&("applied".to_string(), "R".to_string(), vec!["P".to_string()])), "{json}");
    let report = check(&body);
    assert_eq!(verdicts(&report).get("consistency").map(String::as_str), Some("proved"), "{report}");
    assert!(properties(&body).starts_with("passed"), "{}", properties(&body));
    // The prohibition of the action excludes the state.
    let denied = model(&format!("{TERMS}[R] The room shall not be archived.\n[P] While the room is archived, the user shall not delete the message.\n"));
    assert!(denied.contains("(Forbid(x::room|be archived) → ¬Val(x::room, archived))"), "{denied}");
}

#[test]
fn an_enumeration_lists_its_values_and_excludes_the_others_as_a_relation() {
    let alone = model_json(&format!("{TERMS}[T] The room type is private or public.\n"));
    assert_eq!(kinds(&alone, "T"), ["Spec"], "{alone}");
    let body = format!("{TERMS}[T] The room type is private or public.\n[U] The room type shall be secret.\n");
    let json = model_json(&body);
    assert_eq!(kinds(&json, "T"), ["Spec", "Carried"], "{json}");
    assert!(applied(&json).contains(&("applied".to_string(), "T".to_string(), vec!["U".to_string()])), "{json}");
    // The conflict still names the enumeration.
    let report = check(&body);
    let refs: Vec<String> = report["diagnostics"].as_array().unwrap().iter().filter(|d| d["code"] == "contradiction").flat_map(|d| d["refs"].as_array().unwrap().clone()).map(|r| r["id"].as_str().unwrap().to_string()).collect();
    assert!(refs.contains(&"T".to_string()) && refs.contains(&"U".to_string()), "{report}");
    assert!(properties(&body).starts_with("passed"), "{}", properties(&body));
}

#[test]
fn an_inclusion_states_itself_and_reaches_other_statements_as_a_relation() {
    let body = format!("{TERMS}primitive guest\n[G] Each guest is a user.\n[N] The parser shall not notify a user.\n[Y] The parser shall notify a guest.\n");
    let json = model_json(&body);
    // The inclusion is read as one contract; what it says of its terms,
    // and of [N] and [Y], stands beside the contract.
    let own: Vec<String> = kinds(&json, "G");
    assert_eq!(own.iter().filter(|kind| *kind != "Carried").collect::<Vec<_>>(), ["Spec"], "{json}");
    assert!(own.contains(&"Carried".to_string()), "{json}");
    let relations = applied(&json);
    assert!(relations.iter().any(|(kind, subject, rests_on)| kind == "applied" && subject == "G" && rests_on.contains(&"N".to_string()) && rests_on.contains(&"Y".to_string())), "{json}");
    let report = check(&body);
    assert!(report["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "contradiction"), "{report}");
    assert!(properties(&body).starts_with("passed"), "{}", properties(&body));
}

#[test]
fn a_reading_over_individuals_is_a_relation_between_the_statements_that_name_the_domain() {
    let body = format!("{TERMS}primitive owner\n[A] Some room has no owner.\n[B] Each room has exactly one owner.\n");
    let json = model_json(&body);
    // `Some room …` claims that such a room exists: that is the contract of
    // its sentence. What it says of an individual is read over the
    // individuals of the package and stands beside the contract, as what
    // follows from the claim.
    assert!(kinds(&json, "A").contains(&"Spec".to_string()) && kinds(&json, "A").contains(&"Carried".to_string()) && !kinds(&json, "A").contains(&"Axiom".to_string()), "{json}");
    // `Each room …` is read over individuals because A speaks of the relation.
    assert!(kinds(&json, "B").contains(&"Carried".to_string()), "{json}");
    assert!(applied(&json).iter().any(|(kind, subject, rests_on)| kind == "individuals" && subject == "B" && rests_on.contains(&"A".to_string())), "{json}");
    assert!(properties(&body).starts_with("passed"), "{}", properties(&body));
}

#[test]
fn a_coordination_inside_a_role_is_one_action_for_each_noun_phrase() {
    // A required action leaves a choice between the alternatives of a role.
    let choice = model(&format!("{TERMS}primitive fact\nprimitive declaration\nprimitive definition\n[F] Each fact shall rest on a declaration or a definition.\n"));
    assert!(choice.contains("Act(x::fact|rest on declaration)") && choice.contains("Act(x::fact|rest on definition)") && choice.contains("∨"), "{choice}");
    assert!(!choice.contains("Act(x::fact|rest on declaration or definition)"), "{choice}");
    // A prohibition reaches each of them.
    let body = format!("{TERMS}[A] The parser shall not send the report to the user or the room.\n[B] The parser shall send the report to the room.\n");
    let report = check(&body);
    assert!(report["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "contradiction"), "{report}");
    // A conjunction requires each.
    let both = model(&format!("{TERMS}[A] The parser shall send the report to the user and the room.\n"));
    assert!(both.contains("Act(x::parser|send report to user)") && both.contains("Act(x::parser|send report to room)"), "{both}");
}

#[test]
fn a_flow_without_choices_is_read_as_its_ordered_action_list() {
    let flow = format!("{TERMS}[F] When the parser receives a message, the parser shall follow this flow:\n    step read: read the message;\n    step answer: send the report;\n    start read\n    read -> answer\n    finish answer\n");
    let list = format!("{TERMS}[F] When the parser receives a message, the parser shall perform the following actions in order:\n    read the message;\n    send the report;\n");
    let strip = |text: String| text.lines().filter(|l| !l.trim_start().starts_with("text:") && !l.contains("follow this flow") && !l.contains("following actions")).collect::<Vec<_>>().join("\n");
    assert_eq!(strip(model(&flow)), strip(model(&list)));
    assert!(properties(&flow).starts_with("passed"), "{}", properties(&flow));
}
