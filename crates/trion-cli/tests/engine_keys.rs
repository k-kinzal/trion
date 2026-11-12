//! Keys that do not depend on a general determiner, enumerations that ground
//! their values, refinements that stay out of unrelated proofs, blocks as
//! details, and control declarations that reach the namespaces that use them.

mod common;
use common::*;
use serde_json::Value;

fn check(text: &str) -> Value {
    Fixture::new(&[("a.trion", text)]).trion(&["verify", "--json", "a.trion"]).json()
}

fn codes(text: &str) -> Vec<String> {
    report_codes(&check(text))
}

fn model(text: &str) -> String {
    Fixture::new(&[("a.trion", text)]).inspect(&["model", "a.trion"]).stdout
}

fn silent(report: &Value, list: &str) -> Vec<String> {
    report[list].as_array().unwrap().iter().map(|d| d["message"].as_str().unwrap().to_string()).collect()
}

#[test]
fn an_action_on_each_thing_is_the_action_on_the_thing() {
    assert_eq!(codes("[A] The plugin shall fold each block.\n[B] The plugin shall not fold the block.\n"), ["contradiction"]);
    assert_eq!(codes("[A] The plugin shall report every error to all users.\n[B] The plugin shall not report the error to the users.\n"), ["contradiction"]);
    // A condition about each thing waits for the event of the action on the thing.
    let chained = "[A] The parser shall read each line.\n[B] When the parser reads the line, the parser shall count the line.\n[C] The parser shall not count the line.\n";
    assert_eq!(codes(chained), ["contradiction"]);
    let read = check("[A] The plugin shall fold each block.\n");
    assert!(silent(&read, "opaque").is_empty(), "{read}");
    // A count is not a general determiner: it stays in the relation.
    assert!(model("Each room has exactly one owner.\n").contains("has owner count = 1"));
}

#[test]
fn the_same_thing_is_the_thing() {
    assert_eq!(codes("[A] The checker shall use the same environment.\n[B] The checker shall not use the environment.\n"), ["contradiction"]);
    // Two things that are each the same state a function of the one in the other:
    // that is read over individuals, not read away as two articles.
    let runs = check("[H1] The API shall return the same response for the same request.\n[H2] The API shall return two responses for each request.\nThere is a request.\n");
    assert_eq!(report_codes(&runs), ["contradiction"], "{runs}");
    assert!(silent(&runs, "inexpressible").is_empty(), "{runs}");
    // `another` is not read as the thing, and a name of a kind cannot say
    // that two things are not one: the statement is rejected.
    let other = check("[A] The checker shall use another environment.\n[B] The checker shall not use the environment.\n");
    assert!(report_codes(&other).is_empty(), "{other}");
    assert!(silent(&other, "opaque").iter().any(|m| m.contains("`another` is a word that tells two things apart")), "{other}");
}

#[test]
fn an_enumeration_grounds_its_values() {
    let report = check("A test case means a run of a test.\n[R] The result of a test case is passed, failed, or stale.\n[S] The parser shall frobnicate the wibble.\n");
    let ungrounded = silent(&report, "ungrounded");
    assert_eq!(ungrounded.len(), 1, "{ungrounded:?}");
    assert!(ungrounded[0].contains("wibble"), "{ungrounded:?}");
}

/// A package of `count` rules that one statement is detailed by.
fn refined(count: usize) -> String {
    let mut text = String::from("[TOP] The tool shall keep the contract.\n    detailed by ");
    text.push_str(&(0..count).map(|i| format!("[D{i}]")).collect::<Vec<_>>().join(", "));
    text.push('\n');
    for i in 0..count {
        text.push_str(&format!("[D{i}] When the event{i} occurs, the tool shall perform the following actions in order:\n    record the step{i};\n    report the step{i};\n"));
    }
    text.push_str("[L] The tool shall record the entry.\n[R] The tool shall record the entry.\ncheck SAME:\n    relation equivalent\n    left [L]\n    right [R]\n    using definitions\n");
    text
}

#[test]
fn a_refinement_stays_out_of_a_proof_that_its_statement_is_not_part_of() {
    let text = refined(150);
    let started = std::time::Instant::now();
    let report = check(&text);
    assert!(report_codes(&report).is_empty(), "{report}");
    assert_eq!(report["checks"][0]["result"], "proved");
    assert_eq!(report["consistency"]["status"], "satisfiable");
    assert!(started.elapsed().as_secs() < 20, "the check took {:?}", started.elapsed());
    // The refinement still carries a conflict with a detail to the detailed statement.
    let conflict = check(&format!("{text}[N] When the event3 occurs, the tool shall not record the step3.\n"));
    assert_eq!(report_codes(&conflict), ["contradiction"]);
    assert!(conflict["diagnostics"][0]["message"].as_str().unwrap().contains("TOP"), "{conflict}");
}

#[test]
fn a_concept_block_and_a_flow_can_detail_a_statement() {
    let text = "[A] The model shall keep the structure.\n    detailed by [C], [F]\n[C] concept:\n    [C/a] each order -> has -> exactly one buyer;\n[F] When a request arrives, the API shall follow this flow:\n    step check: validate the request;\n    start check\n    finish check\n[T] There is an order.\n";
    assert!(codes(text).is_empty(), "{:?}", codes(text));
    let conflict = check(&format!("{text}[N] Each order has no buyer.\n"));
    assert_eq!(report_codes(&conflict), ["contradiction"]);
    assert!(conflict["diagnostics"][0]["message"].as_str().unwrap().contains("`A`"), "{conflict}");
    assert_eq!(codes("[A] The model shall keep the structure.\n    detailed by [MISSING]\n"), ["UNRESOLVED_REFERENCE"]);
}

#[test]
fn a_control_declaration_reaches_the_namespaces_that_use_it() {
    let manifest = "[package]\nname = \"p\"\nentry = \"p.trion\"\n";
    let files = |declared: &str, used: &str| {
        let base = format!("package p edition \"1\"\n\nnamespace p.base\n{declared}A helper means a part of the system.\n\nnamespace p.app\n{used}A helper means a part of the application.\n[W] When the helper finishes, the API shall log the result.\n");
        Fixture::raw(&[("trion.toml", manifest), ("p.trion", &base)]).trion(&["verify", "--json"]).json()
    };
    let system = |report: &Value| report["environment"]["control"]["system"].as_array().unwrap().iter().any(|a| a.as_str().unwrap().ends_with("app::helper"));
    // Without a declaration, an actor that a condition waits for is the environment's.
    assert!(!system(&files("", "use p.base\n")));
    // The declaration of the used namespace reaches the term that this namespace defines itself.
    assert!(system(&files("system helper\n", "use p.base\n")), "{}", files("system helper\n", "use p.base\n"));
    // A namespace that does not use the declaring namespace is not reached.
    assert!(!system(&files("system helper\n", "")));
}

#[test]
fn a_relation_without_an_object_counts_in_its_role_phrase() {
    let text = "There is a declaration.\n[A] Each declaration belongs to exactly one namespace.\n";
    assert!(codes(text).is_empty());
    assert_eq!(codes(&format!("{text}[B] Each declaration belongs to at least two namespaces.\n")), ["contradiction"]);
    assert!(silent(&check(text), "opaque").is_empty());
}

#[test]
fn a_for_each_head_binds_its_whole_noun_phrase() {
    let text = "For each adverb of time A:\n    [K] The formalizer shall keep A outside the name of the action of A.\n    [L] A parser shall read A.\nFor each reference R from a statement to a source:\n    [M] The checker shall resolve R.\nFor each room R:\n    For each member M of R:\n        [N] The API shall notify M.\n";
    assert!(codes(text).is_empty(), "{:?}", codes(text));
    let expansion = Fixture::new(&[("a.trion", text)]).inspect(&["expand", "a.trion"]).stdout;
    // The variable is replaced by the noun phrase that it binds.
    assert!(expansion.contains("The formalizer shall keep the adverb of time outside the name of the action of the adverb of time."), "{expansion}");
    // At the start of a sentence `A` before a noun is the article.
    assert!(expansion.contains("A parser shall read the adverb of time."), "{expansion}");
    assert!(expansion.contains("The checker shall resolve the reference from a statement to a source."), "{expansion}");
    assert!(expansion.contains("The API shall notify the member of the room."), "{expansion}");
}

#[test]
fn a_for_each_frame_opens_one_sentence() {
    let text = "[A] For each request R, the API shall log R.\n[C] For each open room R, when a user joins R, the API shall notify the owner of R.\n";
    assert!(codes(text).is_empty(), "{:?}", codes(text));
    let expansion = Fixture::new(&[("a.trion", text)]).inspect(&["expand", "a.trion"]).stdout;
    assert!(expansion.contains("The API shall log the request."), "{expansion}");
    assert!(expansion.contains("When a user joins the open room, the API shall notify the owner of the open room."), "{expansion}");
    // The frame binds for its sentence only.
    assert_eq!(codes("[A] For each request R, the API shall log R.\n[B] The API shall store R.\n"), ["UNBOUND_VARIABLE"]);
    assert_eq!(codes("[A] For each request R, the API shall log R.\n[B] For each request, the API shall not log the request.\n"), ["contradiction"]);
}
