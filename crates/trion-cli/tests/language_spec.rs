//! Behaviour of the language edition 0.1.0-draft.1: blocks, composition,
//! flows, concept diagrams, checks, conformance examples and reader views.

mod common;
use common::*;
use serde_json::Value;

fn check(text: &str) -> Value {
    Fixture::new(&[("a.trion", text)]).trion(&["verify", "--json", "a.trion"]).json()
}

fn codes(text: &str) -> Vec<String> {
    report_codes(&check(text))
}

fn run(args: &[&str], text: &str) -> String {
    let f = Fixture::new(&[("a.trion", text)]);
    let mut all = args.to_vec();
    all.push("a.trion");
    let r = f.trion(&all);
    format!("{}{}", r.stdout, r.stderr)
}

/// As above, reading what the libraries read instead of running the command.
fn view(args: &[&str], text: &str) -> String {
    let f = Fixture::new(&[("a.trion", text)]);
    let mut all = args.to_vec();
    all.push("a.trion");
    let r = f.inspect(&all);
    format!("{}{}", r.stdout, r.stderr)
}

// Sections and shared contexts.

#[test]
fn a_section_groups_statements_without_meaning() {
    assert_eq!(codes("section \"Stopping\":\n    [A] The API shall stop.\nsection \"Other\":\n    [B] The API shall not stop.\n"), ["contradiction"]);
}

#[test]
fn a_shared_context_applies_its_condition_to_each_statement() {
    let text = "When the API receives a call:\n    [A] the API shall log the call.\n    [B] the API shall not log the call.\n";
    assert_eq!(codes(text), ["contradiction"]);
    let model = view(&["model"], text);
    assert!(model.contains("Event(API receive call)"), "{model}");
}

#[test]
fn a_shared_context_holds_at_most_one_trigger() {
    let text = "When the API receives a call:\n    When the bell rings, the API shall stop.\n";
    assert_eq!(codes(text), ["context-second-trigger"]);
}

#[test]
fn a_bound_subject_is_replaced_by_its_description() {
    let text = "[A] When the compiler receives a resolved specification S, the compiler shall check S.\n";
    let expansion = view(&["expand"], text);
    assert!(expansion.contains("check the resolved specification"), "{expansion}");
}

#[test]
fn a_reference_names_an_existing_statement() {
    assert!(codes("[A] The API shall stop.\nref [A]\n").is_empty());
    assert_eq!(codes("[A] The API shall stop.\nref [B]\n"), ["UNRESOLVED_REFERENCE"]);
}

#[test]
fn identifiers_are_unique_in_a_package() {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "[A] The API shall stop.\n"), ("b.trion", "namespace p.other:\n    [A] The bell shall ring.\n")]);
    assert_eq!(report_codes(&f.trion(&["verify", "--json"]).json()), ["DUPLICATE_ID"]);
}

// Response composition.

#[test]
fn an_all_list_requires_each_action() {
    let list = "[A] The API shall perform all of the following actions:\n    stop;\n    log the stop;\n";
    assert_eq!(codes(&format!("{list}[B] The API shall not stop.\n")), ["contradiction"]);
    assert!(codes(list).is_empty());
}

#[test]
fn a_some_list_requires_one_action_or_more() {
    let list = "[A] The API shall perform one or more of the following actions:\n    stop;\n    pause;\n";
    assert!(codes(&format!("{list}[B] The API shall not stop.\n")).is_empty());
    assert_eq!(codes(&format!("{list}[B] The API shall not stop.\n[C] The API shall not pause.\n")), ["contradiction"]);
}

#[test]
fn a_one_list_requires_exactly_one_action() {
    let list = "[A] The API shall perform exactly one of the following actions:\n    stop;\n    pause;\n";
    assert!(codes(&format!("{list}[B] The API shall stop.\n")).is_empty());
    assert_eq!(codes(&format!("{list}[B] The API shall stop.\n[C] The API shall pause.\n")), ["contradiction"]);
}

#[test]
fn a_sequence_requires_each_action_in_order() {
    let list = "[A] The API shall perform the following actions in order:\n    stop;\n    pause;\n";
    assert_eq!(codes(&format!("{list}[B] The API shall not pause.\n")), ["contradiction"]);
}

#[test]
fn lists_nest_and_items_carry_identifiers() {
    let text = "[A] The API shall perform all of the following actions:\n    [A/first] stop;\n    perform exactly one of the following actions:\n        [A/left] pause;\n        [A/right] wait;\n[B] The API shall pause.\n[C] The API shall wait.\n";
    assert_eq!(codes(text), ["contradiction"]);
}

#[test]
fn an_action_list_is_well_formed() {
    assert_eq!(codes("[A] The API shall perform all of the following actions:\n    stop\n")[0], "parse-composition");
    assert_eq!(codes("[A] The API shall perform all of the following actions:\n")[0], "parse-composition");
}

#[test]
fn mixed_operators_need_grouping() {
    assert_eq!(codes("When a request fails, the client shall record the failure and retry the request or notify the operator.\n"), ["UNGROUPED_RESPONSE_OPERATORS"]);
}

// Sentences beyond EARS.

#[test]
fn a_necessary_condition_constrains_only_its_claim() {
    let model = view(&["model"], "[A] The API shall stop only when status is Closed.\n");
    assert!(model.contains("(Act(API|stop) ∧ ¬Forbid(API|stop) ∧ ¬Discouraged(API|stop)) → Val(status, Closed)"), "{model}");
}

#[test]
fn an_exact_condition_is_both_sufficient_and_necessary() {
    let model = view(&["model"], "[B] The API shall start exactly when the bell rings.\n");
    assert!(model.contains("(Event(bell ring) → (Act(API|start)"), "{model}");
    assert!(model.contains("¬Discouraged(API|start)) → Event(bell ring))"), "{model}");
}

#[test]
fn an_existence_statement_makes_a_universal_rule_bite() {
    let rules = "Each source document has exactly one source identity.\nEach source document has exactly zero source identities.\n";
    assert!(codes(rules).is_empty(), "an empty domain satisfies both");
    assert_eq!(codes(&format!("There is a source document D.\n{rules}")), ["contradiction"]);
}

#[test]
fn relation_cardinalities_compose() {
    assert_eq!(codes("There is a user U.\nEach user has at most one account.\nEach user has at least two accounts.\n"), ["contradiction"]);
    assert!(codes("There is a user U.\nEach user has at most two accounts.\nEach user has at least two accounts.\n").is_empty());
}

#[test]
fn a_statement_outside_controlled_english_is_rejected() {
    assert_eq!(codes("[A] パーサーは入力を拒否しなければならない。\n"), ["NOT_CONTROLLED_ENGLISH"]);
    assert_eq!(codes("[A] The trion language for every EARS pattern.\n"), ["MISSING_PREDICATE"]);
}

// Flows.

const FLOW_HEAD: &str = "[F] When the checker receives a result R, the checker shall follow this flow:\n    step inspect: read R;\n    step good: publish the success for R;\n    step bad: publish the failure for R;\n    start inspect\n";

#[test]
fn a_flow_reads_as_its_ordered_actions() {
    let text = "[T]\nWhen the compiler receives a resolved specification S,\nthe compiler shall perform the following actions in order:\n    construct the formal model of S;\n    check the formal model of S;\n[F]\nWhen the compiler receives a resolved specification S,\nthe compiler shall follow this flow:\n    step model: construct the formal model of S;\n    step verify: check the formal model of S;\n    start model\n    model -> verify\n    finish verify\ncheck SAME:\n    relation equivalent\n    left [T]\n    right [F]\n    using definitions\n";
    let report = check(text);
    assert!(report_codes(&report).is_empty(), "{report}");
    assert_eq!(report["checks"][0]["result"], "proved");
}

#[test]
fn exclusive_and_complete_guards_pass() {
    let text = format!("{FLOW_HEAD}    choose after inspect:\n        when status is Valid -> good\n        when status is not Valid -> bad\n    finish good\n    finish bad\n");
    let found = codes(&text);
    assert!(!found.contains(&"OVERLAPPING_FLOW_GUARDS".to_string()) && !found.contains(&"INCOMPLETE_FLOW_CHOICE".to_string()), "{found:?}");
}

#[test]
fn overlapping_guards_are_an_error() {
    let text = format!("{FLOW_HEAD}    choose after inspect:\n        when the count is at least 1 -> good\n        when the count is at least 2 -> bad\n        otherwise -> bad\n    finish good\n    finish bad\n");
    assert!(codes(&text).contains(&"OVERLAPPING_FLOW_GUARDS".to_string()), "{:?}", codes(&text));
}

#[test]
fn a_choice_without_otherwise_must_cover_every_case() {
    let text = format!("{FLOW_HEAD}    choose after inspect:\n        when the count is at least 2 -> good\n        when the count is at most 0 -> bad\n    finish good\n    finish bad\n");
    assert!(codes(&text).contains(&"INCOMPLETE_FLOW_CHOICE".to_string()), "{:?}", codes(&text));
}

#[test]
fn an_uninterpreted_guard_is_an_obligation() {
    let text = format!("{FLOW_HEAD}    choose after inspect:\n        when the bell rings -> good\n        when the alarm sounds -> bad\n    finish good\n    finish bad\n");
    let report = check(&text);
    let warnings: Vec<&Value> = report["diagnostics"].as_array().unwrap().iter().filter(|d| d["code"] == "flow-guard-obligation").collect();
    assert!(!warnings.is_empty(), "{report}");
    assert!(warnings.iter().all(|d| d["severity"] == "warning"));
}

#[test]
fn a_flow_cycle_is_unsupported() {
    let text = format!("{FLOW_HEAD}    inspect -> good\n    good -> inspect\n    finish bad\n");
    assert!(codes(&text).contains(&"UNSUPPORTED_FLOW_CYCLE".to_string()), "{:?}", codes(&text));
}

#[test]
fn a_flow_has_one_start_and_a_finish() {
    let text = "[F] When the checker receives a result R, the checker shall follow this flow:\n    step inspect: read R;\n    finish inspect\n";
    assert!(codes(text).contains(&"FLOW_START".to_string()), "{:?}", codes(text));
    let text = "[F] When the checker receives a result R, the checker shall follow this flow:\n    step inspect: read R;\n    start inspect\n";
    assert!(codes(text).contains(&"FLOW_BAD_REFERENCE".to_string()), "{:?}", codes(text));
}

// Concept diagrams.

const CONCEPT: &str = "[TEXT-A]\nEach specification contains zero or more normative statements.\n[TEXT-B]\nEach normative statement denotes exactly one expression.\n[C] concept:\n    [C/a] each specification -> contains -> zero or more normative statements;\n    [C/b] each normative statement -> denotes -> exactly one expression;\n";

#[test]
fn a_concept_diagram_is_equivalent_to_its_sentences() {
    let report = check(&format!("{CONCEPT}check SAME:\n    relation equivalent\n    left [TEXT-A], [TEXT-B]\n    right [C]\n    using definitions\n"));
    assert!(report_codes(&report).is_empty(), "{report}");
    assert_eq!(report["checks"][0]["result"], "proved");
}

#[test]
fn a_check_with_different_sides_is_refuted() {
    let report = check(&format!("{CONCEPT}check DIFFERENT:\n    relation equivalent\n    left [TEXT-A]\n    right [C]\n    using definitions\n"));
    assert_eq!(report_codes(&report), ["check-refuted"]);
    assert_eq!(report["checks"][0]["result"], "refuted");
}

#[test]
fn a_check_names_existing_statements() {
    let report = check(&format!("{CONCEPT}check GONE:\n    relation equivalent\n    left [TEXT-A]\n    right [NOPE]\n    using definitions\n"));
    assert!(report_codes(&report).contains(&"UNRESOLVED_REFERENCE".to_string()), "{report}");
}

#[test]
fn a_concept_edge_expands_to_a_sentence() {
    let expansion = view(&["expand"], CONCEPT);
    assert!(expansion.contains("[C/b]\nEach normative statement denotes exactly one expression."), "{expansion}");
}

#[test]
fn an_unknown_diagram_kind_is_unsupported() {
    assert_eq!(codes("[D] diagram sequence:\n    a -> b\n"), ["UNSUPPORTED_DIAGRAM_KIND"]);
}

// Conformance examples.

fn example(kind: &str, fields: &str) -> String {
    format!("[NOTE-TEXT]\nWhen the checker finds a contradiction C,\nthe checker shall perform all of the following actions:\n    record C;\n    notify the author about C;\n[NOTE-FLOW]\nWhen the checker finds a contradiction C,\nthe checker shall follow this flow:\n    step keep: record C;\n    step tell: notify the author about C;\n    start keep\n    keep -> tell\n    finish tell\nexample E:\n    kind {kind}\n    {fields}")
}

fn example_outcome(kind: &str, fields: &str) -> (Vec<String>, Value) {
    let report = check(&example(kind, fields));
    (report_codes(&report), report["examples"][0].clone())
}

#[test]
fn a_syntax_example_reports_acceptance_or_its_diagnostic() {
    let (found, outcome) = example_outcome("syntax", "    form statement\n    input \"The parser shall preserve source locations.\"\n    expect accepted\n");
    assert!(found.is_empty(), "{found:?}");
    assert_eq!(outcome["observed"], "accepted");
    let (found, _) = example_outcome("syntax", "    form statement\n    input \"The trion language for every EARS pattern.\"\n    expect rejected \"MISSING_PREDICATE\"\n");
    assert!(found.is_empty(), "{found:?}");
    let (found, _) = example_outcome("syntax", "    form fragment\n    input \"\"\"\nnamespace x:\n    source R:\n        title \"t\"\n        locator \"l\"\n        quote Q \"仕様記述言語を作成します。\"\n\"\"\"\n    expect accepted\n");
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_comparison_example_classifies_the_candidate() {
    let (found, outcome) = example_outcome("comparison", "    base [NOTE-TEXT]\n    candidate [NOTE-FLOW]\n    using definitions\n    expect extension\n");
    assert!(found.is_empty(), "{found:?}");
    assert_eq!(outcome["observed"], "extension");
    let (found, _) = example_outcome("comparison", "    base [NOTE-FLOW]\n    candidate [NOTE-TEXT]\n    using definitions\n    expect redundant\n");
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_consistency_example_uses_only_its_input_and_definitions() {
    let (found, _) = example_outcome("consistency", "    input \"\"\"\nThere is a source document D.\nEach source document has exactly one source identity.\nEach source document has exactly zero source identities.\n\"\"\"\n    expect inconsistent\n");
    assert!(found.is_empty(), "{found:?}");
    let (found, _) = example_outcome("consistency", "    input \"The checker shall not record the contradiction.\"\n    expect consistent\n");
    assert!(found.is_empty(), "the package's own rules are excluded: {found:?}");
}

#[test]
fn an_unmet_expectation_fails_and_keeps_both_results() {
    let (found, outcome) = example_outcome("comparison", "    base [NOTE-TEXT]\n    candidate [NOTE-FLOW]\n    using definitions\n    expect redundant\n");
    assert_eq!(found, ["example-failed"]);
    assert_eq!((outcome["expected"].as_str(), outcome["observed"].as_str()), (Some("redundant"), Some("extension")));
}

#[test]
fn an_example_that_cannot_run_is_invalid() {
    let (found, _) = example_outcome("comparison", "    base [NOPE]\n    candidate [NOTE-FLOW]\n    using definitions\n    expect extension\n");
    assert!(found.contains(&"example-invalid".to_string()), "{found:?}");
    let report = check("example E:\n    kind proof\n    expect proved\n");
    assert!(report_codes(&report).contains(&"parse-example".to_string()), "{report}");
}

// Reader views.

#[test]
fn expand_writes_inherited_conditions_out() {
    let text = "When the API receives a call:\n    [A] the API shall log the call.\n";
    let expansion = view(&["expand"], text);
    assert!(expansion.contains("[A]\nWhen the API receives a call, the API shall log the call."), "{expansion}");
    let json: Value = serde_json::from_str(&view(&["expand", "--json"], text)).unwrap();
    assert_eq!(json[0]["id"], "A");
}

#[test]
fn the_glossary_is_generated_with_the_origin_of_each_term() {
    let text = "term API: entity\nA room means a shared channel.\nThe API shall open a room.\n";
    let json: Value = serde_json::from_str(&view(&["glossary", "--json"], text)).unwrap();
    let status = |term: &str| json.as_array().unwrap().iter().find(|e| e["term"] == term).map(|e| e["status"].as_str().unwrap().to_string());
    assert_eq!(status("API").as_deref(), Some("explicit"));
    assert_eq!(status("room").as_deref(), Some("explicit"));
    assert_eq!(status("open").as_deref(), Some("derived"));
    assert!(view(&["glossary"], text).lines().any(|l| l.starts_with("room\texplicit")));
}

#[test]
fn the_check_summary_counts_checks_and_examples() {
    let text = format!("{CONCEPT}check SAME:\n    relation equivalent\n    left [TEXT-A], [TEXT-B]\n    right [C]\n    using definitions\nexample E:\n    kind syntax\n    form statement\n    input \"The API shall stop.\"\n    expect accepted\n");
    let out = run(&["verify"], &text);
    assert!(out.contains("1/1 checks proved, 1 examples run"), "{out}");
}
