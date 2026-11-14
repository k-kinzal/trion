//! Rules of the language draft (edition 0.1.0-draft.1), observed through the
//! `trion` command. Rules the implementation does not yet satisfy are not
//! tested here; they are listed for follow-up instead.

mod common;
use common::*;
use serde_json::Value;

// Diagrams, flows, conformance examples, EARS and the package overview.

fn a_check(text: &str) -> Value {
    Fixture::new(&[("a.trion", text)]).trion(&["verify", "--json", "a.trion"]).json()
}

fn a_codes(text: &str) -> Vec<String> {
    report_codes(&a_check(text))
}

/// As above, reading what the libraries read instead of running the command.
fn a_view(args: &[&str], text: &str) -> String {
    let f = Fixture::new(&[("a.trion", text)]);
    let mut all = args.to_vec();
    all.push("a.trion");
    let r = f.inspect(&all);
    format!("{}{}", r.stdout, r.stderr)
}

/// The messages of the diagnostics with `code`.
fn a_messages(text: &str, code: &str) -> Vec<String> {
    a_check(text)["diagnostics"].as_array().unwrap().iter().filter(|d| d["code"] == code).map(|d| d["message"].as_str().unwrap().to_string()).collect()
}

// Diagrams in general.

#[test]
fn a_concept_edge_is_formalized_like_english_and_its_conflicts_name_the_edge() {
    let diagram = "alias buyer = customer\n[C] concept:\n    [C/a] each order -> has -> exactly one buyer;\n[T] There is an order.\n";
    // The edge adds a constraint no sentence states, and nothing conflicts.
    assert!(a_codes(diagram).is_empty(), "{:?}", a_codes(diagram));
    // The alias and the plural resolve in the diagram as in English, so the
    // edge contradicts a sentence about customers.
    let report = a_check(&format!("{diagram}[U] Each order has at least two customers.\n"));
    let diagnostics = report["diagnostics"].as_array().unwrap();
    assert_eq!(diagnostics.len(), 1, "{report}");
    assert_eq!(diagnostics[0]["code"], "contradiction");
    assert_eq!(diagnostics[0]["severity"], "error");
    let refs: Vec<(&str, u64)> = diagnostics[0]["refs"].as_array().unwrap().iter().map(|r| (r["id"].as_str().unwrap(), r["line"].as_u64().unwrap())).collect();
    // The authored edge is named by its identifier and its own line.
    assert!(refs.contains(&("C/a", 4)), "{refs:?}");
}

#[test]
fn a_diagram_may_restate_existing_sentences() {
    let text = "[TEXT-A]\nEach order contains exactly one item.\n[C] concept:\n    [C/a] each order -> contains -> exactly one item;\n[T] There is an order.\n";
    assert!(a_codes(text).is_empty(), "{:?}", a_codes(text));
    let flow = "[S] When the checker receives a result R, the checker shall perform the following actions in order:\n    read R;\n    publish R;\n[F] When the checker receives a result R, the checker shall follow this flow:\n    step inspect: read R;\n    step tell: publish R;\n    start inspect\n    inspect -> tell\n    finish tell\n";
    assert!(a_codes(flow).is_empty(), "{:?}", a_codes(flow));
}

const A_CONCEPT_CHECK: &str = "check SAME:\n    relation equivalent\n    left [TEXT]\n    right [C]\n    using definitions\n";

#[test]
fn editing_a_concept_edge_changes_the_specification() {
    let text = "[TEXT]\nEach order contains exactly one item.\n[C] concept:\n    [C/a] each order -> contains -> exactly one item;\n";
    let before = a_check(&format!("{text}{A_CONCEPT_CHECK}"));
    assert_eq!(before["checks"][0]["result"], "proved", "{before}");
    let edited = text.replace("-> exactly one item;", "-> at least two items;");
    let after = a_check(&format!("{edited}{A_CONCEPT_CHECK}"));
    assert_eq!(after["checks"][0]["result"], "refuted", "{after}");
    assert!(a_view(&["expand"], &edited).contains("Each order contains at least two items."));
}

#[test]
fn the_order_and_spacing_of_concept_edges_carry_no_meaning() {
    let text = "[C] concept:\n    [C/a] each order -> contains -> exactly one item;\n    [C/b] each item -> has -> at most one label;\n[D] concept:\n    [D/b]   each item  ->  has  ->  at most one label;\n    [D/a] each order->contains->exactly one item;\n";
    let checks = "check SAME:\n    relation equivalent\n    left [C]\n    right [D]\n    using definitions\ncheck PART:\n    relation equivalent\n    left [C/a]\n    right [D]\n    using definitions\n";
    let report = a_check(&format!("{text}{checks}"));
    assert_eq!(report["checks"][0]["result"], "proved", "{report}");
    // The check can tell different diagrams apart.
    assert_eq!(report["checks"][1]["result"], "refuted", "{report}");
}

// Concept diagrams.

#[test]
fn a_concept_edge_has_each_two_arrows_and_a_semicolon() {
    assert!(a_codes("[C] concept:\n    [C/a] each order -> contains -> exactly one item;\n    each item -> has -> at most one label;\n").is_empty());
    assert_eq!(a_messages("[C] concept:\n    each order -> contains -> exactly one item\n", "parse-concept"), ["a concept edge ends with `;`"]);
    assert_eq!(a_messages("[C] concept:\n    order -> contains -> exactly one item;\n", "parse-concept"), ["a concept edge begins with `each`"]);
    assert_eq!(a_codes("[C] concept:\n    each order -> contains exactly one item;\n"), ["parse-concept"]);
    assert_eq!(a_codes("[C] concept:\n    each order -> contains -> exactly one -> item;\n"), ["parse-concept"]);
}

const A_ORDERS: &str = "[C] concept:\n    [C/a] each order -> contains -> exactly one item;\n";

#[test]
fn a_target_cardinality_counts_the_related_targets() {
    assert_eq!(a_codes(&format!("{A_ORDERS}[T] There is an order.\n[U] Each order contains at least two items.\n")), ["contradiction"]);
    assert!(a_codes(&format!("{A_ORDERS}[T] There is an order.\n[U] Each order contains at most three items.\n")).is_empty());
    assert!(a_codes(&format!("{A_ORDERS}[T] There is an order.\n[U] Each order contains at least one item.\n")).is_empty());
}

#[test]
fn a_concept_edge_does_not_require_an_instance() {
    let none = format!("{A_ORDERS}[U] Each order contains exactly zero items.\n");
    assert!(a_codes(&none).is_empty(), "{:?}", a_codes(&none));
    assert_eq!(a_codes(&format!("{none}[T] There is an order.\n")), ["contradiction"]);
}

#[test]
fn a_relation_missing_from_a_concept_diagram_is_not_prohibited() {
    let text = format!("{A_ORDERS}[T] There is an order.\n[U] Each order has at least one note.\n");
    assert!(a_codes(&text).is_empty(), "{:?}", a_codes(&text));
}

// Flow diagrams.

const A_HEAD: &str = "[F] When the checker receives a result R, the checker shall follow this flow:\n";

fn a_flow(body: &str) -> String {
    format!("{A_HEAD}{body}")
}

#[test]
fn a_step_has_a_name_a_colon_an_action_and_a_semicolon() {
    assert!(a_codes_of_the_analysis(&a_flow("    [F/read] step inspect: read R;\n    step tell: publish R;\n    start inspect\n    inspect -> tell\n    finish tell\n")).is_empty());
    assert!(a_codes_of_the_analysis(&a_flow("    step inspect read R;\n    step tell: publish R;\n    start inspect\n    inspect -> tell\n    finish tell\n")).contains(&"parse-flow".to_string()));
    assert_eq!(a_messages(&a_flow("    step Inspect: read R;\n    step tell: publish R;\n    start Inspect\n    Inspect -> tell\n    finish tell\n"), "parse-flow"), ["a step name is a lowercase component name"]);
    assert!(!a_codes_of_the_analysis(&a_flow("    step inspect: read R;\n    step tell: publish R\n    start inspect\n    inspect -> tell\n    finish tell\n")).is_empty());
}

#[test]
fn a_step_reference_names_a_step_of_the_same_flow() {
    assert_eq!(a_messages(&a_flow("    step inspect: read R;\n    step inspect: publish R;\n    start inspect\n    finish inspect\n"), "FLOW_BAD_REFERENCE"), ["the step `inspect` is declared twice"]);
    assert_eq!(a_messages(&a_flow("    step inspect: read R;\n    start inspect\n    inspect -> tell\n    finish inspect\n"), "FLOW_BAD_REFERENCE"), ["the step `tell` is not declared in this flow"]);
    // A second flow cannot refer to the steps of the first.
    let first = a_flow("    step inspect: read R;\n    step tell: publish R;\n    start inspect\n    inspect -> tell\n    finish tell\n");
    let second = "[G] When the checker receives a request Q, the checker shall follow this flow:\n    step log: log Q;\n    start log\n    log -> inspect\n    finish log\n";
    assert!(a_codes_of_the_analysis(&first).is_empty());
    assert_eq!(a_messages(&format!("{first}{second}"), "FLOW_BAD_REFERENCE"), ["the step `inspect` is not declared in this flow"]);
}

#[test]
fn steps_may_be_declared_after_their_references_and_in_any_order() {
    let text = "[T] When the checker receives a result R, the checker shall perform the following actions in order:\n    read R;\n    publish R;\n[F] When the checker receives a result R, the checker shall follow this flow:\n    start inspect\n    inspect -> tell\n    finish tell\n    step tell: publish R;\n    step inspect: read R;\ncheck SAME:\n    relation equivalent\n    left [T]\n    right [F]\n    using definitions\n";
    let report = a_check(text);
    assert!(report_codes(&report).is_empty(), "{report}");
    assert_eq!(report["checks"][0]["result"], "proved");
    let expansion = a_view(&["expand"], text);
    assert!(expansion.contains("[F]\nWhen the checker receives a result, the checker shall perform the following actions in order:\n    read the result;\n    publish the result;"), "{expansion}");
}

#[test]
fn start_finish_and_edges_name_declared_steps() {
    let steps = "    step inspect: read R;\n    step tell: publish R;\n";
    assert!(a_codes_of_the_analysis(&a_flow(&format!("{steps}    start inspect\n    inspect -> tell\n    finish tell\n"))).is_empty());
    assert_eq!(a_messages(&a_flow(&format!("{steps}    start nowhere\n    inspect -> tell\n    finish tell\n")), "FLOW_BAD_REFERENCE"), ["the step `nowhere` is not declared in this flow"]);
    assert_eq!(a_messages(&a_flow(&format!("{steps}    start inspect\n    inspect -> tell\n    finish nowhere\n")), "FLOW_BAD_REFERENCE"), ["the step `nowhere` is not declared in this flow"]);
    assert!(a_messages(&a_flow(&format!("{steps}    start inspect\n    inspect => tell\n    finish tell\n")), "parse-flow").contains(&"a flow holds steps, one start, edges, choices and finishes".to_string()));
}

const A_STEPS: &str = "    step inspect: read R;\n    step good: publish the success for R;\n    step bad: publish the failure for R;\n    start inspect\n";
const A_FINISHES: &str = "    finish good\n    finish bad\n";

#[test]
fn a_choice_holds_guarded_targets_and_an_otherwise() {
    let choice = |body: &str| a_flow(&format!("{A_STEPS}    choose after inspect:\n{body}{A_FINISHES}"));
    assert!(a_codes_of_the_analysis(&choice("        when the count is at least 2 -> good\n        otherwise -> bad\n")).is_empty());
    assert_eq!(a_messages(&a_flow(&format!("{A_STEPS}    choose after inspect\n        otherwise -> bad\n{A_FINISHES}")), "parse-flow"), ["write `choose after <step>:`"]);
    assert_eq!(a_messages(&choice("        when the count is at least 2 good\n        otherwise -> bad\n"), "parse-flow"), ["write `when <condition> -> <step>`"]);
    assert_eq!(a_messages(&choice("        when the count is at least 2 -> good\n        otherwise bad\n"), "parse-flow"), ["a choice holds `when ... -> ...` and `otherwise -> ...`"]);
    assert_eq!(a_messages(&choice("        inspect -> good\n        otherwise -> bad\n"), "parse-flow"), ["a choice holds `when ... -> ...` and `otherwise -> ...`"]);
}

const A_LINEAR: &str = "    step inspect: read R;\n    step tell: publish the success for R;\n    start inspect\n    inspect -> tell\n    finish tell\n";

fn a_linear(modal: &str) -> String {
    format!("[F] When the checker receives a result R, the checker {modal} follow this flow:\n{A_LINEAR}")
}

const A_IN_ORDER: &str = "[S] When the checker receives a result R, the checker shall perform the following actions in order:\n    read R;\n    publish the success for R;\n";

#[test]
fn a_prohibited_flow_prohibits_its_whole_pattern_only() {
    let prohibited = a_linear("shall not");
    // Each step on its own, and both steps without the flow's order, remain allowed.
    assert!(a_codes(&format!("{prohibited}[N] The checker shall read the result.\n")).is_empty());
    assert!(a_codes(&format!("{prohibited}[N] The checker shall read the result.\n[M] The checker shall publish the success for the result.\n")).is_empty());
    // Leaving out a step is one way not to follow the flow.
    assert!(a_codes(&format!("{prohibited}[N] The checker shall not read the result.\n")).is_empty());
    // The complete pattern is what is prohibited.
    assert_eq!(a_codes(&format!("{prohibited}{A_IN_ORDER}")), ["contradiction"]);
}

#[test]
fn a_permitted_flow_admits_its_pattern_without_requiring_it() {
    let permitted = a_linear("may");
    // A recommendation against a step conflicts with an obligation to follow the flow, not with a permission.
    assert_eq!(a_codes(&format!("{}[N] The checker should not read the result.\n", a_linear("shall"))), ["recommendation-violation"]);
    assert!(a_codes(&format!("{permitted}[N] The checker should not read the result.\n")).is_empty());
    // The permission admits the complete matching response.
    assert!(a_codes(&format!("{permitted}{A_IN_ORDER}")).is_empty());
    assert_eq!(a_codes(&format!("{permitted}[N] The checker shall not read the result.\n")), ["contradiction"]);
    // The activation binds R in every step.
    assert!(a_view(&["expand"], &permitted).contains("    read the result;\n    publish the success for the result;"), "{}", a_view(&["expand"], &permitted));
}

#[test]
fn a_flow_edge_orders_its_steps() {
    let reversed = "[S] When the checker receives a result R, the checker shall perform the following actions in order:\n    publish the success for R;\n    read R;\n";
    assert_eq!(a_codes(&format!("{}{reversed}", a_linear("shall"))), ["contradiction"]);
    assert!(a_codes(&format!("{}{A_IN_ORDER}", a_linear("shall"))).is_empty());
}

fn a_choice_flow(guards: &str) -> String {
    a_flow(&format!("{A_STEPS}    choose after inspect:\n{guards}{A_FINISHES}"))
}

const A_OTHERWISE: &str = "        when the count is at least 2 -> good\n        otherwise -> bad\n";

#[test]
fn an_obligatory_flow_requires_the_steps_of_its_selected_path() {
    let flow = a_choice_flow(A_OTHERWISE);
    let no_success = "[N] The checker shall not publish the success.\n";
    let no_failure = "[N] The checker shall not publish the failure.\n";
    // Some path must be completed.
    assert_eq!(a_codes(&format!("{flow}{no_success}[M] The checker shall not publish the failure.\n")), ["contradiction"]);
    // Either path alone may be ruled out while the other stays selectable.
    assert!(a_codes(&format!("{flow}{no_success}")).is_empty());
    // With the guard true, the guarded step is required and the otherwise step is not designated.
    let many = "[I] The count shall be at least 2.\n";
    assert_eq!(a_codes(&format!("{flow}{many}{no_success}")), ["contradiction"]);
    assert!(a_codes(&format!("{flow}{many}{no_failure}")).is_empty());
    // With the guard false, the otherwise target applies.
    let few = "[I] The count shall be less than 2.\n";
    assert_eq!(a_codes(&format!("{flow}{few}{no_failure}")), ["contradiction"]);
    assert!(a_codes(&format!("{flow}{few}{no_success}")).is_empty());
}

#[test]
fn a_flow_does_not_prohibit_other_behavior() {
    let flow = format!("{}[I] The count shall be at least 2.\n", a_choice_flow(A_OTHERWISE));
    // The step of the unselected branch may still happen outside the flow, and so may unrelated actions.
    let text = format!("{flow}[O] The checker shall publish the failure.\n[P] The checker shall notify the operator.\n");
    assert!(a_codes_of_the_analysis(&text).is_empty(), "{:?}", a_codes_of_the_analysis(&text));
}

#[test]
fn guard_order_does_not_set_a_priority() {
    let ascending = "        when the count is at least 2 -> good\n        when the count is less than 2 -> bad\n";
    let descending = "        when the count is less than 2 -> bad\n        when the count is at least 2 -> good\n";
    let compare = |right: &str| {
        let text = format!("{}{}check SAME:\n    relation equivalent\n    left [F]\n    right [G]\n    using definitions\n", a_choice_flow(ascending), a_choice_flow(right).replacen("[F]", "[G]", 1));
        a_check(&text)["checks"][0]["result"].as_str().unwrap().to_string()
    };
    assert_eq!(compare(descending), "proved");
    assert_eq!(compare("        when the count is less than 2 -> good\n        when the count is at least 2 -> bad\n"), "refuted");
    // Overlapping guards are an error whichever comes first, rather than resolved by position.
    for guards in ["        when the count is at least 1 -> good\n        when the count is at least 2 -> bad\n        otherwise -> bad\n", "        when the count is at least 2 -> bad\n        when the count is at least 1 -> good\n        otherwise -> bad\n"] {
        assert_eq!(a_codes_of_the_analysis(&a_choice_flow(guards)), ["OVERLAPPING_FLOW_GUARDS"]);
    }
}

#[test]
fn a_gating_state_is_not_assumed_at_a_later_choice() {
    let text = "[F] While the count is at least 2, when the checker receives a result R, the checker shall follow this flow:\n    step inspect: read R;\n    step good: publish the success for R;\n    start inspect\n    choose after inspect:\n        when the count is at least 2 -> good\n    finish good\n";
    assert_eq!(a_codes_of_the_analysis(text), ["INCOMPLETE_FLOW_CHOICE"]);
}

#[test]
fn each_step_continues_once_and_every_step_is_reachable() {
    let steps = "    step a: read R;\n    step b: publish R;\n    step c: log R;\n    step d: close R;\n    start a\n";
    // Alternative paths may merge.
    let merge = format!("{steps}    choose after a:\n        when the count is at least 2 -> b\n        otherwise -> c\n    b -> d\n    c -> d\n    finish d\n");
    assert!(a_codes_of_the_analysis(&a_flow(&merge)).is_empty(), "{:?}", a_codes_of_the_analysis(&a_flow(&merge)));
    // Two unconditional successors would be parallel.
    let split = format!("{steps}    a -> b\n    a -> c\n    b -> d\n    c -> d\n    finish d\n");
    assert_eq!(a_messages(&a_flow(&split), "FLOW_BAD_REFERENCE"), ["the step `a` needs exactly one successor or one choice"]);
    // A finish step has no successor.
    let past_finish = format!("{steps}    a -> b\n    b -> c\n    c -> d\n    finish c\n    finish d\n");
    assert_eq!(a_messages(&a_flow(&past_finish), "FLOW_BAD_REFERENCE"), ["the finish step `c` has a successor"]);
    // A path that stops before a finish.
    let dead_end = format!("{steps}    a -> b\n    c -> d\n    finish d\n");
    assert_eq!(a_messages(&a_flow(&dead_end), "FLOW_BAD_REFERENCE"), ["the step `b` needs exactly one successor or one choice"]);
    // A step the start never reaches.
    let unreachable = format!("{steps}    a -> b\n    b -> d\n    c -> d\n    finish d\n");
    assert_eq!(a_messages(&a_flow(&unreachable), "FLOW_BAD_REFERENCE"), ["the step `c` is not reachable from the start"]);
}

// Conformance examples.

#[test]
fn an_accepted_syntax_example_says_nothing_about_meaning() {
    let text = "example E:\n    kind syntax\n    form fragment\n    input \"\"\"\n    namespace x:\n        [A] The frobnicator shall frobnicate the widget.\n        [B] The frobnicator shall not frobnicate the widget.\n    \"\"\"\n    expect accepted\n";
    let report = a_check(text);
    assert!(report_codes(&report).is_empty(), "{report}");
    assert_eq!(report["examples"][0]["observed"], "accepted");
    // The same statements written as specifications contradict each other.
    assert_eq!(a_codes("[A] The frobnicator shall frobnicate the widget.\n[B] The frobnicator shall not frobnicate the widget.\n"), ["contradiction"]);
}

// The language as a whole.

#[test]
fn a_controlled_english_statement_compiles_to_a_formal_contract() {
    let text = "[A] When the door opens, the API shall stop.\n";
    let model = a_view(&["model"], text);
    assert!(model.contains("A\n  assume:    Event(door open)\n  guarantee: (Act(API|stop) ∧ ¬Forbid(API|stop) ∧ ¬Discouraged(API|stop))"), "{model}");
    assert_eq!(a_codes(&format!("{text}[B] When the door opens, the API shall not stop.\n")), ["contradiction"]);
}

#[test]
fn each_speech_act_has_its_own_meaning() {
    let text = "[D] A gate means a door.\n[DE] The door is open.\n[O] The API shall stop.\n[P] The API shall not start.\n[R] The API should wait.\n[M] The API may pause.\n";
    let model = a_view(&["model"], text);
    for expected in [
        "DE\n  assume:    ⊤\n  guarantee: Dom(door, open)",
        "O\n  assume:    ⊤\n  guarantee: (Act(API|stop) ∧ ¬Forbid(API|stop) ∧ ¬Discouraged(API|stop))",
        "P\n  assume:    ⊤\n  guarantee: (¬Act(API|start) ∧ Forbid(API|start))",
        "R\n  assume:    ⊤\n  guarantee: (¬Forbid(API|wait) ∧ ¬Discouraged(API|wait))",
        "M\n  assume:    ⊤\n  guarantee: ¬Forbid(API|pause)",
    ] {
        assert!(model.contains(expected), "{expected}\n---\n{model}");
    }
    // A definition introduces a term and an axiom about it, and no obligation.
    let contracts = Fixture::new(&[("a.trion", text)]).inspect(&["model", "--json", "a.trion"]).json();
    let of_definition: Vec<&Value> = contracts["constraints"].as_array().unwrap().iter().filter(|c| c["refs"][0]["id"] == "D").collect();
    assert!(of_definition.iter().all(|c| c["kind"] == "Axiom"), "{contracts}");
    assert!(!of_definition.iter().any(|c| c["guarantee"].to_string().contains("\"Act\"")), "{contracts}");
    assert!(a_view(&["glossary"], text).lines().any(|l| l.starts_with("gate\texplicit")));
}

#[test]
fn one_package_combines_every_authoring_construct() {
    let rules = "section \"Calls\":\n    When the API receives a call C:\n        [A] the API shall perform all of the following actions:\n            log C;\n            answer C;\n";
    let diagram = "[F] When the API receives a call C, the API shall follow this flow:\n    step keep: log C;\n    step reply: answer C;\n    start keep\n    keep -> reply\n    finish reply\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("rules.trion", rules), ("flows.trion", diagram)]);
    let r = f.trion(&["verify", "--json"]);
    assert!(report_codes(&r.json()).is_empty(), "{}", r.stdout);
    let expansion = f.inspect(&["expand"]).stdout;
    assert!(expansion.contains("[A]\nWhen the API receives a call, the API shall perform all of the following actions:\n    log the call;\n    answer the call;"), "{expansion}");
    assert!(expansion.contains("[F]\nWhen the API receives a call, the API shall perform the following actions in order:"), "{expansion}");
    // Both files belong to one specification: a rule in one conflicts with a rule in the other.
    f.write("more.trion", "namespace p:\n    [N] The API shall not answer the call.\n");
    f.write("trion.trion", "package p edition \"test\"\ninclude \"rules.trion\"\ninclude \"flows.trion\"\ninclude \"more.trion\"\n");
    assert!(report_codes(&f.trion(&["verify", "--json"]).json()).contains(&"contradiction".to_string()));
}

#[test]
fn indentation_does_not_determine_structure() {
    let tidy = "section \"S\":\n    When the API receives a call:\n        [A] the API shall log the call.\n";
    let ragged = "section \"S\":\n    When the API receives a call:\n        [A] the API shall log the call.\n";
    let expected = "[A]\nWhen the API receives a call, the API shall log the call.";
    assert!(a_view(&["expand"], tidy).contains(expected));
    assert!(a_view(&["expand"], ragged).contains(expected), "{}", a_view(&["expand"], ragged));
}

fn a_sourced(body: &str) -> Fixture {
    let text = "The API must stop.\n";
    let file = format!("{}{body}", source_block("REQ", "requirement", "req.txt", text, "", &[("STOP", "The API must stop.")]));
    Fixture::new(&[("trion.toml", MANIFEST), ("req.txt", text), ("a.trion", &file)])
}

#[test]
fn a_shared_citation_section_and_condition_cover_a_group() {
    let body = "section \"Stopping\":\n    cite REQ#STOP\n    When the API receives a call:\n        [A] the API shall stop.\n        [B] the API shall log the call.\n    [C] The API shall perform all of the following actions:\n        stop;\n        log the stop;\n";
    let f = a_sourced(body);
    let r = f.trion(&["verify", "--json"]).json()["sources"].clone();
    assert!(report_codes(&r).is_empty(), "{r}");
    let expansion = f.inspect(&["expand"]).stdout;
    assert!(expansion.contains("[B]\nWhen the API receives a call, the API shall log the call."), "{expansion}");
    // A statement outside the group is not covered by its citation.
    let f = a_sourced(&format!("{body}[D] The bell shall ring.\n"));
    let r = f.trion(&["verify", "--json"]).json()["sources"].clone();
    assert_eq!(report_codes(&r), ["unsourced"]);
    assert_eq!(r["diagnostics"][0]["refs"][0]["id"], "D");
}

#[test]
fn statements_need_no_citation_or_test_link_of_their_own() {
    let body = "section \"Stopping\":\n    cite REQ#STOP\n    [A] The API shall stop.\n    [B] The API shall log the stop.\n";
    assert!(report_codes(&a_sourced(body).trion(&["verify", "--json"]).json()["sources"]).is_empty());
}

// Formalization and verification.

fn b_check(text: &str) -> Value {
    Fixture::new(&[("a.trion", text)]).trion(&["verify", "--json", "a.trion"]).json()
}

fn b_run(args: &[&str], text: &str) -> Result {
    let f = Fixture::new(&[("a.trion", text)]);
    let mut all = args.to_vec();
    all.push("a.trion");
    f.trion(&all)
}

/// As above, reading what the libraries read instead of running the command.
fn b_view(args: &[&str], text: &str) -> Result {
    let f = Fixture::new(&[("a.trion", text)]);
    let mut all = args.to_vec();
    all.push("a.trion");
    f.inspect(&all)
}

/// The ids of the statements each constraint of the model refers to first.
fn b_constraint_ids(model: &Value) -> Vec<String> {
    model["constraints"].as_array().unwrap().iter().map(|c| c["refs"][0]["id"].as_str().unwrap().to_string()).collect()
}

/// The observed outcome of the first example of a report.
fn b_example(report: &Value) -> (String, Vec<String>) {
    (report["examples"][0]["observed"].as_str().unwrap_or_default().to_string(), report_codes(report))
}

// Source structure and formal structure.

#[test]
fn authored_resolved_and_formal_forms_share_the_statement_identity() {
    let text = "[A] When the compiler receives a resolved specification S, the compiler shall check S.\n[B] When the compiler receives a resolved specification, the compiler shall not check the resolved specification.\n";
    // The authored structure: the conflict names the statement as written.
    let report = b_check(text);
    let refs = &report["diagnostics"][0]["refs"];
    assert_eq!(refs[0]["id"], "A", "{report}");
    assert_eq!(refs[0]["text"], "When the compiler receives a resolved specification S, the compiler shall check S.");
    // The resolved controlled English.
    let expansion = b_view(&["expand"], text).stdout;
    assert!(expansion.contains("[A]\nWhen the compiler receives a resolved specification, the compiler shall check the resolved specification."), "{expansion}");
    // The formal expression.
    let model = b_view(&["model"], text).stdout;
    assert!(model.contains("A\n  assume:    Event(compiler receive resolved specification)"), "{model}");
}

#[test]
fn normalization_keeps_speech_acts_binders_and_provenance() {
    let text = "[MUST] The API shall stop.\n[MUSTNOT] The API shall not pause.\n[SHOULD] The API should rotate.\n[MAY] The API may wait.\n[BOUND] When the compiler receives a resolved specification S, the compiler shall check S.\n";
    let model = b_view(&["model"], text).stdout;
    // Each speech act keeps a distinct formal shape.
    assert!(model.contains("MUST\n  assume:    ⊤\n  guarantee: (Act(API|stop) ∧ ¬Forbid(API|stop) ∧ ¬Discouraged(API|stop))"), "{model}");
    assert!(model.contains("MUSTNOT\n  assume:    ⊤\n  guarantee: (¬Act(API|pause) ∧ Forbid(API|pause))"), "{model}");
    assert!(model.contains("SHOULD\n  assume:    ⊤\n  guarantee: (¬Forbid(API|rotate) ∧ ¬Discouraged(API|rotate))"), "{model}");
    // The bound subject S denotes the same thing in the trigger and the response.
    assert!(model.contains("Event(compiler receive resolved specification)") && model.contains("Act(compiler|check resolved specification)"), "{model}");
    let json = b_view(&["model", "--json"], text).json();
    let constraints = json["constraints"].as_array().unwrap();
    let may = constraints.iter().find(|c| c["refs"][0]["id"] == "MAY").unwrap();
    assert_eq!(may["kind"], "Permission");
    // Provenance: each constraint keeps the file, line and text of its statement.
    let must = constraints.iter().find(|c| c["refs"][0]["id"] == "MUST").unwrap();
    assert_eq!((must["refs"][0]["file"].as_str(), must["refs"][0]["line"].as_u64(), must["refs"][0]["text"].as_str()), (Some("a.trion"), Some(2), Some("The API shall stop.")));
}

#[test]
fn one_occurrence_satisfies_repeated_and_compatible_statements() {
    // Two statements require stopping and a third allows exactly one action:
    // a single stop satisfies all three.
    let text = "[A] The API shall stop.\n[B] The API shall stop.\n[O] The API shall perform exactly one of the following actions:\n    stop;\n    pause;\n";
    let report = b_check(text);
    assert!(report_codes(&report).is_empty(), "{report}");
    // The exactly-one list does constrain: a second action conflicts.
    assert_eq!(report_codes(&b_check(&format!("{text}[P] The API shall pause.\n"))), ["contradiction"]);
}

#[test]
fn equivalent_statements_keep_their_own_origins() {
    let text = "[A] The API shall stop.\n[B] The API shall stop.\nexample SAME:\n    kind comparison\n    base [A]\n    candidate [B]\n    using definitions\n    expect redundant\n";
    let report = b_check(text);
    assert!(report_codes(&report).is_empty(), "{report}");
    assert_eq!(report["examples"][0]["observed"], "redundant");
    let model = b_view(&["model", "--json"], text).json();
    let constraints = model["constraints"].as_array().unwrap();
    assert_eq!(b_constraint_ids(&model), ["A", "B"]);
    assert_eq!(constraints[0]["guarantee"], constraints[1]["guarantee"], "the formulas are the same");
    assert_eq!((constraints[0]["refs"][0]["line"].as_u64(), constraints[1]["refs"][0]["line"].as_u64()), (Some(2), Some(3)));
}

#[test]
fn each_normative_statement_denotes_one_expression_with_one_source() {
    // Zero statements: an empty specification has an empty model and passes.
    let empty = b_view(&["model", "--json"], "");
    assert_eq!(empty.json()["constraints"].as_array().unwrap().len(), 0);
    assert_eq!(b_run(&["verify"], "").code, 0);
    // A note is not a statement; a composed statement is one expression.
    let text = "section \"S\":\n    note \"Not a statement.\"\n    [A] The API shall stop.\n    [L] The API shall perform all of the following actions:\n        log the stop;\n        pause;\n    [M] The API may wait.\n";
    let model = b_view(&["model", "--json"], text).json();
    assert_eq!(b_constraint_ids(&model), ["A", "L", "M"]);
    for c in model["constraints"].as_array().unwrap() {
        let refs = c["refs"].as_array().unwrap();
        assert_eq!(refs.len(), 1, "{c}");
        assert_eq!(refs[0]["file"], "a.trion");
        assert!(refs[0]["line"].as_u64().unwrap() > 0);
    }
}

#[test]
fn the_compiler_models_checks_and_reports_a_specification() {
    let text = "[T] When the door opens, the API shall perform the following actions in order:\n    stop;\n    pause;\n[F] When the door opens, the API shall follow this flow:\n    step one: stop;\n    step two: pause;\n    start one\n    one -> two\n    finish two\ncheck SAME:\n    relation equivalent\n    left [T]\n    right [F]\n    using definitions\n";
    // The formal model of the specification.
    let model = b_view(&["model"], text).stdout;
    assert!(model.contains("Before(API|stop, API|pause)"), "{model}");
    // The check runs on that model and the report publishes its result.
    let report = b_check(text);
    assert!(report_codes(&report).is_empty(), "{report}");
    assert_eq!(report["checks"][0]["result"], "proved");
    let summary = b_run(&["verify"], text).stdout;
    assert!(summary.contains("1/1 checks proved"), "{summary}");
}

#[test]
fn a_contradiction_is_recorded_and_reported_without_weakening() {
    let text = "[A] The API shall stop.\n[B] The API shall not stop.\n";
    // Recorded in the report.
    let report = b_check(text);
    assert_eq!(report_codes(&report), ["contradiction"]);
    // The author is told, and the run fails rather than dropping a rule.
    let out = b_run(&["verify"], text);
    assert_eq!(out.code, 1);
    assert!(out.stdout.contains("error[contradiction]") && out.stdout.contains("[A] The API shall stop.") && out.stdout.contains("[B] The API shall not stop."), "{}", out.stdout);
    // Both constraints stay in the model as authored.
    let model = b_view(&["model", "--json"], text).json();
    assert_eq!(b_constraint_ids(&model), ["A", "B"]);
}

#[test]
fn an_unsupported_or_unresolved_construct_prevents_success() {
    let fine = "primitive API\n[A] The API shall stop.\n";
    assert_eq!(b_run(&["verify"], fine).code, 0);
    // An unsupported diagram has no formal meaning: the run is not a success.
    let unsupported = b_run(&["verify"], &format!("{fine}[D] diagram sequence:\n    a -> b\n"));
    assert_eq!(unsupported.code, 1, "{}", unsupported.stdout);
    assert!(unsupported.stdout.contains("UNSUPPORTED_DIAGRAM_KIND"), "{}", unsupported.stdout);
    // A check over a statement that does not resolve is not counted as proved.
    let report = b_check(&format!("{fine}check GONE:\n    relation equivalent\n    left [A]\n    right [NOPE]\n    using definitions\n"));
    assert!(report_codes(&report).contains(&"UNRESOLVED_REFERENCE".to_string()), "{report}");
    // The check was asked for, so it stays among the outcomes, and as a
    // check that states no question: a check that vanishes from the report
    // reads as a check that nobody wrote.
    assert_eq!(report["checks"].as_array().unwrap().iter().map(|c| c["result"].as_str().unwrap()).collect::<Vec<_>>(), ["invalid"], "{report}");
    assert!(unverified(&report).contains(&"property_entails".to_string()), "{report}");
    // A relation that this edition does not decide, and a check without its
    // `using` field, are no equivalence that was proved.
    for block in ["check OTHER:\n    relation implies\n    left [A]\n    right [A]\n    using definitions\n", "check BARE:\n    relation equivalent\n    left [A]\n    right [A]\n"] {
        let report = b_check(&format!("{fine}{block}"));
        assert!(report_codes(&report).contains(&"parse-check".to_string()), "{report}");
        assert_eq!(report["checks"][0]["result"], "invalid", "{report}");
    }
}

// Consistency results.

#[test]
fn consistency_means_some_interpretation_satisfies_every_hard_constraint() {
    let example = |input: &str, expect: &str| b_check(&format!("example E:\n    kind consistency\n    input \"\"\"\n    {input}\n    \"\"\"\n    expect {expect}\n"));
    let (observed, codes) = b_example(&example("The API shall stop.\nThe API shall log the stop.", "consistent"));
    assert_eq!(observed, "consistent");
    assert!(codes.is_empty(), "{codes:?}");
    let (observed, codes) = b_example(&example("The API shall stop.\nThe API shall not stop.", "inconsistent"));
    assert_eq!(observed, "inconsistent");
    assert!(codes.is_empty(), "{codes:?}");
}

#[test]
fn a_consistent_specification_can_still_miss_a_case() {
    let text = "[D] The status is Open or Closed.\n[L] When the status is Open, the API shall stop.\n";
    let report = b_check(text);
    assert_eq!(report_codes(&report), ["missing-case"], "consistent, yet incomplete: {report}");
}

#[test]
fn an_undecided_guard_question_is_not_reported_as_proved() {
    let text = "[F] When the checker receives a result R, the checker shall follow this flow:\n    step inspect: read R;\n    step good: publish the success for R;\n    step bad: publish the failure for R;\n    start inspect\n    choose after inspect:\n        when the bell rings -> good\n        when the alarm sounds -> bad\n    finish good\n    finish bad\n";
    let report = b_check(text);
    let open: Vec<&Value> = report["diagnostics"].as_array().unwrap().iter().filter(|d| d["code"] == "flow-guard-obligation").collect();
    assert!(!open.is_empty(), "the question stays open: {report}");
    assert!(open.iter().all(|d| d["message"].as_str().unwrap().contains("neither proved nor refuted")), "{report}");
}

// Comparisons.

#[test]
fn an_inconsistent_base_is_reported_before_the_candidate() {
    let text = "[A] The API shall stop.\n[B] The API shall not stop.\n[C] The API shall not stop.\nexample E:\n    kind comparison\n    base [A], [B]\n    candidate [C]\n    using definitions\n    expect base-inconsistent\n";
    let (observed, codes) = b_example(&b_check(text));
    assert_eq!(observed, "base-inconsistent", "not blamed on the candidate");
    assert!(!codes.contains(&"example-failed".to_string()), "{codes:?}");
}

#[test]
fn a_candidate_that_no_interpretation_shares_with_the_base_conflicts() {
    let text = "[A] When the API receives a call, the API shall stop.\n[C] When the API receives a call, the API shall not stop.\n[D] When the API receives a call, the API shall log the call.\nexample CONFLICT:\n    kind comparison\n    base [A]\n    candidate [C]\n    using definitions\n    expect conflict\nexample FINE:\n    kind comparison\n    base [A]\n    candidate [D]\n    using definitions\n    expect extension\n";
    let report = b_check(text);
    assert_eq!(report["examples"][0]["observed"], "conflict", "{report}");
    assert_eq!(report["examples"][1]["observed"], "extension", "{report}");
    assert!(!report_codes(&report).contains(&"example-failed".to_string()), "{report}");
}

// Checks.

#[test]
fn a_check_accepts_only_the_equivalent_relation() {
    let check = |relation: &str| report_codes(&b_check(&format!("[A] The API shall stop.\n[B] The API shall stop.\ncheck SAME:\n    relation {relation}\n    left [A]\n    right [B]\n    using definitions\n")));
    assert!(check("equivalent").is_empty(), "{:?}", check("equivalent"));
    assert!(check("implies").contains(&"parse-check".to_string()), "{:?}", check("implies"));
}

#[test]
fn a_check_does_not_assume_its_operands_or_its_claim() {
    // Both operands are asserted by the specification. Were they premises, each
    // would entail the other and the check would pass.
    let text = "[A] The API shall stop.\n[B] The API shall log the call.\ncheck SAME:\n    relation equivalent\n    left [A]\n    right [B]\n    using definitions\n";
    let report = b_check(text);
    assert_eq!(report_codes(&report), ["check-refuted"], "{report}");
    // The check is an obligation in the report, not a fact added to the model.
    assert_eq!(report["checks"][0]["result"], "refuted");
    let model = b_view(&["model", "--json"], text).json();
    assert_eq!(b_constraint_ids(&model), ["A", "B"]);
}

// Surface forms, English sentences and vocabulary.

fn c_codes(text: &str) -> Vec<String> {
    report_codes(&Fixture::new(&[("a.trion", text)]).trion(&["verify", "--json", "a.trion"]).json())
}

/// As above, reading what the libraries read instead of running the command.
fn c_view(args: &[&str], text: &str) -> String {
    let f = Fixture::new(&[("a.trion", text)]);
    let mut all = args.to_vec();
    all.push("a.trion");
    let r = f.inspect(&all);
    format!("{}{}", r.stdout, r.stderr)
}

fn c_glossary(f: &Fixture) -> Vec<Value> {
    f.inspect(&["glossary", "--json"]).json().as_array().unwrap().clone()
}

// Source characters and boundaries.

#[test]
fn a_source_file_is_read_as_utf8() {
    let f = Fixture::raw(&[]);
    std::fs::write(f.path().join("bad.trion"), b"namespace main:\n    [A] The API shall stop.\n    note \"caf\xe9\"\n").unwrap();
    let r = f.trion(&["verify", "bad.trion"]);
    assert_eq!(r.code, 2, "{}{}", r.stdout, r.stderr);
    assert!(r.stderr.contains("UTF-8"), "{}", r.stderr);
    f.write("good.trion", "namespace main:\n    primitive API\n    [A] The API shall stop.\n    note \"café, パーサー\"\n");
    assert_eq!(f.trion(&["verify", "good.trion"]).code, 0);
}

#[test]
fn a_nested_item_ends_where_its_indentation_ends() {
    let nested = |close: &str| format!("[B] The API shall perform all of the following actions:\n    perform exactly one of the following actions:\n        stop;\n        pause;\n{close}    log the stop;\n[C] The bell shall ring.\n");
    assert!(c_codes_of_the_analysis(&nested("")).is_empty());
    // The nested list holds two items and the outer list holds the nested list and one more.
    let expansion = c_view(&["expand"], &nested(""));
    assert!(expansion.contains("        stop;\n        pause;\n    log the stop;"), "{expansion}");
    // `end` is not written: neither as a line nor as an item.
    assert_eq!(c_codes_of_the_analysis("[B] The API shall stop.\nend\n"), ["parse-block"]);
}

#[test]
fn a_directive_ends_at_a_line_break_outside_a_string() {
    // A multiline string may carry the directive across lines.
    assert!(c_codes_of_the_analysis("note \"\"\"first\nsecond\"\"\"\n[A] The API shall stop.\nref [A]\n").is_empty());
    // A single-line string does not, and the line break ends the directive.
    assert!(c_codes_of_the_analysis("note \"first\nsecond\"\n[A] The API shall stop.\n").contains(&"parse-note".to_string()));
    // Nothing else follows a directive on its line.
    assert_eq!(c_codes_of_the_analysis("[A] The API shall stop.\nnote \"x\" [B] The bell shall ring.\n"), ["parse-note"]);
    assert_eq!(c_codes_of_the_analysis("[A] The API shall stop.\nref [A] [A]\n"), ["parse-reference"]);
    assert_eq!(c_codes_of_the_analysis("[A] The API shall stop.\nref\n[A]\n"), ["parse-sentence"]);
}

#[test]
fn a_component_name_is_lowercase_letters_digits_and_hyphens() {
    let item = |name: &str| format!("[A] The API shall perform all of the following actions:\n    [A/{name}] stop;\n");
    assert!(c_codes_of_the_analysis(&item("first-step2")).is_empty());
    for bad in ["First", "1st", "first_step"] {
        assert_eq!(c_codes_of_the_analysis(&item(bad)), ["parse-spec-id"], "{bad}");
    }
    let flow = |name: &str| format!("[F] When the door opens, the API shall follow this flow:\n    step {name}: stop;\n    start {name}\n    finish {name}\n");
    assert!(c_codes_of_the_analysis(&flow("check-2")).is_empty());
    assert_eq!(c_codes_of_the_analysis(&flow("Check")), ["parse-flow"]);
}

// Literal structural forms.

#[test]
fn a_note_is_note_and_a_quoted_string() {
    assert!(c_codes("note \"Read this first.\"\n").is_empty());
    assert_eq!(c_codes("note Read this first.\n"), ["parse-note"]);
}

#[test]
fn a_reference_is_ref_and_a_bracketed_identifier() {
    assert!(c_codes_of_the_analysis("[A] The API shall stop.\nref [A]\n").is_empty());
    assert_eq!(c_codes_of_the_analysis("[A] The API shall stop.\nref A\n"), ["parse-reference"]);
    assert_eq!(c_codes_of_the_analysis("[A] The API shall stop.\nref [a]\n"), ["parse-reference"]);
}

#[test]
fn a_source_block_holds_named_source_fields() {
    let source = "source DOC:\n    title \"The document\"\n    locator \"https://example.com/doc\"\n    revision \"3\"\n    select \"section 2\"\n    quote Q \"The API stops.\"\n[A] The API shall stop.\n    cite DOC#Q\n";
    assert!(c_codes_of_the_analysis(source).is_empty());
    assert_eq!(c_codes_of_the_analysis("source DOC:\n    title \"t\"\n    locator \"l\"\n    author \"me\"\n"), ["parse-source"]);
    assert_eq!(c_codes_of_the_analysis("source doc:\n    title \"t\"\n    locator \"l\"\n"), ["parse-name"]);
}

#[test]
fn a_shared_context_opens_with_a_supported_clause() {
    let text = "For each request R:\n    [A] the API shall log R.\nWhere the API is remote:\n    [B] the API shall wait.\nWhile the pump runs:\n    [C] the API shall pause.\nWhen the bell rings:\n    [D] the API shall ring.\nIf the bell fails, then:\n    [E] the API shall stop.\n";
    assert!(c_codes_of_the_analysis(text).is_empty());
    let expansion = c_view(&["expand"], text);
    assert!(expansion.contains("If the bell fails, then the API shall stop."), "{expansion}");
    assert_eq!(c_codes_of_the_analysis("Because the bell rings:\n    [F] the API shall stop.\n"), ["parse-block"]);
}

#[test]
fn an_action_list_head_ends_in_one_of_four_phrases() {
    for phrase in ["perform all of the following actions", "perform one or more of the following actions", "perform exactly one of the following actions", "perform the following actions in order"] {
        assert!(c_codes_of_the_analysis(&format!("[A] The API shall {phrase}:\n    stop;\n    pause;\n")).is_empty(), "{phrase}");
    }
    assert_eq!(c_codes_of_the_analysis("[A] The API shall perform some of the following actions:\n    stop;\n"), ["parse-block"]);
}

#[test]
fn a_flow_holds_steps_one_start_edges_and_finishes_on_their_own_lines() {
    let flow = |body: &str| format!("[F] When a request arrives, the API shall follow this flow:\n    step check: validate the request;\n    step save: store the request;\n{body}");
    assert!(c_codes_of_the_analysis(&flow("    start check\n    check -> save\n    finish save\n")).is_empty());
    assert_eq!(c_codes_of_the_analysis(&flow("    start check\n    start save\n    check -> save\n    finish save\n")), ["FLOW_START"]);
    assert_eq!(c_codes_of_the_analysis(&flow("    start check\n    check -> save\n")), ["FLOW_BAD_REFERENCE"]);
    assert_eq!(c_codes_of_the_analysis(&flow("    start check\n    check -> save\n    finish save\n    save the request\n")), ["parse-flow"]);
    // A line break ends a start, finish or edge: two of them on one line name no step.
    assert_eq!(c_codes_of_the_analysis(&flow("    start check finish save\n    check -> save\n")), ["FLOW_BAD_REFERENCE"]);
    assert_eq!(c_codes_of_the_analysis(&flow("    start check\n    check -> save finish save\n")), ["FLOW_BAD_REFERENCE"]);
}

#[test]
fn a_concept_holds_cardinality_edges_with_optional_identifiers() {
    assert!(c_codes("[K] concept:\n    [K-VALVE] each pump -> has -> exactly one valve;\n    each valve -> belongs to -> exactly one pump;\n").is_empty());
    assert_eq!(c_codes("concept:\n    each pump has a valve;\n"), ["parse-concept"]);
    assert_eq!(c_codes("concept:\n    a pump -> has -> exactly one valve;\n"), ["parse-concept"]);
}

#[test]
fn a_check_holds_relation_left_right_and_using() {
    let check = |name: &str, fields: &str| format!("[A] The API shall stop.\n[B] The API shall stop.\ncheck {name}:\n{fields}");
    let all = "    relation equivalent\n    left [A]\n    right [B]\n    using definitions\n";
    assert!(c_codes(&check("SAME", all)).is_empty());
    assert_eq!(c_codes(&check("SAME", "    relation equivalent\n    left [A]\n    right [B]\n")), ["parse-check"]);
    assert!(c_codes(&check("SAME", "    relation equivalent\n    left [A]\n    using definitions\n")).contains(&"parse-check".to_string()));
    assert_eq!(c_codes(&check("same", all)), ["parse-name"]);
}

#[test]
fn an_example_holds_a_kind_its_inputs_and_one_expect() {
    let example = |fields: &str| format!("example E:\n{fields}");
    assert!(c_codes(&example("    kind syntax\n    form statement\n    input \"The API shall stop.\"\n    expect accepted\n")).is_empty());
    assert!(c_codes(&example("    kind syntax\n    form statement\n    input \"The API shall stop.\"\n    expect accepted\n    expect accepted\n")).contains(&"parse-example".to_string()));
    assert!(c_codes(&example("    kind syntax\n    form statement\n    input \"The API shall stop.\"\n")).contains(&"parse-example".to_string()));
    assert!(c_codes(&example("    form statement\n    input \"The API shall stop.\"\n    expect accepted\n")).contains(&"parse-example".to_string()));
    assert!(c_codes(&example("    kind syntax\n    form statement\n    input The API shall stop.\n    expect accepted\n")).contains(&"parse-example".to_string()));
}

// Nesting and separation of roles.

#[test]
fn a_namespace_holds_declarations_statements_and_blocks() {
    let body = "namespace p.app:\n    use p.lib\n    source DOC:\n        title \"t\"\n        locator \"l\"\n        quote Q \"The API stops.\"\n    cite DOC#Q\n    note \"n\"\n    [A] The API shall stop.\n    ref [A]\n    section \"s\":\n        [B] The API shall log the stop.\n    When the bell rings:\n        [C] the API shall ring.\n    [K] concept:\n        each pump -> has -> exactly one valve;\n    check SAME:\n        relation equivalent\n        left [A]\n        right [A]\n        using definitions\n    example E:\n        kind syntax\n        form statement\n        input \"The API shall stop.\"\n        expect accepted\n";
    let lib = "namespace p.lib:\n    term API: entity\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", body), ("lib.trion", lib)]);
    let codes = analysis_codes(&f.trion(&["verify", "--json"]).json());
    assert!(codes.is_empty(), "{codes:?}");
    for file_level in ["package q edition \"1\"", "include \"other.trion\""] {
        assert_eq!(c_codes_of_the_analysis(&format!("namespace main:\n    {file_level}\n    [A] The API shall stop.\n")), ["parse-placement"], "{file_level}");
    }
}

#[test]
fn a_definition_stays_outside_shared_contexts() {
    assert!(c_codes("A room means a shared channel.\nsection \"s\":\n    A space means a shared area.\n").is_empty());
    assert_eq!(c_codes("When the bell rings:\n    A room means a shared channel.\n"), ["definition-in-context"]);
}

#[test]
fn source_and_use_declarations_sit_directly_in_a_namespace() {
    let lib = "namespace p.lib:\n    term API: entity\n";
    let project = |body: &str| {
        let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &format!("namespace p.app\n{body}")), ("lib.trion", lib)]);
        analysis_codes(&f.trion(&["verify", "--json"]).json())
    };
    let source = "source DOC:\n    title \"t\"\n    locator \"l\"\n";
    assert!(project(&format!("use p.lib\n{source}[A] The API shall stop.\n")).is_empty());
    let inner: String = source.lines().map(|l| format!("    {l}\n")).collect();
    assert_eq!(project(&format!("section \"s\":\n    use p.lib\n{inner}    [A] The API shall stop.\n")), ["parse-placement", "parse-placement"]);
    assert_eq!(project(&format!("When the bell rings:\n    use p.lib\n{inner}    [A] the API shall stop.\n")), ["parse-placement", "parse-placement"]);
}

#[test]
fn checks_and_examples_stay_outside_shared_contexts() {
    let blocks = "check SAME:\n    relation equivalent\n    left [A]\n    right [A]\n    using definitions\nexample E:\n    kind syntax\n    form statement\n    input \"The API shall stop.\"\n    expect accepted\n";
    let indented: String = blocks.lines().map(|l| format!("    {l}\n")).collect();
    assert!(c_codes(&format!("[A] The API shall stop.\n{blocks}")).is_empty());
    assert!(c_codes(&format!("[A] The API shall stop.\nsection \"s\":\n{indented}")).is_empty());
    let in_context = c_codes(&format!("When the bell rings:\n    [A] the API shall stop.\n{indented}"));
    assert_eq!(in_context.iter().filter(|c| *c == "parse-placement").count(), 2, "{in_context:?}");
}

// English statements.

#[test]
fn domain_words_are_usable_without_a_definition() {
    let text = "The flux capacitor shall recalibrate the dilithium matrix.\nThe quorbler is frabjous.\n";
    assert!(c_codes_of_the_analysis(text).is_empty());
    let f = Fixture::new(&[("a.trion", text)]);
    let json: Value = f.inspect(&["glossary", "--json", "a.trion"]).json();
    let status = |term: &str| json.as_array().unwrap().iter().find(|e| e["term"] == term).map(|e| e["status"].as_str().unwrap().to_string());
    for term in ["flux capacitor", "recalibrate", "dilithium matrix", "quorbler", "frabjous"] {
        assert_eq!(status(term).as_deref(), Some("derived"), "{term}");
    }
}

#[test]
fn trailing_conditions_restrict_the_preceding_claim() {
    let model = c_view(&["model"], "[A] The API shall stop when the bell rings.\n[B] The pump is red when the valve is open.\n[C] The pump is blue unless the valve is open.\n[D] The pump is green exactly when the valve is shut.\n");
    let block = |id: &str| model.split(&format!("{id}\n")).nth(1).unwrap().lines().take(2).collect::<Vec<_>>().join("\n");
    assert!(block("A").contains("assume:    Event(bell ring)"), "{model}");
    assert!(block("B").contains("assume:    Val(valve, open)") && block("B").contains("guarantee: Val(pump, red)"), "{model}");
    assert!(block("C").contains("assume:    ¬Val(valve, open)") && block("C").contains("guarantee: Val(pump, blue)"), "{model}");
    assert!(block("D").contains("(Val(valve, shut) → Val(pump, green)) ∧ (Val(pump, green) → Val(valve, shut))"), "{model}");
}

#[test]
fn a_variable_is_an_uppercase_letter_with_optional_digits() {
    let expansion = c_view(&["expand"], "[A] When the API receives a call C1, the API shall log C1.\n[B] When the API receives a call CX, the API shall log CX.\n[C] When the API receives a call c, the API shall log c.\n");
    assert!(expansion.contains("When the API receives a call, the API shall log the call."), "{expansion}");
    assert!(expansion.contains("receives a call CX, the API shall log CX."), "{expansion}");
    assert!(expansion.contains("receives a call c, the API shall log c."), "{expansion}");
}

#[test]
fn a_definite_reference_resolves_to_its_binding() {
    let text = "[E] When a user U sends a request R, the API shall log R for U.\n[S] The API shall perform the following actions in order:\n    open a session S;\n    close S;\n";
    let expansion = c_view(&["expand"], text);
    assert!(expansion.contains("When a user sends a request, the API shall log the request for the user."), "{expansion}");
    assert!(expansion.contains("close the session;"), "{expansion}");
}

// Vocabulary.

#[test]
fn an_ambiguous_term_names_its_candidates() {
    let f = Fixture::new(&[
        ("trion.toml", MANIFEST),
        ("x.trion", "namespace p.a:\n    term API: entity\n"),
        ("y.trion", "namespace p.b:\n    term API: entity\n"),
        ("z.trion", "namespace p.c:\n    use p.a\n    use p.b\n    [S] The API shall stop.\n"),
    ]);
    let json = f.trion(&["verify", "--json"]).json();
    assert_eq!(analysis_codes(&json), ["AMBIGUOUS_TERM"]);
    let message = json["diagnostics"][0]["message"].as_str().unwrap();
    assert!(message.contains("declared by a and b"), "{message}");
}

#[test]
fn ears_terms_resolve_through_the_local_ears_domain() {
    let ears = "namespace trion.reference.ears:\n    [EARS-DOMAIN]\n    EARS means the requirement pattern system of the EARS reference.\n\n    [EARS-PATTERN]\n    An EARS pattern means a requirement shape that identifies a subject and a required response.\n";
    let sentence = "    [LANG-EARS-REFERENCE]\n    The resolver shall resolve \"EARS\" and \"EARS pattern\"\n    through the local EARS term domain.\n";
    let manifest = "[package]\nname = \"trion\"\n";
    let glossary = |uses: &str| c_glossary(&Fixture::new(&[("trion.toml", manifest), ("references/ears.trion", ears), ("english.trion", &format!("namespace trion.english:\n{uses}{sentence}"))]));
    let entry = |entries: &[Value], term: &str| entries.iter().find(|e| e["term"] == term).cloned();
    let resolved = glossary("    use trion.reference.ears\n");
    let unresolved = glossary("");
    for term in ["EARS", "EARS pattern"] {
        let domain = format!("reference.ears::{term}");
        let with = entry(&resolved, &domain).unwrap();
        let without = entry(&unresolved, &domain).unwrap();
        assert_eq!(with["status"], "explicit");
        assert_eq!(with["occurrences"].as_u64().unwrap(), without["occurrences"].as_u64().unwrap() + 1, "{term}");
        assert!(entry(&resolved, &format!("english::{term}")).is_none(), "{term}");
        assert!(entry(&unresolved, &format!("english::{term}")).is_some(), "{term}");
    }
}

// Composition, sections, contexts, files and names.

fn d_check(text: &str) -> Value {
    Fixture::new(&[("a.trion", text)]).trion(&["verify", "--json", "a.trion"]).json()
}

fn d_codes(text: &str) -> Vec<String> {
    report_codes(&d_check(text))
}

/// As above, reading what the libraries read instead of running the command.
fn d_view(args: &[&str], text: &str) -> String {
    let f = Fixture::new(&[("a.trion", text)]);
    let mut all = args.to_vec();
    all.push("a.trion");
    let r = f.inspect(&all);
    format!("{}{}", r.stdout, r.stderr)
}

/// The `guarantee:` line printed by `trion model` for one statement.
fn d_guarantee(text: &str, id: &str) -> String {
    let model = d_view(&["model"], text);
    let mut lines = model.lines().skip_while(|l| *l != id);
    lines.find_map(|l| l.trim().strip_prefix("guarantee: ").map(str::to_string)).unwrap_or_else(|| panic!("{model}"))
}

fn d_assume(text: &str, id: &str) -> String {
    let model = d_view(&["model"], text);
    let mut lines = model.lines().skip_while(|l| *l != id);
    lines.find_map(|l| l.trim().strip_prefix("assume:").map(|s| s.trim().to_string())).unwrap_or_else(|| panic!("{model}"))
}

fn d_check_result(text: &str) -> String {
    let report = d_check(text);
    report["checks"][0]["result"].as_str().unwrap_or_else(|| panic!("{report}")).to_string()
}

const D_SHALL: &str = "(Act(API|stop) ∧ ¬Forbid(API|stop) ∧ ¬Discouraged(API|stop))";
const D_SHALL_PAUSE: &str = "(Act(API|pause) ∧ ¬Forbid(API|pause) ∧ ¬Discouraged(API|pause))";

// Composition.

#[test]
fn a_composition_keeps_its_subject_modal_conditions_exception_and_order() {
    let text = "[A] While the API is active, when the API receives a call C, the API shall perform the following actions in order, unless the override is active:\n    log C;\n    notify every operator about C;\n";
    let assume = d_assume(text, "A");
    assert_eq!(assume, "(Val(API, active) ∧ Event(API receive call) ∧ ¬Val(override, active))");
    let guarantee = d_guarantee(text, "A");
    // The subject and the modal of the head reach every item; the binding C
    // names the same call in both; `every operator` is the action on the operator; the order is a relation.
    assert!(guarantee.contains("Act(API|log call) ∧ ¬Forbid(API|log call) ∧ ¬Discouraged(API|log call)"), "{guarantee}");
    assert!(guarantee.contains("Act(API|notify operator about call)"), "{guarantee}");
    assert!(guarantee.contains("Before(API|log call, API|notify operator about call)"), "{guarantee}");
}

#[test]
fn the_modal_of_a_list_head_applies_to_the_whole_list() {
    let list = "[A] The API shall not perform all of the following actions:\n    stop;\n    pause;\n";
    assert_eq!(d_guarantee(list, "A"), format!("¬({D_SHALL} ∧ {D_SHALL_PAUSE})"));
    // Not doing both is not the same as doing neither.
    assert!(d_codes(&format!("{list}[B] The API shall stop.\n")).is_empty());
    assert_eq!(d_codes(&format!("{list}[B] The API shall stop.\n[C] The API shall pause.\n")), ["contradiction"]);
    let some = "[A] The API shall not perform one or more of the following actions:\n    stop;\n    pause;\n";
    assert_eq!(d_guarantee(some, "A"), format!("¬({D_SHALL} ∨ {D_SHALL_PAUSE})"));
}

#[test]
fn an_ordered_list_under_a_prohibition_matches_a_pattern_only() {
    let banned = "[A] The API shall not perform the following actions in order:\n    stop;\n    pause;\n";
    // Neither action is asserted or forbidden on its own: only the ordered pattern is.
    assert!(d_codes(&format!("{banned}[B] The API shall stop.\n[C] The API shall pause.\n")).is_empty());
    assert!(d_codes(&format!("{banned}[B] The API shall perform the following actions in order:\n    pause;\n    stop;\n")).is_empty());
    assert_eq!(d_codes(&format!("{banned}[B] The API shall perform the following actions in order:\n    stop;\n    pause;\n")), ["contradiction"]);
}

#[test]
fn a_composition_is_not_its_leaves_asserted_one_by_one() {
    let leaves = "[L1] The API shall stop.\n[L2] The API shall pause.\n";
    let same = |list: &str| d_check_result(&format!("{list}{leaves}check SAME:\n    relation equivalent\n    left [A]\n    right [L1], [L2]\n    using definitions\n"));
    let disjunction = "[A] The API shall perform one or more of the following actions:\n    stop;\n    pause;\n";
    let choice = "[A] The API shall perform exactly one of the following actions:\n    stop;\n    pause;\n";
    let ordered = "[A] The API shall perform the following actions in order:\n    stop;\n    pause;\n";
    let permission = "[A] The API may perform all of the following actions:\n    stop;\n    pause;\n";
    let conjunction = "[A] The API shall perform all of the following actions:\n    stop;\n    pause;\n";
    assert_eq!(same(disjunction), "refuted");
    assert_eq!(same(choice), "refuted");
    assert_eq!(same(ordered), "refuted");
    assert_eq!(same(permission), "refuted");
    // Only a plain conjunction is its leaves.
    assert_eq!(same(conjunction), "proved");
    assert_eq!(d_guarantee(disjunction, "A"), format!("({D_SHALL} ∨ {D_SHALL_PAUSE})"));
}

#[test]
fn a_conjunction_imposes_no_order() {
    let forward = "[F] The API shall perform all of the following actions:\n    stop;\n    pause;\n";
    let backward = "[B] The API shall perform all of the following actions:\n    pause;\n    stop;\n";
    let ordered = "[O] The API shall perform the following actions in order:\n    stop;\n    pause;\n";
    let reversed = "[R] The API shall perform the following actions in order:\n    pause;\n    stop;\n";
    let check = |l: &str, r: &str| format!("check SAME:\n    relation equivalent\n    left [{l}]\n    right [{r}]\n    using definitions\n");
    assert_eq!(d_check_result(&format!("{forward}{backward}{}", check("F", "B"))), "proved");
    assert_eq!(d_check_result(&format!("{forward}{ordered}{}", check("F", "O"))), "refuted");
    assert!(!d_guarantee(forward, "F").contains("Before"));
    // A conjunction agrees with either order.
    assert!(d_codes(&format!("{forward}{ordered}")).is_empty());
    assert!(d_codes(&format!("{forward}{reversed}")).is_empty());
}

#[test]
fn an_exception_applies_where_it_is_written() {
    let on_head = "[A] The API shall perform all of the following actions, unless the override is active:\n    stop;\n    pause;\n";
    let on_item = "[A] The API shall perform all of the following actions:\n    stop, unless the override is active;\n    pause;\n";
    let no_stop = "[B] While the override is active, the API shall not stop.\n";
    let no_pause = "[B] While the override is active, the API shall not pause.\n";
    // On the head, the exception covers every item.
    assert!(d_codes(&format!("{on_head}{no_stop}")).is_empty());
    assert!(d_codes(&format!("{on_head}{no_pause}")).is_empty());
    // On an item, it covers that item alone.
    assert!(d_codes(&format!("{on_item}{no_stop}")).is_empty());
    // The prohibition holds while the override is active, and nothing says that
    // the override is ever inactive: the item without the exception meets it there.
    assert_eq!(d_codes(&format!("{on_item}{no_pause}")), ["contradiction"]);
    assert_eq!(d_assume(on_head, "A"), "¬Val(override, active)");
    assert_eq!(d_guarantee(on_item, "A"), format!("((Val(override, active) ∨ {D_SHALL}) ∧ {D_SHALL_PAUSE})"));
}

#[test]
fn each_designated_action_follows_the_completion_of_the_previous() {
    let text = "[A] The API shall perform the following actions in order:\n    stop;\n    perform all of the following actions:\n        log the stop;\n        notify the operator;\n    pause;\n";
    let guarantee = d_guarantee(text, "A");
    for pair in ["Before(API|stop, API|log stop)", "Before(API|stop, API|notify operator)", "Before(API|log stop, API|pause)", "Before(API|notify operator, API|pause)"] {
        assert!(guarantee.contains(pair), "{pair}: {guarantee}");
    }
    // The two actions of the inner conjunction are not ordered.
    assert!(!guarantee.contains("Before(API|log stop, API|notify operator)"), "{guarantee}");
    // The order is strict: the reverse order cannot also hold.
    let forward = "[F] The API shall perform the following actions in order:\n    stop;\n    pause;\n";
    let backward = "[B] The API shall perform the following actions in order:\n    pause;\n    stop;\n";
    assert_eq!(d_codes(&format!("{forward}{backward}")), ["contradiction"]);
}

#[test]
fn an_ordered_list_adds_only_occurrence_and_order() {
    let text = "[A] The API shall perform the following actions in order:\n    stop;\n    pause;\n";
    // No deadline and no success condition: the guarantee is the two actions and their order.
    assert_eq!(d_guarantee(text, "A"), format!("({D_SHALL} ∧ {D_SHALL_PAUSE} ∧ Before(API|stop, API|pause))"));
}

#[test]
fn an_ordered_list_permits_other_behavior() {
    let text = "[A] The API shall perform the following actions in order:\n    stop;\n    pause;\n";
    assert!(d_codes_of_the_analysis(&format!("{text}[B] The API shall log the request.\n")).is_empty());
    assert!(d_codes_of_the_analysis(&format!("{text}[B] The API shall perform the following actions in order:\n    pause;\n    log the pause;\n")).is_empty());
    assert_eq!(d_codes_of_the_analysis(&format!("{text}[B] The API shall not log the request.\n[C] The API shall log the request.\n")), ["contradiction"]);
}

// Bindings in a composition.

fn d_binding(kind: &str) -> String {
    format!("[A] When the API receives a call C, the API shall perform {kind}:\n    create a record R for C;\n    perform all of the following actions:\n        store R;\n        notify the operator about C;\n")
}

#[test]
fn a_binding_reaches_later_items_of_an_ordered_list() {
    let text = d_binding("the following actions in order");
    assert!(d_codes_of_the_analysis(&text).is_empty(), "{:?}", d_codes_of_the_analysis(&text));
    let expansion = d_view(&["expand"], &text);
    assert!(expansion.contains("    create a record for the call;\n    perform all of the following actions:\n        store the record;\n        notify the operator about the call;"), "{expansion}");
}

#[test]
fn a_binding_stays_inside_its_alternative() {
    for kind in ["all of the following actions", "one or more of the following actions", "exactly one of the following actions"] {
        let report = d_check(&d_binding(kind));
        assert_eq!(analysis_codes(&report), ["UNRESOLVED_REFERENCE"], "{kind}: {report}");
        let message = report["diagnostics"][0]["message"].as_str().unwrap();
        assert!(message.contains("`R` was bound in another alternative"), "{message}");
    }
}

// Source identity of diagnostics.

#[test]
fn a_diagnostic_carries_the_authored_source() {
    let report = d_check("[A] When the API receives a call C, the API shall log C.\n[B] The API shall not log the call.\n");
    let diagnostic = &report["diagnostics"][0];
    assert_eq!(diagnostic["code"], "contradiction");
    let refs: Vec<(String, u64, String, String)> = diagnostic["refs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| (r["file"].as_str().unwrap().to_string(), r["line"].as_u64().unwrap(), r["id"].as_str().unwrap().to_string(), r["text"].as_str().unwrap().to_string()))
        .collect();
    // The text is what the author wrote, before the binding C was replaced.
    assert_eq!(refs, [
        ("a.trion".to_string(), 2, "A".to_string(), "When the API receives a call C, the API shall log C.".to_string()),
        ("a.trion".to_string(), 3, "B".to_string(), "The API shall not log the call.".to_string()),
    ]);
}

#[test]
fn an_expanded_composition_keeps_its_identity_and_items() {
    let text = "[A] When the API receives a call C, the API shall perform all of the following actions:\n    [A/log] log C;\n    [A/choice] perform exactly one of the following actions:\n        [A/stop] stop;\n        [A/pause] pause;\n";
    let json: Value = serde_json::from_str(&d_view(&["expand", "--json"], text)).unwrap();
    assert_eq!(json[0]["id"], "A");
    assert_eq!(json[0]["expansion"], "When the API receives a call, the API shall perform all of the following actions:\n    log the call;\n    perform exactly one of the following actions:\n        stop;\n        pause;");
    // Each identified item stays an addressable member of A.
    assert!(d_codes_of_the_analysis(&format!("{text}ref [A/stop]\nref [A/choice]\n")).is_empty());
    assert_eq!(d_codes_of_the_analysis(&format!("{text}ref [A/gone]\n")), ["UNRESOLVED_REFERENCE"]);
}

// Sections.

#[test]
fn several_sections_display_one_declaration() {
    let text = "section \"Stopping\":\n    [A] The API shall stop.\nsection \"Operations\":\n    ref [A]\nsection \"Safety\":\n    ref [A]\n";
    assert!(d_codes_of_the_analysis(text).is_empty(), "{:?}", d_codes_of_the_analysis(text));
    let model = d_view(&["model"], text);
    assert_eq!(model.lines().filter(|l| *l == "A").count(), 1, "{model}");
}

// Shared contexts.

#[test]
fn an_if_then_block_shares_one_activation() {
    let text = "If a request R fails, then:\n    [A] the API shall log R.\n    [B] the API shall notify the operator about R.\n";
    assert_eq!(d_assume(text, "A"), "Event(request fail)");
    assert_eq!(d_assume(text, "B"), "Event(request fail)");
    let expansion = d_view(&["expand"], text);
    assert!(expansion.contains("[A]\nIf a request fails, then the API shall log the request."), "{expansion}");
    assert!(expansion.contains("[B]\nIf a request fails, then the API shall notify the operator about the request."), "{expansion}");
    let conflict = "If the request fails, then:\n    [A] the API shall log the failure.\n[B] If the request fails, then the API shall not log the failure.\n";
    assert_eq!(d_codes(conflict), ["contradiction"]);
}

#[test]
fn a_while_block_restricts_its_statements_to_the_state() {
    let block = "While the API is active:\n    [A] the API shall log the call.\n";
    assert_eq!(d_assume(block, "A"), "Val(API, active)");
    assert!(d_codes(&format!("{block}[B] While the API is inactive, the API shall not log the call.\n")).is_empty());
    assert_eq!(d_codes(&format!("{block}[B] The API shall not log the call.\n")), ["contradiction"]);
}

#[test]
fn a_where_block_restricts_its_statements_to_the_feature() {
    let block = "Where the audit feature is included:\n    [A] the API shall log the call.\n";
    assert_eq!(d_assume(block, "A"), "Val(audit feature, included)");
    assert!(d_codes(&format!("{block}[B] Where the audit feature is excluded, the API shall not log the call.\n")).is_empty());
    assert_eq!(d_codes(&format!("{block}[B] The API shall not log the call.\n")), ["contradiction"]);
}

#[test]
fn nested_contexts_keep_their_kinds_and_order() {
    let text = "Where the audit feature is included:\n    While the API is active:\n        When the API receives a call:\n            [A] the API shall log the call.\n";
    assert_eq!(d_assume(text, "A"), "(Val(audit feature, included) ∧ Val(API, active) ∧ Event(API receive call))");
    let expansion = d_view(&["expand"], text);
    let line = expansion.lines().nth(1).unwrap().to_lowercase();
    assert_eq!(line, "where the audit feature is included, while the api is active, when the api receives a call, the api shall log the call.");
}

fn d_example(name: &str, input: &str, expect: &str) -> String {
    format!("example {name}:\n    kind consistency\n    input \"\"\"\n{input}\"\"\"\n    expect {expect}\n")
}

#[test]
fn a_condition_that_can_hold_is_a_situation_of_its_statement() {
    // Nothing says that the condition never holds, so the statement meets
    // the prohibition where it holds.
    let text = [
        d_example("TRIGGER", "When the bell rings, the API shall stop.\nThe API shall not stop.\n", "inconsistent"),
        d_example("BLOCK", "When the bell rings:\n    the API shall stop.\nThe API shall not stop.\n", "inconsistent"),
        d_example("STATE", "While the door is open, the API shall stop.\nThe API shall not stop.\n", "inconsistent"),
        d_example("FEATURE", "Where the audit feature is included:\n    the API shall stop.\nThe API shall not stop.\n", "inconsistent"),
        d_example("PLAIN", "The API shall stop.\nThe API shall not stop.\n", "inconsistent"),
        d_example("APART", "While the door is open, the API shall stop.\nWhile the door is closed, the API shall not stop.\n", "consistent"),
    ]
    .concat();
    let report = d_check(&text);
    assert!(report_codes(&report).is_empty(), "{report}");
    let observed: Vec<&str> = report["examples"].as_array().unwrap().iter().map(|e| e["observed"].as_str().unwrap()).collect();
    assert_eq!(observed, ["inconsistent", "inconsistent", "inconsistent", "inconsistent", "inconsistent", "consistent"]);
}

#[test]
fn a_binding_ends_with_its_statement() {
    let text = "[A] When the API receives a call C, the API shall log C.\n";
    let expansion = d_view(&["expand"], text);
    assert!(expansion.contains("[A]\nWhen the API receives a call, the API shall log the call."), "{expansion}");
    // The next ordinary statement cannot see C.
    assert_eq!(c_codes_of_the_analysis(&format!("{text}[B] The API shall store C.\n")), ["UNBOUND_VARIABLE"]);
    // A shared binding needs an enclosing context.
    let shared = "When the API receives a call C:\n    [A] the API shall log C.\n    [B] the API shall store C.\n";
    assert!(d_view(&["expand"], shared).contains("[B]\nWhen the API receives a call, the API shall store the call."));
}

// Files.

fn d_package(files: &[(&str, &str)]) -> Fixture {
    let mut all = vec![("trion.toml", MANIFEST)];
    all.extend_from_slice(files);
    Fixture::raw(&all)
}

#[test]
fn an_included_file_inherits_nothing_from_the_file_before_it() {
    let f = d_package(&[
        ("trion.trion", "package p edition \"test\"\ninclude \"a.trion\"\ninclude \"b.trion\"\n"),
        ("a.trion", "namespace p:\n    When the API receives a call C:\n        [A] the API shall log C.\n"),
        ("b.trion", "namespace p:\n    [B] The API shall log C.\n    [D] The API shall stop.\n"),
    ]);
    // C is bound in the other file only, and the condition does not carry over.
    let report = f.trion(&["verify", "--json"]).json();
    assert_eq!(analysis_codes(&report), ["UNBOUND_VARIABLE"], "{report}");
    let model = f.inspect(&["model"]).stdout;
    assert!(model.contains("D\n  assume:    ⊤\n"), "{model}");
}

#[test]
fn a_declaration_in_a_later_file_is_visible_to_an_earlier_one() {
    let f = d_package(&[
        ("trion.trion", "package p edition \"test\"\ninclude \"a.trion\"\ninclude \"b.trion\"\n"),
        ("a.trion", "namespace p:\n    ref [B]\n    [A] The API shall open a room.\n    check SAME:\n        relation equivalent\n        left [B]\n        right [C]\n        using definitions\n"),
        ("b.trion", "namespace p:\n    A room means a shared channel.\n    [B] The API shall stop.\n    [C] The API shall stop.\n"),
    ]);
    let report = f.trion(&["verify", "--json"]).json();
    assert!(analysis_codes(&report).is_empty(), "{report}");
    assert_eq!(report["checks"][0]["result"], "proved");
    let glossary: Value = serde_json::from_str(&f.inspect(&["glossary", "--json"]).stdout).unwrap();
    let room = glossary.as_array().unwrap().iter().find(|e| e["term"] == "room").unwrap();
    assert_eq!(room["status"], "explicit");
}

#[test]
fn moving_a_statement_to_another_file_keeps_its_meaning() {
    let entry = "package p edition \"test\"\ninclude \"a.trion\"\ninclude \"b.trion\"\n";
    let together = d_package(&[
        ("trion.trion", entry),
        ("a.trion", "namespace p.api:\n    When the API receives a call C:\n        [A] the API shall log C.\n    [B] When the API receives a call, the API shall not log the call.\n"),
        ("b.trion", "namespace p.api:\n"),
    ]);
    let apart = d_package(&[
        ("trion.trion", entry),
        ("a.trion", "namespace p.api:\n    When the API receives a call C:\n        [A] the API shall log C.\n"),
        ("b.trion", "namespace p.api:\n    section \"Moved\":\n        [B] When the API receives a call, the API shall not log the call.\n"),
    ]);
    assert_eq!(together.inspect(&["model"]).stdout, apart.inspect(&["model"]).stdout);
    let codes = |f: &Fixture| report_codes(&f.trion(&["verify", "--json"]).json());
    assert_eq!(codes(&together), ["contradiction"]);
    assert_eq!(codes(&apart), ["contradiction"]);
}

// Namespaces.

#[test]
fn a_use_declaration_loads_nothing() {
    let app = "namespace p.app:\n    use p.extra\n    [A] The API shall stop.\n";
    let extra = "namespace p.extra:\n    [B] The API shall not stop.\n";
    let only_app = d_package(&[("trion.trion", "package p edition \"test\"\ninclude \"a.trion\"\n"), ("a.trion", app), ("extra.trion", extra)]);
    let r = only_app.trion(&["verify"]);
    assert!(r.stdout.contains("error[namespace-unknown]: the namespace `p.extra` does not exist"), "{}", r.stdout);
    assert!(r.stdout.contains("checked 1 specifications"), "{}", r.stdout);
    // With the file included, the same constraints are checked whether or not a block uses it.
    let entry = "package p edition \"test\"\ninclude \"a.trion\"\ninclude \"extra.trion\"\n";
    let using = d_package(&[("trion.trion", entry), ("a.trion", app), ("extra.trion", extra)]);
    let plain = d_package(&[("trion.trion", entry), ("a.trion", &app.replace("    use p.extra\n", "")), ("extra.trion", extra)]);
    assert_eq!(using.inspect(&["model"]).stdout, plain.inspect(&["model"]).stdout);
}

#[test]
fn two_definitions_of_one_name_collide() {
    let entry = "package p edition \"test\"\ninclude \"a.trion\"\ninclude \"b.trion\"\n";
    let first = "namespace p:\n    A room means a shared channel.\n    [A] The API shall open a room.\n";
    let colliding = d_package(&[("trion.trion", entry), ("a.trion", first), ("b.trion", "namespace p:\n    A room means a private channel.\n")]);
    let report = colliding.trion(&["verify", "--json"]).json();
    assert_eq!(analysis_codes(&report), ["NAME_COLLISION"]);
    // Neither file wins: both definitions are named.
    let files: Vec<&str> = report["diagnostics"][0]["refs"].as_array().unwrap().iter().map(|r| r["file"].as_str().unwrap()).collect();
    assert_eq!(files, ["a.trion", "b.trion"]);
    let repeated = d_package(&[("trion.trion", entry), ("a.trion", first), ("b.trion", "namespace p:\n    A room means a shared channel.\n")]);
    assert!(analysis_codes(&repeated.trion(&["verify", "--json"]).json()).is_empty());
    let elsewhere = d_package(&[("trion.trion", entry), ("a.trion", first), ("b.trion", "namespace p.other:\n    A room means a private channel.\n")]);
    assert!(analysis_codes(&elsewhere.trion(&["verify", "--json"]).json()).is_empty());
}

// Identity.

// Citations, notes, and examples as isolated inputs.

fn e_check(files: &[(&str, &str)]) -> Vec<String> {
    let mut all = vec![("trion.toml", MANIFEST)];
    all.extend_from_slice(files);
    report_codes(&Fixture::new(&all).trion(&["verify", "--json"]).json())
}

/// As `a_codes`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn a_codes_of_the_analysis(text: &str) -> Vec<String> {
    analysis_codes(&a_check(text))
}

/// As `b_example`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn b_example_of_the_analysis(report: &Value) -> (String, Vec<String>) {
    (report["examples"][0]["observed"].as_str().unwrap_or_default().to_string(), analysis_codes(report))
}

/// As `c_codes`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn c_codes_of_the_analysis(text: &str) -> Vec<String> {
    analysis_codes(&Fixture::new(&[("a.trion", text)]).trion(&["verify", "--json", "a.trion"]).json())
}

/// As `d_codes`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn d_codes_of_the_analysis(text: &str) -> Vec<String> {
    analysis_codes(&d_check(text))
}

/// As `e_check`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn e_check_of_the_analysis(files: &[(&str, &str)]) -> Vec<String> {
    let mut all = vec![("trion.toml", MANIFEST)];
    all.extend_from_slice(files);
    analysis_codes(&Fixture::new(&all).trion(&["verify", "--json"]).json())
}

/// The guarantees of the model, keyed by the identifier of their statement.
fn e_formulas(f: &Fixture) -> Vec<(String, Value)> {
    let model = f.inspect(&["model", "--json"]).json();
    model["constraints"].as_array().unwrap().iter().map(|c| (c["refs"][0]["id"].as_str().unwrap().to_string(), c["guarantee"].clone())).collect()
}

const E_TEXT: &str = "The API shall not stop. The API shall log each call.";

fn e_source(quotes: &[(&str, &str)]) -> String {
    source_block("R", "requirement", "r.txt", E_TEXT, "", quotes)
}

const E_QUOTES: [(&str, &str); 2] = [("ONE", "The API shall not stop."), ("TWO", "The API shall log each call.")];

fn e_sourced(spec: &str) -> Fixture {
    Fixture::new(&[("trion.toml", MANIFEST), ("r.txt", E_TEXT), ("s.trion", &e_source(&E_QUOTES)), ("a.trion", spec)])
}

// Citations.

#[test]
fn source_and_quote_names_are_unique_where_they_are_declared() {
    let one = "source R:\n    title \"One\"\n    locator \"https://example.com/1\"\n    quote X \"x\"\n";
    let other = "source S:\n    title \"Two\"\n    locator \"https://example.com/2\"\n    quote X \"x\"\n";
    assert!(e_check(&[("a.trion", &format!("{one}{other}"))]).is_empty(), "one quote name in two sources");
    assert_eq!(e_check(&[("a.trion", &format!("{one}{}", other.replace("source S", "source R")))]), ["DUPLICATE_ID"]);
    let twice = "source R:\n    title \"One\"\n    locator \"https://example.com/1\"\n    quote X \"x\"\n    quote X \"y\"\n";
    assert_eq!(e_check(&[("a.trion", twice)]), ["DUPLICATE_ID"]);
}

#[test]
fn a_quote_is_cited_through_its_own_source() {
    let sources = "source R:\n    title \"R\"\n    locator \"https://example.com/r\"\n    quote ONE \"Stop.\"\nsource S:\n    title \"S\"\n    locator \"https://example.com/s\"\n";
    assert!(e_check_of_the_analysis(&[("a.trion", &format!("{sources}[A] The API shall stop.\n    cite R#ONE\n"))]).is_empty());
    assert_eq!(e_check_of_the_analysis(&[("a.trion", &format!("{sources}[A] The API shall stop.\n    cite S#ONE\n"))]), ["UNRESOLVED_CITATION"]);
}

#[test]
fn a_summary_is_a_note_and_a_quote_is_literal() {
    let literal = e_sourced("[A] The API shall stop.\n    cite R#ONE\n[B] The API shall log each call.\n    cite R#TWO\n");
    assert!(analysis_codes(&literal.trion(&["verify", "--json"]).json()["sources"].clone()).is_empty());
    let summary = [("ONE", "The API never stops."), ("TWO", "The API shall log each call.")];
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("r.txt", E_TEXT), ("s.trion", &e_source(&summary)), ("a.trion", "[A] The API shall stop.\n    cite R#ONE\n[B] The API shall log each call.\n    cite R#TWO\n")]);
    assert!(analysis_codes(&f.trion(&["verify", "--json"]).json()["sources"].clone()).contains(&"source-quote-not-found".to_string()), "a summary is not a quotation");
    let noted = e_sourced("note \"In short, the API never stops.\"\n[A] The API shall stop.\n    cite R#ONE\n[B] The API shall log each call.\n    cite R#TWO\n");
    assert!(analysis_codes(&noted.trion(&["verify", "--json"]).json()["sources"].clone()).is_empty());
    assert!(analysis_codes(&noted.trion(&["verify", "--json"]).json()).is_empty());
}

#[test]
fn a_citation_informs_a_statement_without_entailing_or_importing_anything() {
    // The quote says the opposite of the statement that cites it.
    let cited = e_sourced("[A] The API shall stop.\n    cite R#ONE\n[B] The API shall log each call.\n    cite R#TWO\n");
    assert!(analysis_codes(&cited.trion(&["verify", "--json"]).json()).is_empty(), "the quoted text is no premise");
    let coverage = cited.trion(&["verify", "--json"]).json()["sources"].clone();
    assert_eq!(coverage["sources"][0]["percent"], 100.0, "the citation is recorded: {coverage}");
    // Without the citation the statement means the same.
    let bare = e_sourced("[A] The API shall stop.\n[B] The API shall log each call.\n    cite R#TWO\n");
    assert_eq!(e_formulas(&bare), e_formulas(&cited));
    assert_eq!(e_formulas(&bare).len(), 2, "the quotes add no constraint");
    // Adopting the quoted rule takes a statement of its own, with its citation.
    let adopted = e_sourced("[A] The API shall stop.\n    cite R#ONE\n[B] The API shall log each call.\n    cite R#TWO\n[C] The API shall not stop.\n    cite R#ONE\n");
    assert_eq!(analysis_codes(&adopted.trion(&["verify", "--json"]).json()), ["contradiction"]);
}

#[test]
fn a_citation_does_not_follow_a_reference_or_enter_an_example() {
    let spec = "section \"Stopping\":\n    cite R#ONE\n    cite R#TWO\n    [A] The API shall stop.\n    ref [B]\n    example E:\n        kind syntax\n        form fragment\n        input \"[X] The bell shall ring.\"\n        expect accepted\n[B] The API shall start.\n";
    let f = e_sourced(spec);
    let report = f.trion(&["verify", "--json"]).json()["sources"].clone();
    assert_eq!(report_codes(&report), ["unsourced"], "{report}");
    assert_eq!(report["diagnostics"][0]["refs"][0]["id"], "B");
    let text = report.to_string();
    assert!(!text.contains("The bell shall ring"), "the example input is not a cited statement: {text}");
}

// Notes and examples.

#[test]
fn a_note_explains_without_constraining() {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "note \"The API shall not stop.\"\n[A] The API shall stop.\n")]);
    assert!(analysis_codes(&f.trion(&["verify", "--json"]).json()).is_empty());
    assert_eq!(e_formulas(&f).len(), 1);
}

#[test]
fn an_example_changes_no_outer_name_source_identity_or_include() {
    let spec = r#"source R:
    title "Outer"
    locator "https://example.com/r"
[A] The API shall stop.
example E:
    kind syntax
    form fragment
    input """
package q edition "x"
include "missing.trion"
namespace q:
    source R:
        title "Inner"
        locator "https://example.com/inner"
    [A] A room means a place.
    [B] The room shall open.
"""
    expect accepted
"#;
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", spec)]);
    let report = f.trion(&["verify", "--json"]).json();
    assert!(analysis_codes(&report).is_empty(), "no duplicate identifier or source, no missing include: {report}");
    assert_eq!(report["examples"][0]["observed"], "accepted");
    let broken = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &spec.replace("shall open", "shall shall open"))]);
    let observed = broken.trion(&["verify", "--json"]).json()["examples"][0]["observed"].clone();
    assert!(observed.as_str().unwrap().starts_with("rejected"), "the input is parsed: {observed}");
    let glossary = f.inspect(&["glossary"]).stdout;
    assert!(!glossary.contains("room"), "{glossary}");
    assert_eq!(e_formulas(&f).iter().map(|(id, _)| id.as_str()).collect::<Vec<_>>(), ["A"]);
}

#[test]
fn a_namespace_name_is_lowercase_components() {
    assert!(c_codes_of_the_analysis("namespace main.sub-part2:\n    [A] The API shall stop.\n").is_empty());
    for bad in ["Main.sub", "main.Sub", "main.sub_x", "main..sub", "main.2sub"] {
        assert!(!c_codes_of_the_analysis(&format!("namespace {bad}:\n    [A] The API shall stop.\n")).is_empty(), "{bad}");
    }
}

#[test]
fn a_source_has_one_quoted_title_and_one_quoted_locator() {
    let ok = "source DOC:\n    title \"The document\"\n    locator \"https://example.com/doc\"\n";
    assert!(c_codes(ok).is_empty());
    assert_eq!(c_codes("source DOC:\n    title \"The document\"\n"), ["parse-source"], "no locator");
    assert_eq!(c_codes("source DOC:\n    locator \"https://example.com/doc\"\n"), ["parse-source"], "no title");
    assert_eq!(c_codes("source DOC:\n    title \"a\"\n    title \"b\"\n    locator \"l\"\n"), ["parse-source"], "two titles");
    // An unquoted value is reported, not dropped in silence.
    assert_eq!(c_codes("source DOC:\n    title The document\n    locator \"l\"\n"), ["parse-source", "parse-source"]);
}

#[test]
fn include_order_is_the_reading_order() {
    let entry = "package p edition \"1\"\n\ninclude \"z.trion\"\ninclude \"a.trion\"\n";
    let f = Fixture::new(&[
        ("trion.toml", MANIFEST),
        ("trion.trion", entry),
        ("z.trion", "namespace p:\n    [ZED] The API shall stop.\n"),
        ("a.trion", "namespace p:\n    [ALPHA] The API shall start.\n"),
    ]);
    let out = f.inspect(&["expand"]).stdout;
    let (zed, alpha) = (out.find("[ZED]").unwrap(), out.find("[ALPHA]").unwrap());
    assert!(zed < alpha, "{out}");
    // The order does not select different constraints.
    assert!(analysis_codes(&f.trion(&["verify", "--json"]).json()).is_empty());
}
