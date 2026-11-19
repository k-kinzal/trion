//! Diagrams as another notation for controlled English: the source map of an
//! expansion, generated views, declared diagram kinds and choice flows.

mod common;
use common::*;
use serde_json::Value;

const MANIFEST: &str = "[package]\nname = \"p\"\n";

const CHOICE: &str = "[F] When a request arrives, the API shall follow this flow:\n    step inspect: inspect the request;\n    [F/keep] step accept: store the request;\n    step reject: discard the request;\n    step answer: send a reply;\n    start inspect\n    choose after inspect:\n        when the request is valid -> accept\n        otherwise -> reject\n    accept -> answer\n    reject -> answer\n    finish answer\n";

fn package(text: &str) -> Fixture {
    Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", text)])
}

fn codes(text: &str) -> Vec<String> {
    report_codes(&package(text).verify(&["--json"]).json())
}

/// As `codes`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn codes_of_the_analysis(text: &str) -> Vec<String> {
    analysis_codes(&package(text).verify(&["--json"]).json())
}

/// The expressions that `expand --json` gives for one statement.
fn expressions(f: &Fixture, id: &str) -> Vec<Value> {
    let items = f.inspect(&["expand", "--json"]).json();
    let item = items.as_array().unwrap().iter().find(|i| i["id"] == id).unwrap_or_else(|| panic!("no {id} in {items}")).clone();
    item["expressions"].as_array().unwrap().clone()
}

fn origins(expression: &Value) -> Vec<(String, String, u64)> {
    expression["origins"].as_array().unwrap().iter().map(|o| (o["kind"].as_str().unwrap().to_string(), o["name"].as_str().unwrap().to_string(), o["line"].as_u64().unwrap())).collect()
}

/// The assumption and the guarantee of each statement, by identifier.
fn contracts(f: &Fixture) -> Vec<(String, String, String)> {
    let model = f.inspect(&["model", "--json"]).json();
    model["constraints"].as_array().unwrap().iter().map(|c| (c["refs"][0]["id"].as_str().unwrap().to_string(), c["assume"].to_string(), c["guarantee"].to_string())).collect()
}

#[test]
fn each_generated_expression_names_the_elements_and_scopes_it_came_from() {
    // The fixture adds the namespace header, so the flow head is on line 2.
    let f = package(CHOICE);
    let found = expressions(&f, "F");
    assert_eq!(found.len(), 5, "{found:?}");
    let entry = |kind: &str, name: &str, line: u64| (kind.to_string(), name.to_string(), line);
    // The first step: the head, the start mark and the step.
    assert_eq!(origins(&found[0]), [entry("head", "F", 2), entry("start", "inspect", 7), entry("step", "inspect", 3)]);
    // A guarded step names its guard; the identifier of the step is kept.
    assert_eq!(origins(&found[1]), [entry("head", "F", 2), entry("guard", "inspect -> accept", 9), entry("step", "accept", 4)]);
    assert_eq!(found[1]["origins"][2]["id"], "F/keep");
    assert_eq!(found[1]["origins"][1]["text"], "when the request is valid -> accept");
    // A step after a guarded step names its edge, the guard of its path, and the finish mark.
    assert_eq!(origins(&found[2]), [entry("head", "F", 2), entry("edge", "accept -> answer", 11), entry("guard", "inspect -> accept", 9), entry("step", "answer", 6), entry("finish", "answer", 13)]);
    // The otherwise arm names itself and the guard that it denies.
    assert_eq!(origins(&found[3])[1..3], [entry("otherwise", "inspect -> reject", 10), entry("guard", "inspect -> accept", 9)]);

    // A concept edge names its nodes, its label and itself; the enclosing scope is kept.
    let f = package("While the shop is open:\n    [C] concept:\n        [C/owner] each order -> has -> exactly one buyer;\n");
    let edge = &expressions(&f, "C/owner")[0];
    assert_eq!(edge["text"], "While the shop is open, each order has exactly one buyer.");
    assert_eq!(origins(edge), [entry("node", "order", 4), entry("label", "has", 4), entry("node", "exactly one buyer", 4), entry("edge", "order -> exactly one buyer", 4)]);
    assert_eq!(edge["origins"][3]["id"], "C/owner");
    assert_eq!(edge["scopes"], serde_json::json!(["While the shop is open"]));

    // An authored sentence is its own origin.
    let f = package("[A] The API shall stop.\n");
    assert_eq!(origins(&expressions(&f, "A")[0]), [entry("statement", "A", 2)]);
}

#[test]
fn a_flow_with_choices_expands_to_sentences_that_the_parser_reads() {
    let f = package(CHOICE);
    let expansion = f.inspect(&["expand"]).stdout;
    let expected = [
        "When a request arrives, the API shall inspect the request.",
        "While the request is valid, when a request arrives, the API shall store the request after the API inspects the request.",
        "While the request is valid, when a request arrives, the API shall send a reply after the API stores the request.",
        "While the request is not valid, when a request arrives, the API shall discard the request after the API inspects the request.",
        "While the request is not valid, when a request arrives, the API shall send a reply after the API discards the request.",
    ];
    assert!(expansion.contains(&format!("[F]\n{}\n", expected.join("\n"))), "{expansion}");
    // The expansion is controlled English: written as statements, it passes the check.
    assert!(codes_of_the_analysis(&format!("{}\n", expected.join("\n"))).is_empty());
    // A verbal guard is denied with `does not`, and a step keeps its exception.
    let verbal = CHOICE.replace("when the request is valid -> accept", "when the request passes the filter -> accept").replace("discard the request;", "discard the request, unless the request is a retry;");
    let expansion = package(&verbal).inspect(&["expand"]).stdout;
    assert!(expansion.contains("While the request does not pass the filter, when a request arrives, the API shall discard the request after the API inspects the request, unless the request is a retry."), "{expansion}");
    // A flow without choices still reads as one ordered list.
    let linear = "[L] When a request arrives, the API shall follow this flow:\n    step a: validate the request;\n    step b: store the request;\n    start a\n    a -> b\n    finish b\n";
    assert!(package(linear).inspect(&["expand"]).stdout.contains("perform the following actions in order:\n    validate the request;\n    store the request;"));
}

#[test]
fn a_generated_view_says_what_its_statements_say() {
    let text = "[PKG] Each package has exactly one entry file.\nEach namespace contains zero or more declarations.\n[RULE] The API shall stop.\n[SEQ]\nWhen the checker completes an analysis A,\nthe checker shall perform the following actions in order:\n    create an analysis report R for A;\n    retain R;\n";
    let f = package(text);
    let concept = f.inspect(&["diagram", "concept"]).stdout;
    assert_eq!(concept, "concept:\n    [PKG] each package -> has -> exactly 1 entry file;\n    each namespace -> contains -> zero or more declarations;\n");
    let flow = f.inspect(&["diagram", "flow", "SEQ"]).stdout;
    assert!(flow.starts_with("[SEQ] When the checker completes an analysis, the checker shall follow this flow:\n    step s1: create an analysis report R for the analysis;\n"), "{flow}");
    // The views are diagrams of the language: read back, they give the contracts of the statements.
    let view = package(&format!("{flow}{concept}"));
    assert!(analysis_codes(&view.verify(&["--json"]).json()).is_empty());
    let original = contracts(&f);
    let generated = contracts(&view);
    for id in ["PKG", "SEQ"] {
        let of = |all: &[(String, String, String)]| all.iter().find(|(found, _, _)| found == id).cloned().unwrap();
        assert_eq!(of(&generated), of(&original), "{id}");
    }
    let expansion = |f: &Fixture| f.inspect(&["expand", "--json"]).json().as_array().unwrap().iter().filter(|i| i["id"] == "PKG" || i["id"] == "SEQ").map(|i| format!("{} {}", i["id"], i["expansion"])).collect::<std::collections::BTreeSet<_>>();
    assert_eq!(expansion(&view), expansion(&f));
    // A statement that the notation cannot restate gets no view, instead of an approximate one.
    let refused = f.inspect(&["diagram", "concept", "RULE"]);
    assert_eq!(refused.code, 2, "{}{}", refused.stdout, refused.stderr);
    assert!(refused.stderr.contains("no concept edge restates it"), "{}", refused.stderr);
    assert_eq!(f.inspect(&["diagram", "flow", "PKG"]).code, 2);
}

const KIND: &str = "diagram kind transition:\n    element \"$from -> $event -> $to;\"\n    types \"$from: value, $event: value, $to: value\"\n    expansion \"While the door is $from, when the bell is $event, the light shall be $to.\"\n    preserves \"Each element means exactly its expansion sentence.\"\n";

#[test]
fn a_declared_diagram_kind_is_normative_and_an_undeclared_one_is_not() {
    let diagram = "[T] diagram transition:\n    [T/pay] closed -> rung -> red;\n    open -> rung -> green;\n";
    let f = package(&format!("{KIND}{diagram}"));
    assert!(report_codes(&f.verify(&["--json"]).json()).is_empty());
    // Each element is the sentence of its expansion, formalized like authored English.
    let authored = package("[T/pay] While the door is closed, when the bell is rung, the light shall be red.\n");
    assert_eq!(contracts(&f)[0], contracts(&authored)[0]);
    let element = &expressions(&f, "T/pay")[0];
    assert_eq!(element["text"], "While the door is closed, when the bell is rung, the light shall be red.");
    assert_eq!(element["origins"][3]["text"], "closed -> rung -> red;");
    assert_eq!(expressions(&f, "T/2")[0]["text"], "While the door is open, when the bell is rung, the light shall be green.");
    // So an element can contradict a sentence.
    assert_eq!(codes(&format!("{KIND}{diagram}[X] While the door is closed, when the bell is rung, the light shall not be red.\n")), ["contradiction"]);
    // The typing rules hold: a part declared as an action is not used as a value.
    let mistyped = KIND.replace("$event: value", "$event: action");
    assert!(codes(&format!("{mistyped}{diagram}")).contains(&"vocabulary-kind-conflict".to_string()));
    // An element follows the element grammar of its kind.
    assert_eq!(codes(&format!("{KIND}[T] diagram transition:\n    closed to red;\n")), ["parse-diagram"]);
    // Without all four parts the kind is not declared, and its diagram stays unsupported.
    for missing in ["    element", "    types", "    expansion", "    preserves"] {
        let partial: String = KIND.lines().filter(|l| !l.starts_with(missing)).map(|l| format!("{l}\n")).collect();
        assert_eq!(codes(&format!("{partial}{diagram}")), ["parse-diagram-kind", "UNSUPPORTED_DIAGRAM_KIND"], "{missing}");
    }
    // A kind is declared before it is used.
    assert_eq!(codes(&format!("{diagram}{KIND}")), ["UNSUPPORTED_DIAGRAM_KIND"]);
    assert_eq!(codes("[G] diagram gantt:\n    a -> b;\n"), ["UNSUPPORTED_DIAGRAM_KIND"]);
}

#[test]
fn a_declared_diagram_round_trips_with_its_inherited_configuration() {
    let terms = "primitive audit, enabled, door, bell, light, closed, rung, red\n";
    let f = package(&format!(
        "{terms}{KIND}Where the audit is enabled:\n    [T] diagram transition:\n        [T/pay] closed -> rung -> red;\n"
    ));
    let expression = &expressions(&f, "T/pay")[0];
    let sentence = expression["text"].as_str().unwrap();
    assert!(sentence.starts_with("Where the audit is enabled,"), "{sentence}");
    let authored = package(&format!("{terms}[T/pay] {sentence}\n"));
    assert_eq!(contracts(&f), contracts(&authored));
    let conversion = f.convert(&["--properties", "--json"]);
    assert_eq!(conversion.code, 0, "{}{}", conversion.stdout, conversion.stderr);
}

#[test]
fn a_target_cardinality_leaves_the_inverse_relation_free() {
    let exists = "[O] There is an order.\n[B] There is a buyer.\n";
    // One buyer for each order says nothing of the orders of a buyer.
    let both = format!("{exists}[C] concept:\n    each order -> has -> exactly one buyer;\n    each buyer -> has -> at least two orders;\n");
    assert!(codes(&both).is_empty(), "{:?}", codes(&both));
    // The same direction is constrained: two cardinalities of one relation
    // conflict. A concept describes no actor of a system: its edges are
    // assumptions, and together they allow no environment.
    let same = format!("{exists}[C] concept:\n    each order -> has -> exactly one buyer;\n    each order -> has -> at least two buyers;\n");
    assert_eq!(codes(&same), ["incompatible"]);
}

#[test]
fn the_rendered_document_draws_views_of_sentences() {
    let text = "[PKG] Each package has exactly one entry file.\n[SEQ]\nWhen the checker completes an analysis A,\nthe checker shall perform the following actions in order:\n    create an analysis report R for A;\n    retain R;\n";
    let terms = "primitive package\nprimitive entry file\nprimitive checker\nprimitive analysis\nprimitive analysis report\n";
    let html = package(&format!("{terms}{text}")).document(&[]).stdout;
    assert!(html.contains("<section id=\"views\"><h2>Generated diagram views</h2>"), "no views section");
    assert!(html.contains("each package -&gt; has -&gt; exactly 1 entry file;"), "the notation of the concept view");
    assert!(html.contains("Generated flow view: it restates the list above"), "the flow view of the ordered list");
    assert_eq!(html.matches("<svg").count(), 2);
    // A package without such statements has no views section.
    assert!(!package("[A] The API shall stop.\n").document(&[]).stdout.contains("id=\"views\""));
}

#[test]
fn a_compatibility_claim_names_a_revision_and_its_sentence_forms() {
    let source = |revision: &str| format!("source ORACLE:\n    title \"The base grammar\"\n    kind citation\n    locator \"https://example.test/grammar\"\n    revision \"{revision}\"\n");
    let claim = "compatibility BASE-SENTENCES:\n    source ORACLE\n    revision \"abc123\"\n    form Definition\n    form Event-driven\n[A] The API shall stop.\n    unsourced \"A fixture.\"\n";
    let check = |text: &str| {
        let f = package(text);
        let mut found = analysis_codes(&f.verify(&["--json"]).json());
        found.extend(analysis_codes(&f.verify(&["--json"]).json()["sources"].clone()).into_iter().filter(|c| c.starts_with("compatibility")));
        found
    };
    assert!(check(&format!("{}{claim}", source("abc123"))).is_empty());
    // The claim is about the revision that the source is at.
    assert_eq!(check(&format!("{}{claim}", source("def456"))), ["compatibility-revision"]);
    assert_eq!(check(&format!("{}{}", source("abc123"), claim.replace("source ORACLE", "source OTHER"))), ["compatibility-source-unknown"]);
    // A claim without a revision or without a form identifies nothing.
    assert_eq!(check(&format!("{}{}", source("abc123"), claim.replace("    revision \"abc123\"\n", ""))), ["parse-compatibility"]);
    assert_eq!(check(&format!("{}{}", source("abc123"), claim.replace("    form Definition\n    form Event-driven\n", ""))), ["parse-compatibility"]);
    // The forms are the sentence forms of the language.
    assert_eq!(check(&format!("{}{}", source("abc123"), claim.replace("form Definition", "form Haiku"))), ["parse-compatibility"]);
}

#[test]
fn what_a_package_declares_and_nothing_checks_is_named_in_the_result() {
    // The reason why a diagram kind keeps the meaning of its elements, and
    // the agreement of sentence forms with another grammar, are stated by
    // the package. Old behaviour: both had to be present, were never read
    // again, and a verified result said nothing of them. A result now
    // names each as declared and not checked, in every view.
    let diagram = "[T] diagram transition:\n    [T/pay] closed -> rung -> red;\n    open -> rung -> green;\n";
    let source = "source ORACLE:\n    title \"The base grammar\"\n    kind citation\n    locator \"https://example.test/grammar\"\n    revision \"abc123\"\n";
    let claim = "compatibility BASE-SENTENCES:\n    source ORACLE\n    revision \"abc123\"\n    form Definition\n    form Event-driven\n";
    let f = package(&format!("{source}{claim}{KIND}{diagram}"));
    let report = f.verify(&["--json"]).json();
    let declared: Vec<&str> = report["declared"].as_array().unwrap_or_else(|| panic!("the report names nothing as declared: {report}")).iter().map(|d| d.as_str().unwrap()).collect();
    assert_eq!(declared.len(), 2, "{declared:?}");
    assert!(declared[0].starts_with("diagram kind transition: ") && declared[0].contains("is not checked"), "{declared:?}");
    assert!(declared[1].starts_with("compatibility BASE-SENTENCES: ") && declared[1].contains("Definition, Event-driven") && declared[1].contains("is not checked"), "{declared:?}");
    let text = f.verify(&[]).stdout;
    assert_eq!(text.lines().filter(|line| line.starts_with("declared, not checked: ")).count(), 2, "{text}");
    let html = f.document(&[]).stdout;
    assert_eq!(html.matches("<li>declared, not checked: ").count(), 2, "no status line in the document");
    // A package that declares neither has no such line.
    let plain = package("[A] The API shall stop.\n").verify(&["--json"]).json();
    assert!(plain["declared"].as_array().unwrap().is_empty());
}
