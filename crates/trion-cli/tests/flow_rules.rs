//! The flows that the specification states for the loader, the processor,
//! the checker, the source check and the verification linkage: each step of
//! a flow is observed, in its order, on a package that needs it. And the
//! rules about coordinated descriptions, the composition tree and diagrams.

mod common;
use common::*;
use serde_json::Value;

fn codes(f: &Fixture) -> Vec<String> {
    report_codes(&f.trion(&["verify", "--json"]).json())
}

/// As `codes`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn codes_of_the_analysis(f: &Fixture) -> Vec<String> {
    analysis_codes(&f.trion(&["verify", "--json"]).json())
}

fn unread(f: &Fixture) -> Vec<String> {
    let report = f.trion(&["verify", "--json"]).json();
    ["opaque", "ungrounded"].iter().flat_map(|list| report[list].as_array().cloned().unwrap_or_default()).map(|d| d["code"].as_str().unwrap().to_string()).collect()
}

fn grpc_manifest() -> String {
    format!("[package]\nname = \"p\"\n\n[dependencies]\ngrpc = {{ path = \"{}\" }}\n", repo_root().join("stdlib/grpc").display())
}

#[test]
fn the_loader_reads_the_entry_then_its_includes_then_the_used_dependencies() {
    let entry = "package p edition \"1\"\ninclude \"spec/a.trion\"\n";
    let a = "include \"deeper/b.trion\"\nnamespace p:\n    primitive API\n    [A] The API shall stop.\n";
    let b = "namespace p:\n    [B] The API shall not stop.\n";
    // Step entry: without the entry file nothing is loaded.
    let none = Fixture::raw(&[("trion.toml", MANIFEST), ("spec/a.trion", a)]);
    let r = none.trion(&["verify"]);
    assert!(r.code != 0 && r.stdout.contains("MISSING_SOURCE") && r.stdout.contains("checked 0 specifications"), "{}", r.stdout);
    // Step includes: a file is read because the entry, or a file that the entry includes, includes it.
    let f = Fixture::raw(&[("trion.toml", MANIFEST), ("trion.trion", entry), ("spec/a.trion", a), ("spec/deeper/b.trion", b), ("spec/unused.trion", "namespace p:\n    [C] The API shall run.\n")]);
    let r = f.trion(&["verify"]);
    assert!(r.stdout.contains("checked 2 specifications"), "{}", r.stdout);
    assert_eq!(codes_of_the_analysis(&f), ["contradiction"]);
    // Step dependencies: a dependency is loaded when a file uses it, after the files of the package.
    let used = Fixture::new(&[("trion.toml", &grpc_manifest()), ("a.trion", "use grpc\nbind API as grpc.service.\nThe API shall use gRPC communication.\nThe API GET /foo shall return foo.\n")]);
    assert_eq!(codes_of_the_analysis(&used), ["shape-violation"], "the rule of the dependency is applied");
    let unused = Fixture::new(&[("trion.toml", &grpc_manifest()), ("a.trion", "primitive API\nprimitive foo\nThe API GET /foo shall return foo.\n")]);
    assert!(!codes_of_the_analysis(&unused).contains(&"shape-violation".to_string()), "a dependency that no file uses states nothing here");
    // A missing include stops the loader before any dependency is read.
    let missing = Fixture::raw(&[("trion.toml", &grpc_manifest()), ("trion.trion", "package p edition \"1\"\ninclude \"gone.trion\"\n")]);
    let r = missing.trion(&["verify"]);
    assert!(r.code != 0 && r.stdout.contains("the included file gone.trion cannot be read") && r.stdout.contains("checked 0 specifications"), "{}", r.stdout);
}

#[test]
fn the_processor_parses_resolves_formalizes_checks_and_reports_in_that_order() {
    let conflict = "[A] The API shall stop.\n[B] The API shall not stop.\n";
    // Step parse comes before step check: what the parser reports stands before what the checker reports,
    // and a sentence that is not parsed is no part of the model.
    let unparsed = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &format!("primitive API\n{conflict}[C] The API shall shall stop.\n"))]);
    assert_eq!(codes(&unparsed), ["parse-sentence", "contradiction"]);
    assert!(!unparsed.inspect(&["model"]).stdout.lines().any(|line| line == "C"));
    // Step resolve: a term that nothing declares or relates is reported for its statement.
    let unresolved = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "[E] The gadget shall frobnicate the widget.\n")]);
    assert_eq!(unread(&unresolved), ["ungrounded"]);
    // Steps formalize, check and report: the model of the parsed and resolved package is checked.
    let checked = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &format!("primitive API\n{conflict}"))]);
    assert_eq!(codes(&checked), ["contradiction"]);
    let model = checked.inspect(&["model"]).stdout;
    assert!(model.contains("Act(API|stop)") && model.contains("Forbid(API|stop)"), "{model}");
    // Step report: every diagnostic of the package is in the one report, with its statements.
    let report = checked.trion(&["verify", "--json"]).json();
    let named: Vec<&str> = report["diagnostics"][0]["refs"].as_array().unwrap_or_else(|| panic!("{}", report["diagnostics"][0])).iter().map(|s| s["id"].as_str().unwrap()).collect();
    assert_eq!(named, ["A", "B"]);
}

#[test]
fn the_checker_reports_contradictions_then_form_violations_then_missing_cases() {
    let text = "use grpc\nbind API as grpc.service.\nprimitive gate\n[U] The API shall use gRPC communication.\n[G] The API GET /foo shall return foo.\n[A] The gate shall stop.\n[B] The gate shall not stop.\n[D] The status is Open or Closed.\n[L] When the status is Open, the gate shall wait.\n";
    let f = Fixture::new(&[("trion.toml", &grpc_manifest()), ("a.trion", text)]);
    let report = f.trion(&["verify", "--json"]).json();
    let found = report_codes(&report);
    // Steps compose and solve give the status; the three reports follow in the order of the flow.
    let position = |code: &str| found.iter().position(|c| c == code).unwrap_or_else(|| panic!("{code} is missing from {found:?}"));
    assert!(position("contradiction") < position("shape-violation"), "{found:?}");
    assert!(position("shape-violation") < position("missing-case"), "{found:?}");
    assert_eq!(report["consistency"]["status"], "unsatisfiable", "{}", report["consistency"]);
}

const SOURCE: &str = "要求その一です。要求その二です。";

fn sourced(quotes: &[(&str, &str)], spec: &str) -> Fixture {
    let block = source_block("R", "requirement", "source.txt", SOURCE, "", quotes);
    Fixture::new(&[("trion.toml", MANIFEST), ("source.txt", SOURCE), ("sources.trion", &block), ("a.trion", spec)])
}

#[test]
fn the_source_check_compares_copies_finds_quotes_classifies_statements_and_measures_coverage() {
    let quotes = [("ONE", "要求その一です。"), ("TWO", "要求その二です。")];
    let spec = "primitive API\n[A] The API shall stop.\n  cite R#ONE\n[B] The API shall start.\n  unsourced \"A reason.\"\n";
    let check = |f: &Fixture| f.trion(&["verify", "--json"]).json()["sources"].clone();
    // Step copies: a local copy that differs from its digest is reported.
    let changed = sourced(&quotes, spec);
    changed.write("source.txt", "要求その一です。要求その二です。追加。");
    assert!(report_codes(&check(&changed)).contains(&"source-changed".to_string()));
    // Step quotes: a quote that is not in its local copy is reported.
    let misquoted = sourced(&[("ONE", "要求その壱です。"), ("TWO", "要求その二です。")], spec);
    assert!(report_codes(&check(&misquoted)).contains(&"source-quote-not-found".to_string()));
    // Step statements: each statement without a citation is reported, with its reason where it states one.
    let f = sourced(&quotes, spec);
    let report = check(&f);
    let unsourced: Vec<&str> = report["unsourced"].as_array().unwrap().iter().filter_map(|u| u["id"].as_str()).collect();
    assert_eq!(unsourced, ["B"], "{report}");
    let neither = sourced(&quotes, "primitive API\n[A] The API shall stop.\n  cite R#ONE\n[C] The API shall run.\n");
    assert!(report_codes(&check(&neither)).contains(&"unsourced".to_string()), "{:?}", report_codes(&check(&neither)));
    // Step coverage: the share of the copy that cited quotes cover is measured last.
    let coverage = f.trion(&["verify", "--json"]).json()["sources"].clone();
    assert_eq!(coverage["sources"][0]["percent"], 50.0, "{coverage}");
}

#[test]
fn a_coordinated_description_predicate_takes_the_subject_of_the_predicate_before_it() {
    let model = |text: &str| Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", text)]).inspect(&["model"]).stdout;
    // The second predicate has no subject of its own: it is asserted of the room.
    let both = model("primitive room\nprimitive message\n[D] The room is archived and accepts no messages.\n");
    assert!(both.contains("Dom(room, archived)") && both.contains("Dom(room, accept no message)"), "{both}");
    // Each predicate constrains the subject: denying either one contradicts.
    let denied = |second: &str| codes(&Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &format!("primitive room\n[D] The room is archived and locked.\n{second}\n"))]));
    assert_eq!(denied("[N] The room is not locked."), ["contradiction"]);
    assert_eq!(denied("[N] The room is not archived."), ["contradiction"]);
    // A predicate of another subject is not coordinated with it.
    assert!(denied("[N] The door is not locked.").is_empty());
}

#[test]
fn the_model_keeps_composition_operators_and_binders() {
    let text = "primitive report\nprimitive analyst\nprimitive operator\nprimitive request\n[O] The analyst shall perform all of the following actions:\n    create a report;\n    send the report;\n[X] The operator shall perform exactly one of the following actions:\n    create a report;\n    send the report;\n[B] When the analyst receives a request Q, the analyst shall create a report R for Q and shall retain R.\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", text)]);
    let model = f.inspect(&["model", "--json"]).json();
    let of = |id: &str| model["constraints"].as_array().unwrap().iter().find(|c| c["kind"] == "Spec" && c["refs"][0]["id"] == id).unwrap_or_else(|| panic!("{id}"))["guarantee"].clone();
    fn atoms(formula: &Value, out: &mut Vec<String>) {
        match formula {
            Value::Object(map) => {
                if let Some(key) = map.get("key").and_then(Value::as_str) {
                    out.push(key.to_string());
                }
                map.values().for_each(|v| atoms(v, out));
            }
            Value::Array(items) => items.iter().for_each(|v| atoms(v, out)),
            _ => {}
        }
    }
    // `all of` is a conjunction of its two items, not one flattened action.
    let all = of("O");
    assert_eq!(all["And"].as_array().map(Vec::len), Some(2), "{all}");
    // `exactly one of` is a disjunction whose branches exclude each other.
    let one = of("X");
    let branches = one["Or"].as_array().unwrap_or_else(|| panic!("{one}"));
    assert_eq!(branches.len(), 2);
    assert!(branches.iter().all(|b| b.to_string().contains("\"Not\"")), "{one}");
    // The binder R is one name in both items of its statement, and it is local to the statement.
    let mut keys = Vec::new();
    atoms(&of("B"), &mut keys);
    assert!(keys.iter().any(|k| k.contains("create #R@B/1 report")) && keys.iter().any(|k| k.contains("retain #R@B/1 report")), "{keys:?}");
    let mut others = Vec::new();
    atoms(&all, &mut others);
    atoms(&one, &mut others);
    assert!(others.iter().all(|k| !k.contains("#R@")), "{others:?}");
    // The expansion keeps the composition as the author wrote it.
    let expanded = f.inspect(&["expand"]).stdout;
    assert!(expanded.contains("all of the following actions") && expanded.contains("exactly one of the following actions"), "{expanded}");
}

const KIND: &str = "primitive door\nprimitive bell\nprimitive light\ndiagram kind transition:\n    element \"$from -> $event -> $to;\"\n    types \"$from: value, $event: value, $to: value\"\n    expansion \"While the door is $from, when the bell is $event, the light shall be $to.\"\n    preserves \"Each element means exactly its expansion sentence.\"\n";

#[test]
fn a_diagram_is_a_typed_notation_for_sentences_with_one_interpretation() {
    let contracts = |text: &str| -> Vec<(String, String)> {
        let model = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", text)]).inspect(&["model", "--json"]).json();
        model["constraints"].as_array().unwrap().iter().filter(|c| c["kind"] == "Spec").map(|c| (c["assume"].to_string(), c["guarantee"].to_string())).collect()
    };
    // An alternate notation: the diagram has the contract of the sentence that it stands for.
    let drawn = contracts(&format!("{KIND}[T] diagram transition:\n    closed -> rung -> red;\n"));
    let written = contracts(&format!("{KIND}[T] While the door is closed, when the bell is rung, the light shall be red.\n"));
    assert!(!drawn.is_empty());
    assert_eq!(drawn, written);
    // Typed: an element that does not have the form of its kind is no diagram of that kind.
    assert_eq!(codes(&Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &format!("{KIND}[T] diagram transition:\n    closed to red;\n"))])), ["parse-diagram"]);
    // A defined interpretation: a kind that no declaration interprets is rejected.
    assert_eq!(codes(&Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "[G] diagram gantt:\n    a -> b;\n")])), ["UNSUPPORTED_DIAGRAM_KIND"]);
}

#[test]
fn the_weight_counts_what_the_check_reports_as_not_read() {
    let text = "primitive API\n[A] The API shall stop.\n[E] The gadget shall frobnicate the widget.\n[P] The API shall log the call because the auditor asks.\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", text)]);
    let report = f.trion(&["verify", "--json"]).json();
    // The weight and the errors are one count: a part without a reading is never in one and not in the other.
    assert_eq!(report["weight"]["unread_parts"].as_u64(), report["opaque"].as_array().map(|a| a.len() as u64), "{}", report["weight"]);
    assert_eq!(report["weight"]["ungrounded_statements"].as_u64(), report["ungrounded"].as_array().map(|a| a.len() as u64), "{}", report["weight"]);
    assert!(report["weight"]["unread_parts"].as_u64() > Some(0) && report["weight"]["ungrounded_statements"].as_u64() > Some(0), "{}", report["weight"]);
    assert!(report["weight"]["grounded_only_through_detailed_by"].is_u64() && report["weight"]["terms_neither"].is_u64(), "{}", report["weight"]);
    // The text report shows both kinds of these errors.
    let plain = f.trion(&["verify"]).stdout;
    assert!(plain.contains("[UNSUPPORTED_SEMANTICS]") && plain.contains("error[ungrounded]"), "{plain}");
}
