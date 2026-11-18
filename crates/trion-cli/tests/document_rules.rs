//! Specifications written as documents: paragraphs, optional identifiers,
//! explicit scopes, blocks closed by indentation and the flat form.

mod common;
use common::*;
use serde_json::Value;

fn check(text: &str) -> Value {
    Fixture::new(&[("a.trion", text)]).verify(&["--json", "a.trion"]).json()
}

fn codes(text: &str) -> Vec<String> {
    report_codes(&check(text))
}

/// As `codes`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn codes_of_the_analysis(text: &str) -> Vec<String> {
    analysis_codes(&check(text))
}

/// As above, reading what the libraries read instead of running the command.
fn view(args: &[&str], text: &str) -> String {
    let f = Fixture::new(&[("a.trion", text)]);
    let mut all = args.to_vec();
    all.push("a.trion");
    let r = f.inspect(&all);
    format!("{}{}", r.stdout, r.stderr)
}

/// The contracts of the model as (assumption, guarantee), in order.
fn contracts(text: &str) -> Vec<(String, String)> {
    let model = Fixture::new(&[("a.trion", text)]).inspect(&["model", "--json", "a.trion"]).json();
    model["constraints"].as_array().unwrap().iter().map(|c| (c["assume"].to_string(), c["guarantee"].to_string())).collect()
}

const REJECT: &str = "For each source statement S:\n    When the parser rejects S:\n        The parser shall identify the source extent of S.\n        The parser shall explain the violated grammar rule for S.\n";

#[test]
fn line_breaks_blank_lines_and_sections_change_no_meaning() {
    let one_paragraph = "When the bell rings, the API shall stop. The API shall log each call.\n";
    let wrapped = "When the bell rings,\nthe API shall stop.\n\nThe API shall\nlog each call.\n";
    let sectioned = "section \"Stopping\":\n    When the bell rings, the API shall stop.\n\nsection \"Logging\":\n    The API shall log each call.\n";
    let expected = contracts(one_paragraph);
    assert_eq!(expected.len(), 2);
    assert_eq!(contracts(wrapped), expected);
    assert_eq!(contracts(sectioned), expected);
    // A blank line inside an explicit scope keeps the scope.
    let spaced = REJECT.replace("of S.\n        The parser shall explain", "of S.\n\n        The parser shall explain");
    assert_eq!(contracts(&spaced), contracts(REJECT));
}

#[test]
fn paragraph_regrouping_keeps_the_order_of_a_list_and_one_binder() {
    let list = "When the checker completes an analysis A,\nthe checker shall perform the following actions in order:\n    create an analysis report R for A;\n    retain R;\n";
    let joined = format!("The checker shall log each call.\n{list}The checker shall count each call.\n");
    let apart = format!("The checker shall log each call.\n\n{list}\nThe checker shall count each call.\n");
    let sectioned = format!("section \"Logging\":\n    The checker shall log each call.\n\nsection \"Reports\":\n{}\nsection \"Counting\":\n    The checker shall count each call.\n", list.lines().map(|l| format!("    {l}\n")).collect::<String>());
    // A bound object is named by the place of its binding; the place changes with the layout.
    let placeless = |text: &str| -> Vec<(String, String)> {
        let strip = |formula: String| -> String {
            let mut parts = formula.split("#R@a:");
            let mut out = parts.next().unwrap_or_default().to_string();
            for part in parts {
                out.push_str("#R@");
                out.push_str(part.trim_start_matches(|c: char| c.is_ascii_digit() || c == '/'));
            }
            out
        };
        contracts(text).into_iter().map(|(assume, guarantee)| (assume, strip(guarantee))).collect()
    };
    let expected = placeless(&joined);
    assert_eq!(expected.len(), 3, "{expected:?}");
    assert_eq!(placeless(&apart), expected);
    assert_eq!(placeless(&sectioned), expected);
    // The written order of the list is a temporal relation of the model, and
    // the object that the first item binds is the object of the second item.
    let ordered = &expected[1].1;
    assert!(ordered.contains("Before"), "{ordered}");
    assert!(ordered.contains("create #R@ analysis report") && ordered.contains("retain #R@ analysis report"), "{ordered}");
}

#[test]
fn a_statement_means_the_same_whatever_stands_before_it() {
    let alone = contracts("The parser shall preserve source locations.\n");
    let after = contracts("When the parser rejects an input I, the parser shall report the reason for rejecting I.\nThe parser shall preserve source locations.\n");
    // The condition of the first sentence does not reach the second one.
    assert_eq!(after[1], alone[0]);
    assert!(after[0].0.contains("Event"), "{after:?}");
    // Independent statements of one scope may change places.
    let mut swapped = contracts("The parser shall preserve source locations.\nWhen the parser rejects an input I, the parser shall report the reason for rejecting I.\n");
    swapped.reverse();
    assert_eq!(swapped, after);
}

#[test]
fn a_variable_is_bound_in_its_sentence_or_in_an_enclosing_block() {
    let split = "When the checker completes an analysis A, the checker shall create an analysis report R for A.\nThe checker shall retain R.\n";
    let report = check(split);
    assert_eq!(analysis_codes(&report), ["UNBOUND_VARIABLE"], "{report}");
    let diagnostic = &report["diagnostics"][0];
    assert!(diagnostic["message"].as_str().unwrap().contains("`R`"), "{diagnostic}");
    assert_eq!(diagnostic["refs"][0]["text"], "The checker shall retain R.");
    // The same reference inside the block that binds it is closed.
    assert!(codes_of_the_analysis(REJECT).is_empty());
    // A paragraph break does not bind anything either.
    assert_eq!(codes_of_the_analysis("The checker shall retain R.\n"), ["UNBOUND_VARIABLE"]);
    // A capital letter after a copula is a value, not a variable.
    assert!(codes_of_the_analysis("The grade is A or B.\n").is_empty());
    // A pronoun without a condition before it has nothing to refer to.
    assert_eq!(codes_of_the_analysis("It shall stop.\n"), ["UNRESOLVED_REFERENCE"]);
}

#[test]
fn a_pronoun_takes_the_one_subject_of_the_conditions() {
    assert!(view(&["model"], "[A] When the server fails, it shall restart.\n").contains("Act(server|restart)"));
    assert_eq!(codes_of_the_analysis("While the pump is active, when the valve opens, it shall close.\n"), ["AMBIGUOUS_REFERENCE"]);
    // Conditions about one subject leave nothing to choose.
    assert!(codes_of_the_analysis("While the pump is active, when the pump overheats, it shall stop.\n").is_empty());
}

#[test]
fn a_block_shares_its_condition_and_its_subject() {
    let both = contracts(REJECT);
    assert_eq!(both.len(), 2);
    assert_eq!(both[0].0, both[1].0);
    assert!(both[0].0.contains("parser reject source statement"), "{both:?}");
    let expansion = view(&["expand"], REJECT);
    assert!(expansion.contains("When the parser rejects the source statement, the parser shall identify the source extent of the source statement."), "{expansion}");
    assert!(expansion.contains("the parser shall explain the violated grammar rule for the source statement."), "{expansion}");
    // `For each` names what it quantifies.
    assert_eq!(codes_of_the_analysis("For each U:\n    The parser shall stop.\n"), ["parse-block"]);
}

#[test]
fn a_composition_keeps_one_object_across_its_items() {
    let text = "[D]\nWhen the checker completes an analysis A,\nthe checker shall perform the following actions in order:\n    create an analysis report R for A;\n    retain R;\n";
    assert!(codes_of_the_analysis(text).is_empty());
    let expansion = view(&["expand"], text);
    assert!(expansion.contains("create an analysis report for the analysis;"), "{expansion}");
    assert!(expansion.contains("retain the analysis report;"), "{expansion}");
    let model = view(&["model"], text);
    // The report that the first item creates is the report that the second item retains:
    // one object of this statement, marked with its binding.
    let created = model.split("Before(checker|create ").nth(1).and_then(|rest| rest.split(" analysis report").next()).expect("an ordered pair").to_string();
    assert!(created.starts_with("#R@"), "{model}");
    assert!(model.contains(&format!("checker|retain {created} analysis report)")), "{model}");
    // What holds of every analysis report holds of that one. The trigger is
    // the environment's here: one that the system controls and that nothing
    // requires leaves the statement vacuous for a system that never takes it.
    let submitted = text.replace("When the checker completes an analysis A", "When a user submits an analysis A");
    assert_eq!(codes_of_the_analysis(&format!("{submitted}[E] The checker shall not retain an analysis report.\n")), ["contradiction"]);
    // Two statements that each introduce a report speak of two objects, which may be one or two.
    let apart = "[D1] When the bell rings, the checker shall perform the following actions in order:\n    create a report R;\n    retain R;\n[D2] When the bell rings, the checker shall perform the following actions in order:\n    create a report R;\n    discard R;\n";
    assert!(codes_of_the_analysis(apart).is_empty(), "{:?}", codes_of_the_analysis(apart));
    // Joined by `and`, the two actions would be sentences of their own, and
    // the report of the one would not be the report of the other: refused.
    assert_eq!(codes_of_the_analysis("[D1] When the bell rings, the checker shall create a report R and shall retain R.\n"), ["composite-not-distributive"]);
    // An object of a condition is every such object, as before.
    let general = "[G1] When a user submits an analysis A, the checker shall log A.\n[G2] When a user submits an analysis B, the checker shall not log B.\n";
    assert_eq!(codes_of_the_analysis(general), ["contradiction"]);
    // The marks of bound objects are no part of what an author reads.
    assert!(!view(&["glossary"], text).contains('#'));
    // The checker itself creates one report of an analysis, with the revision of what it read.
    let f = Fixture::new(&[("a.trion", "[A] The API shall stop.\n[B] The API shall not stop.\n")]);
    let kept = f.verify(&["--json", "a.trion"]).json();
    assert!(kept["proof"]["subject"]["revision"].is_string(), "{kept}");
    assert_eq!(analysis_codes(&kept), ["contradiction"]);
}

#[test]
fn a_rejection_names_the_extent_the_rule_and_the_original_text() {
    let text = "The API shall stop. The API for\n   gRPC.\nThe bell shall ring.\n";
    let report = check(text);
    assert_eq!(analysis_codes(&report), ["MISSING_PREDICATE"], "{report}");
    let diagnostic = &report["diagnostics"][0];
    let at = &diagnostic["refs"][0];
    // The fixture puts the namespace header on the first line.
    assert_eq!(at["line"], 2);
    assert_eq!(at["text"], "The API for gRPC.");
    assert!(diagnostic["message"].as_str().unwrap().contains("pivot"), "{diagnostic}");
    // The statements around the rejected one are kept.
    let model = Fixture::new(&[("a.trion", text)]).inspect(&["model", "--json", "a.trion"]).json();
    assert_eq!(model["constraints"].as_array().unwrap().len(), 2);
}

#[test]
fn a_paragraph_holds_sentences_and_an_identifier_names_the_first() {
    let text = "[FIRST]\nThe API shall stop. The API shall log\neach call. The bell shall ring.\n";
    let model = Fixture::new(&[("a.trion", text)]).inspect(&["model", "--json", "a.trion"]).json();
    let ids: Vec<&str> = model["constraints"].as_array().unwrap().iter().map(|c| c["refs"][0]["id"].as_str().unwrap()).collect();
    // The second sentence starts on the line of the first one; the third is the first to start on its line.
    assert_eq!(ids, ["FIRST", "a.trion:3:21", "a.trion:4"]);
}

#[test]
fn indentation_decides_what_a_block_holds() {
    let nested = "When the bell rings:\n    [A] The API shall stop.\n    While the door is open:\n        [B] The API shall wait.\n    [C] The API shall log the stop.\n[D] The API shall start.\n";
    let model = Fixture::new(&[("a.trion", nested)]).inspect(&["model", "--json", "a.trion"]).json();
    let assume = |id: &str| model["constraints"].as_array().unwrap().iter().find(|c| c["refs"][0]["id"] == id).unwrap()["assume"].to_string();
    assert!(assume("A").contains("bell ring") && !assume("A").contains("door"), "{}", assume("A"));
    assert!(assume("B").contains("bell ring") && assume("B").contains("door"), "{}", assume("B"));
    assert_eq!(assume("C"), assume("A"));
    assert!(!assume("D").contains("bell"), "{}", assume("D"));
    // The same lines with other indentation are another structure.
    let flat = nested.replace("        [B]", "    [B]");
    let model = Fixture::new(&[("a.trion", &flat)]).verify(&["--json", "a.trion"]).json();
    assert_eq!(analysis_codes(&model), ["parse-block"], "an empty block: {model}");
    // `end` is not part of the language.
    assert_eq!(codes_of_the_analysis("When the bell rings:\n    [A] The API shall stop.\nend\n"), ["parse-block"]);
    assert_eq!(codes_of_the_analysis("[A] The API shall perform all of the following actions:\n    stop;\n    end\n"), ["parse-block"]);
}

#[test]
fn a_citation_inside_a_composition_belongs_to_its_statement() {
    let f = Fixture::new(&[("trion.toml", "[package]\nname = \"p\"\n"), ("req.txt", "Stop and log."), ("a.trion", &format!("{}\n[A] The API shall perform all of the following actions:\n    cite R#ALL\n    stop;\n    log the stop;\n[B] The API shall wait.\n    unsourced \"Not asked for yet.\"\n", source_block("R", "requirement", "req.txt", "Stop and log.", "", &[("ALL", "Stop and log.")])))]);
    let report = f.verify(&["--json"]).json()["sources"].clone();
    // The citation covers the statement of the composition; only the statement that states no source is reported.
    assert_eq!(report_codes(&report), ["unsourced"], "{report}");
    assert_eq!(report["diagnostics"][0]["refs"][0]["id"], "B");
    assert_eq!(report["sources"][0]["percent"], 100.0);
}

#[test]
fn the_flat_form_needs_neither_colon_nor_indentation() {
    let flat = "package chat edition \"1\"\n\nnamespace chat.room\n\nsection \"Room types\"\n\n[ROOM-KINDS] The room type is private or public.\n\nsection \"Room member\"\n\n[MEMBER] Each room has at least one member.\n\nnamespace chat.message\n\n[TEXT] Each message has one text.\n";
    let block = "package chat edition \"1\"\n\nnamespace chat.room:\n    section \"Room types\":\n        [ROOM-KINDS] The room type is private or public.\n    section \"Room member\":\n        [MEMBER] Each room has at least one member.\n\nnamespace chat.message:\n    [TEXT] Each message has one text.\n";
    let manifest = "[package]\nname = \"chat\"\nentry = \"chat.trion\"\n";
    let outline = |text: &str| {
        let f = Fixture::raw(&[("trion.toml", manifest), ("chat.trion", text)]);
        let report = f.verify(&["--json"]).json();
        assert!(report_codes(&report).is_empty(), "{report}");
        f.inspect(&["expand"]).stdout
    };
    assert_eq!(outline(flat), outline(block));
}

#[test]
fn an_indicative_sentence_is_a_description() {
    for sentence in [
        "Each analysis report records the source revision.",
        "Each section organizes content under a title.",
        "The entry file of the package declares the name of the package.",
        "Blank lines between complete sentences separate paragraphs for presentation.",
        "The API uses gRPC communication.",
    ] {
        assert!(codes(&format!("{sentence}\n")).is_empty(), "{sentence}");
    }
    // The verb agrees with its subject: `organizes`, not `content`.
    let model = view(&["model"], "Each section organizes content under a title.\n");
    assert!(model.contains("organize"), "{model}");
    // No word agrees, or the sentence has no verb at all.
    assert_eq!(codes("The trion language for every EARS pattern.\n"), ["MISSING_PREDICATE"]);
    // Two unknown words both agree with a subject before them.
    assert_eq!(codes("The frob wibbles wobble.\n"), ["parse-sentence"]);
    // A description states no obligation, so it contradicts no prohibition of an action.
    assert!(codes("The API uses gRPC communication.\nThe API shall not stop.\n").is_empty());
}

#[test]
fn forms_that_the_document_chapters_use_are_read() {
    let two = view(&["model"], "Verification links may be declared on the test or proof artifact and shall support reverse navigation.\n");
    // The permission reaches each alternative of its role phrase, and only the second predicate is required.
    assert!(two.contains("¬Forbid(verification link|be declared on test)") && two.contains("¬Forbid(verification link|be declared on proof artifact)"), "{two}");
    assert!(two.contains("Act(verification link|support reverse navigation)"), "{two}");
    assert!(!two.contains("Act(Verification links|be declared"), "{two}");
    assert!(codes_of_the_analysis("The path of the file is not part of the qualified name.\n").is_empty());
    let necessary = view(&["expand"], "[A] Each variable shall be available only where the grammar permits a use of that variable.\n");
    assert!(necessary.contains("only when the grammar permits a use of"), "{necessary}");
    assert_eq!(codes_of_the_analysis("[A] Each variable shall be available where the grammar permits the use.\n"), ["parse-sentence"]);
}

#[test]
fn a_context_holds_statements_and_a_flow_answers_a_trigger() {
    assert_eq!(codes_of_the_analysis("When the bell rings:\n    term valve: entity\n    [A] The API shall stop.\n"), ["parse-placement"]);
    let flow = |head: &str| format!("[F] {head} follow this flow:\n    step check: validate the request;\n    start check\n    finish check\n");
    assert_eq!(codes_of_the_analysis(&flow("The API shall")), ["parse-flow"]);
    assert!(codes_of_the_analysis(&flow("When a request arrives, the API shall")).is_empty());
    let inherited = format!("When a request arrives:\n    {}", flow("The API shall").replace('\n', "\n    "));
    assert!(codes_of_the_analysis(inherited.trim_end()).is_empty(), "{:?}", codes_of_the_analysis(inherited.trim_end()));
}

#[test]
fn a_prohibition_reaches_every_alternative_subject_and_a_relation_keeps_its_roles() {
    // `A or B shall not X` leaves neither of them free to do X.
    assert_eq!(codes("primitive parser, loader, binding\n[A] The parser or the loader shall not guess a binding.\n[B] The loader shall guess a binding.\n"), ["contradiction"]);
    assert_eq!(codes("primitive parser, loader, binding\n[A] The parser or the loader shall not guess a binding.\n[B] The parser shall guess a binding.\n"), ["contradiction"]);
    // An obligation of one of two subjects is met by either of them.
    assert!(codes("[A] The parser or the loader shall report the error.\n[B] The loader shall not report the error.\n").is_empty());
    // A relation without an object says what holds in its role phrases.
    let model = view(&["model"], "Each declaration belongs to exactly one namespace.\n");
    assert!(model.contains("belong to namespace") && model.contains("belong to namespace count = 1"), "{model}");
}

#[test]
fn one_namespace_holds_declarations_of_two_files() {
    let manifest = "[package]\nname = \"p\"\nentry = \"p.trion\"\n";
    let entry = "package p edition \"1\"\n\ninclude \"words.trion\"\n\nnamespace p.x:\n    primitive parser\n    [A]\n    The parser shall keep each response.\n    [B]\n    The parser shall not keep a message.\n";
    let words = "namespace p.x:\n    primitive message\n    A response means a message.\n";
    let report = Fixture::raw(&[("trion.toml", manifest), ("p.trion", entry), ("words.trion", words)]).verify(&["--json"]).json();
    // The definition of the second file gives the term of the first file its
    // meaning: a response is a message, so the two rules contradict.
    let codes = report_codes(&report);
    assert_eq!(codes, ["contradiction"], "{report}");
    assert!(report["ungrounded"].as_array().unwrap().is_empty(), "{}", report["ungrounded"]);
}
