//! Rules of the language draft that the parser and the
//! analysis decide on their own.

mod common;
use common::*;
use trion_language::document::Meta;
use trion_language::syntax::ast::{Core, Purpose, VpGroup};
use trion_language::{parse_document, parse_sentence, ParsedFile, VocabularyMode};
use trion_verification::{Options};

// Diagrams, flows, conformance examples, EARS and the package overview.

#[test]
fn an_ears_requirement_has_a_subject_and_a_response() {
    assert!(parse_sentence("When the door opens, shall stop.").unwrap_err().contains("no subject"));
    assert!(parse_sentence("The API shall.").unwrap_err().contains("needs a response"));
    let one = parse_sentence("When the door opens, the API shall stop.").unwrap();
    assert!(matches!(one.core, Core::Deontic { vp: VpGroup::Single(_), .. }), "{:?}", one.core);
    let two = parse_sentence("When the door opens, the API shall stop and log the stop.").unwrap();
    assert!(matches!(&two.core, Core::Deontic { vp: VpGroup::All { items, .. }, .. } if items.len() == 2), "{:?}", two.core);
}

#[test]
fn an_ears_requirement_has_one_trigger_and_any_number_of_states() {
    let none = parse_sentence("The API shall stop.").unwrap();
    assert!(none.frames.trigger.is_none() && none.frames.states.is_empty());
    let states = parse_sentence("While the door is open, while the light is lit, the API shall stop.").unwrap();
    assert_eq!((states.frames.states.len(), states.frames.trigger.is_some()), (2, false));
    let both = parse_sentence("While the door is open, while the light is lit, when the bell rings, the API shall stop.").unwrap();
    assert_eq!((both.frames.states.len(), both.frames.trigger.is_some()), (2, true));
    assert!(parse_sentence("When the door opens, when the bell rings, the API shall stop.").unwrap_err().contains("one trigger frame"));
    assert!(parse_sentence("If the door opens, when the bell rings, the API shall stop.").unwrap_err().contains("one trigger frame"));
}

#[test]
fn a_source_file_parses_as_one_trion_document() {
    let (parsed, diags) = parse_document("package p\nnamespace p:\n    [A] The API shall stop.\n", "a.trion");
    assert!(diags.is_empty(), "{diags:?}");
    assert_eq!(parsed.package.map(|p| p.name), Some("p".to_string()));
    assert_eq!(parsed.documents.len(), 1);
    assert_eq!(parsed.documents[0].namespace, "p");
    assert_eq!(parsed.documents[0].specs.len(), 1);
    // A file that is not written in the language is rejected, not read as prose.
    let (_, diags) = parse_document("Stop the API when asked\n", "b.trion");
    assert!(!diags.is_empty());
}

// Surface forms, English sentences and vocabulary.

/// Parses statements inside `namespace main:` and returns the file with its diagnostic codes.
fn c_parse(src: &str) -> (ParsedFile, Vec<String>) {
    let (parsed, diags) = parse_document(&wrap("main", src), "main.trion");
    (parsed, diags.into_iter().map(|d| d.code).collect())
}

#[test]
fn a_single_line_string_escapes_a_quote_and_a_backslash() {
    let (parsed, codes) = c_parse("source DOC:\n    title \"a \\\"quoted\\\" word and a \\\\ backslash\"\n    locator \"l\"\n");
    assert!(codes.is_empty(), "{codes:?}");
    assert_eq!(parsed.documents[0].sources[0].title.as_deref(), Some("a \"quoted\" word and a \\ backslash"));
    // Without its closing quote the string does not end, and a line break does not close it.
    assert_eq!(c_parse("note \"unterminated\n").1, ["parse-note"]);
    // An unescaped quote ends the string, so what follows it is not part of the note.
    assert_eq!(c_parse("note \"one\" two\"\n").1, ["parse-note"]);
}

#[test]
fn quoted_excerpts_notes_titles_locators_and_inputs_are_data() {
    let src = "source DOC:\n    title \"end\"\n    locator \"namespace other:\"\n    quote Q \"[X] The API may not stop. パーサーは拒否する。\"\nnote \"[Y] The bell may not ring. end\"\nexample E:\n    kind syntax\n    form statement\n    input \"The API may not stop.\"\n    expect rejected\n";
    let (parsed, codes) = c_parse(src);
    assert!(codes.is_empty(), "{codes:?}");
    assert_eq!(parsed.documents.len(), 1);
    let doc = &parsed.documents[0];
    assert!(doc.specs.is_empty(), "quoted text declares no statement: {:?}", doc.specs);
    let source = &doc.sources[0];
    assert_eq!(source.title.as_deref(), Some("end"));
    assert_eq!(source.locator.as_deref(), Some("namespace other:"));
    assert_eq!(source.quotes[0].text, "[X] The API may not stop. パーサーは拒否する。");
    assert_eq!(doc.examples[0].input.as_deref(), Some("The API may not stop."));
}

#[test]
fn a_quoted_example_cannot_close_declare_or_load_outside_itself() {
    let src = "example E:\n    kind syntax\n    form statement\n    input \"\"\"\n[Z] The API shall stop.\ninclude \"other.trion\"\n\"\"\"\n    expect rejected \"parse-placement\"\n[A] The bell shall ring.\n";
    let (parsed, codes) = c_parse(src);
    assert!(codes.is_empty(), "{codes:?}");
    assert!(parsed.includes.is_empty(), "the example loads no file");
    assert_eq!(parsed.documents.len(), 1, "the example closes no block");
    let doc = &parsed.documents[0];
    assert_eq!(doc.specs.iter().map(|s| s.display_id()).collect::<Vec<_>>(), ["A"], "the example declares no identifier");
    assert!(doc.examples[0].input.as_deref().unwrap().contains("[Z] The API shall stop."));
    assert_eq!(run_codes(&format!("{src}ref [Z]\n")), ["UNRESOLVED_REFERENCE"]);
}

#[test]
fn a_modal_keyword_alone_does_not_make_a_sentence() {
    for text in ["Shall the API stop.", "The API shall.", "Stop shall the API.", "shall shall shall."] {
        assert!(parse_sentence(text).is_err(), "{text} was accepted");
    }
    assert!(parse_sentence("The API shall stop.").is_ok());
}

#[test]
fn a_parsed_specification_can_still_fail_resolution_and_verification() {
    let src = "[A] The API shall return foo.\n[B] The API shall not return foo.\n";
    let (_, parse_codes) = c_parse(src);
    assert!(parse_codes.is_empty(), "{parse_codes:?}");
    let analysis = proved(&set_of(&[("main", true, src)], VocabularyMode::Declared), &Options::default());
    let codes = codes(&analysis);
    assert!(codes.contains(&"contradiction".to_string()), "{codes:?}");
    assert!(codes.contains(&"UNRESOLVED_TERM".to_string()), "{codes:?}");
}

#[test]
fn a_complex_sentence_orders_feature_state_and_trigger() {
    let sentence = parse_sentence("Where the API is remote, While the pump runs, When the bell rings, the API shall stop.").unwrap();
    assert_eq!(sentence.frames.scopes.len(), 1);
    assert_eq!(sentence.frames.states.len(), 1);
    assert!(sentence.frames.trigger.is_some());
    for text in ["While the pump runs, Where the API is remote, the API shall stop.", "When the bell rings, While the pump runs, the API shall stop.", "When the bell rings, Where the API is remote, the API shall stop."] {
        let error = parse_sentence(text).unwrap_err();
        assert!(error.contains("must come before"), "{text}: {error}");
    }
}

#[test]
fn may_not_is_rejected_with_a_request_for_an_explicit_form() {
    let error = parse_sentence("The API may not stop.").unwrap_err();
    assert!(error.contains("ambiguous") && error.contains("shall not"), "{error}");
    assert!(parse_sentence("The API shall not stop.").is_ok());
}

#[test]
fn a_purpose_is_parsed_and_rejected_because_it_has_no_formal_reading() {
    let so_that = parse_sentence("The API shall stop, so that the pump cools.").unwrap();
    assert!(matches!(so_that.purpose, Some(Purpose::SoThat(_))));
    let in_order = parse_sentence("The API shall stop, in order to save power.").unwrap();
    assert!(matches!(in_order.purpose, Some(Purpose::InOrderTo(_))));
    // The intended consequence is no claim, so a statement that holds one is
    // not accepted: what passes the check is read entirely.
    assert_eq!(unread_codes("The API shall stop, so that the pump cools.\n"), ["UNSUPPORTED_SEMANTICS"]);
    assert_eq!(unread_codes("The API shall stop, in order to save power.\n"), ["UNSUPPORTED_SEMANTICS"]);
}

#[test]
fn coordinated_clauses_keep_their_own_subject_and_speech_act() {
    let both = "[A] The API shall stop and the bell shall not ring.\n";
    assert_eq!(run_codes(&format!("{both}[B] The bell shall ring.\n")), ["contradiction"]);
    assert_eq!(run_codes(&format!("{both}[B] The API shall not stop.\n")), ["contradiction"]);
    // The prohibition belongs to the bell, not to the API.
    assert!(run_codes(&format!("{both}[B] The API shall ring.\n")).is_empty());
    // Each clause keeps its own quantifier.
    // Descriptions are assumptions: two that exclude each other leave no environment.
    assert_eq!(run_codes("There is a pump P.\n[A] Each pump is red and each valve is blue.\n[B] Each pump is never red.\n"), ["incompatible"]);
}

#[test]
fn a_negated_action_list_denies_the_list_as_a_whole() {
    let list = "[A] The API shall not perform all of the following actions:\n    stop;\n    log the stop;\n";
    assert!(run_codes(&format!("{list}[S] The API shall stop.\n")).is_empty());
    assert!(run_codes(&format!("{list}[L] The API shall log the stop.\n")).is_empty());
    assert_eq!(run_codes(&format!("{list}[S] The API shall stop.\n[L] The API shall log the stop.\n")), ["contradiction"]);
}

#[test]
fn a_description_holds_in_its_stated_scope() {
    // Descriptions are assumptions: two that exclude each other leave no environment.
    assert_eq!(run_codes("The pump is red.\nThe pump is never red.\n"), ["incompatible"]);
    // Under a condition the two descriptions say that the condition never
    // holds, and an environment in which the valve is never open exists.
    assert!(run_codes("While the valve is open, the pump is red.\nWhile the valve is open, the pump is never red.\n").is_empty());
    assert!(run_codes("While the valve is open, the pump is red.\nWhile the valve is closed, the pump is never red.\n").is_empty());
}

#[test]
fn a_universal_phrase_applies_to_each_instance() {
    assert_eq!(run_codes("There is a user U.\nEach user has at most one account.\nThe user has at least two accounts.\n"), ["incompatible"]);
    assert!(run_codes("There is a user U.\nThe user has at least two accounts.\n").is_empty());
    assert_eq!(run_codes("Each pump shall stop.\nThe pump shall not stop.\n"), ["contradiction"]);
}

#[test]
fn numbers_compare_only_in_compatible_dimensions() {
    assert_eq!(run_codes("The timeout is at most 30 seconds.\nThe timeout is at least 1 minute.\n"), ["incompatible"]);
    assert!(run_codes("The timeout is at most 2 minutes.\nThe timeout is at least 90 seconds.\n").is_empty());
    assert_eq!(run_codes("The limit is at most 3 seconds.\nThe limit is at least 5 bytes.\n"), ["unit-mismatch"]);
}

#[test]
fn a_duration_constrains_the_modified_action() {
    assert_eq!(run_codes("The pump shall run for 5 seconds.\nThe pump shall run for at least 10 seconds.\n"), ["contradiction"]);
    assert!(run_codes("The pump shall run for 5 seconds.\nThe pump shall run for at least 3 seconds.\n").is_empty());
    // The duration belongs to running, not to another action of the pump.
    assert!(run_codes("The pump shall run for 5 seconds.\nThe pump shall rest for at least 10 seconds.\n").is_empty());
}

#[test]
fn a_term_with_one_well_typed_interpretation_is_accepted() {
    // An explicit definition, a referenced domain, a declared primitive and a derivation.
    let src = "use lib\nterm API: entity\nA room means a shared channel.\nThe API shall open a room.\nThe gateway shall forward the request.\n";
    let library = "term gateway: entity\n";
    let analysis = proved(&set_of(&[("main", true, src), ("lib", false, library)], VocabularyMode::Inferred), &Options::default());
    assert!(analysis.diagnostics.is_empty(), "{:?}", analysis.diagnostics);
    // A term whose uses do not fit its declared type has no well-typed interpretation.
    assert_eq!(run_codes("term API: entity\nThe status is API.\n"), ["vocabulary-kind-conflict"]);
}

#[test]
fn the_spelling_of_a_word_establishes_no_fact() {
    // Antonyms by spelling are unrelated words until the specification relates them.
    assert!(run_codes("The door is open.\nThe door is closed.\n").is_empty());
    assert!(run_codes("The pump is active.\nThe pump is inactive.\n").is_empty());
    assert!(run_codes("The API shall start.\nThe API shall stop.\n").is_empty());
    assert!(run_codes("The API shall enable the cache.\nThe API shall disable the cache.\n").is_empty());
}

// Composition, sections, contexts, files and names.

fn d_parse(src: &str) -> (trion_language::ParsedFile, Vec<String>) {
    let (file, diags) = parse_document(src, "a.trion");
    (file, diags.into_iter().map(|d| d.code).collect())
}

#[test]
fn a_section_holds_a_title_and_an_ordered_body() {
    let src = concat!(
        "namespace p:\n",
        "    section \"Outer\":\n",
        "        cite R#Q\n",
        "        note \"A remark for the reader.\"\n",
        "        term API: entity\n",
        "        [A] The API shall stop.\n",
        "        ref [A]\n",
        "        example E:\n",
        "            kind syntax\n",
        "            form statement\n",
        "            input \"The API shall stop.\"\n",
        "            expect accepted\n",
        "",
        "        section \"Inner\":\n",
        "            [B] The API shall start.\n",
        "",
        "        [C] The API shall pause.\n",
        "",
        "",
    );
    let (file, codes) = d_parse(src);
    assert!(codes.is_empty(), "{codes:?}");
    let doc = &file.documents[0];
    let specs: Vec<(Option<&str>, Vec<&str>)> = doc.specs.iter().map(|s| (s.id.as_deref(), s.sections.iter().map(String::as_str).collect())).collect();
    assert_eq!(specs, [(Some("A"), vec!["Outer"]), (Some("B"), vec!["Outer", "Inner"]), (Some("C"), vec!["Outer"])]);
    assert_eq!(doc.vocabulary[0].term, "API");
    assert_eq!(doc.references[0].0, "A");
    assert_eq!(doc.examples[0].name, "E");
    // The citation of the section reaches every statement inside it.
    assert!(doc.specs.iter().all(|s| !s.meta.is_empty()));

    // A section without a quoted title is not a section.
    let (_, codes) = d_parse("namespace p:\n    section:\n        [A] The API shall stop.\n");
    assert_eq!(codes, ["parse-block"]);
    let (_, codes) = d_parse("namespace p:\n    section Outer:\n        [A] The API shall stop.\n");
    assert_eq!(codes, ["parse-block"]);
}

#[test]
fn an_include_belongs_to_the_file_level() {
    let (file, codes) = d_parse("package p\ninclude \"a.trion\"\nnamespace p:\n");
    assert!(codes.is_empty(), "{codes:?}");
    assert_eq!(file.includes[0].path, "a.trion");

    let (file, codes) = d_parse("namespace p:\n    include \"a.trion\"\n");
    assert_eq!(codes, ["parse-placement"]);
    assert!(file.includes.is_empty());

    let (file, codes) = d_parse("namespace p:\n    section \"S\":\n        include \"a.trion\"\n");
    assert_eq!(codes, ["parse-placement"]);
    assert!(file.includes.is_empty());

    let (file, codes) = d_parse("namespace p:\n    When the API receives a call:\n        include \"a.trion\"\n");
    assert_eq!(codes, ["parse-placement"]);
    assert!(file.includes.is_empty());
}

#[test]
fn a_rejection_explains_the_violated_rule() {
    let message = |body: &str| {
        let (_, diags) = parse_document(&format!("namespace p\n{body}\n"), "a.trion");
        diags.first().map(|d| d.message.clone()).unwrap_or_else(|| panic!("no diagnostic for {body}"))
    };
    assert_eq!(message("The API shall stop"), "a sentence ends with a period");
    assert!(message("Unless the override is active, the pump shall stop.").contains("the exception follows the core"));
    assert_eq!(message("[A] The API shall perform all of the following actions:\n    stop\n"), "an action item ends with `;`");
    assert_eq!(message("section Outer:"), "write `section \"title\"` or `section \"title\":`");
    assert!(message("include \"a.trion\"").contains("only at the file level"));
}

// Citations, notes, and examples as isolated inputs.

fn e_cites(meta: &[Meta]) -> Vec<String> {
    meta.iter()
        .filter_map(|m| match m {
            Meta::Cite { source, quote } => Some(format!("{source}#{}", quote.as_deref().unwrap_or(""))),
            _ => None,
        })
        .collect()
}

#[test]
fn a_source_may_name_a_revision_and_selected_parts() {
    let src = "source R:\n    title \"The request\"\n    locator \"https://example.com/r\"\n    revision \"v2\"\n    select \"section 3\"\n    select \"table 1\"\nsource S:\n    title \"Another\"\n    locator \"https://example.com/s\"\n";
    let docs = documents("main", true, src);
    let sources = &docs[0].sources;
    assert_eq!(sources[0].revision.as_deref(), Some("v2"));
    assert_eq!(sources[0].select, ["section 3", "table 1"]);
    assert_eq!((sources[1].revision.as_deref(), sources[1].select.len()), (None, 0), "both fields are optional");
}

#[test]
fn a_quote_keeps_its_text_its_language_and_its_source() {
    let src = "source R:\n    title \"Request\"\n    locator \"r.txt\"\n    quote ONE \"要求その一です。  二つの空白も残る。\"\n    quote TWO \"The API  stops.\"\n";
    let docs = documents("main", true, src);
    let source = &docs[0].sources[0];
    assert_eq!(source.name, "R");
    let quotes: Vec<(&str, &str)> = source.quotes.iter().map(|q| (q.name.as_str(), q.text.as_str())).collect();
    assert_eq!(quotes, [("ONE", "要求その一です。  二つの空白も残る。"), ("TWO", "The API  stops.")]);
    // A normative sentence must be controlled English; a quotation need not be.
    let (_, diags) = parse_document(&wrap("main", "[A] 要求は停止しなければならない。\n"), "main.trion");
    assert!(!diags.is_empty(), "a Japanese statement is not a trion sentence");
}

#[test]
fn a_nested_citation_adds_to_the_inherited_ones() {
    let src = "section \"Outer\":\n    cite R#ONE\n    section \"Inner\":\n        cite R#TWO\n        [A] The API shall stop.\n            cite R#THREE\n    [B] The API shall start.\n";
    let docs = documents("main", true, src);
    let spec = |id: &str| docs[0].specs.iter().find(|s| s.display_id() == id).unwrap();
    let mut a = e_cites(&spec("A").meta);
    a.sort();
    assert_eq!(a, ["R#ONE", "R#THREE", "R#TWO"]);
    assert_eq!(e_cites(&spec("B").meta), ["R#ONE"]);
}

#[test]
fn an_if_condition_is_followed_by_then() {
    assert!(parse_sentence("If the door opens, then the API shall stop.").is_ok());
    let error = parse_sentence("If the door opens, the API shall stop.").unwrap_err();
    assert!(error.contains("followed by `then`"), "{error}");
    assert!(parse_sentence("When the door opens, then the API shall stop.").unwrap_err().contains("only after an `If"));
}
