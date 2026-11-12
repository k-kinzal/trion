mod common;
use common::*;
use trion_language::VocabularyMode;
use trion_verification::{analyze, Options};

#[test]
fn infers_terms_and_kinds_from_specifications() {
    let analysis = run("room_type is Private.\nThe API shall return foo.\n");
    let kinds = |t: &str| analysis.vocabulary[t].inferred_kinds.iter().cloned().collect::<Vec<_>>();
    assert_eq!(kinds("room_type"), ["attribute"]);
    assert_eq!(kinds("Private"), ["value"]);
    assert_eq!(kinds("API"), ["entity"]);
    assert_eq!(kinds("foo"), ["object"]);
    assert_eq!(kinds("return"), ["action"]);
    assert_eq!(analysis.vocabulary["API"].declared_kind, None);
}

#[test]
fn records_declared_terms() {
    let analysis = run("term API: entity\nThe API shall stop.\n");
    assert_eq!(analysis.vocabulary["API"].declared_kind.as_deref(), Some("entity"));
    assert_eq!(analysis.vocabulary["API"].occurrences, 1);
}

#[test]
fn declared_mode_rejects_undeclared_terms() {
    let src = "term API: entity\nThe API shall return foo.\n";
    let analysis = analyze(&set_of(&[("main", true, src)], VocabularyMode::Declared), &Options::default());
    let undeclared: Vec<&str> = analysis.diagnostics.iter().filter(|d| d.code == "UNRESOLVED_TERM").map(|d| d.message.as_str()).collect();
    assert_eq!(undeclared, ["the term `foo` has no interpretation: it is not declared"]);
}

#[test]
fn an_undeclared_term_is_accepted_only_where_something_relates_it() {
    // Two statements about one action relate their terms.
    let related = run("[A] The API shall return foo.\n[B] When a call arrives, the API shall return foo.\n");
    assert!(related.silence.ungrounded.is_empty(), "{:?}", related.silence.ungrounded);
    // A statement alone, with terms that nothing declares, is an error that
    // names the terms and says how a term is declared.
    let alone = run("The API shall return foo.\n");
    let [error] = alone.silence.ungrounded.as_slice() else { panic!("{:?}", alone.silence.ungrounded) };
    assert_eq!(error.severity, trion_language::Severity::Error);
    assert!(error.message.contains("`API`") && error.message.contains("`foo`"), "{}", error.message);
    assert!(error.message.contains("`A <term> means …`") && error.message.contains("`primitive <term>`"), "{}", error.message);
    // A declaration grounds them.
    assert!(run("primitive API\nprimitive foo\nThe API shall return foo.\n").silence.ungrounded.is_empty());
}

#[test]
fn a_definition_declares_its_term() {
    let src = "A room means a chat space.\nThe room shall close.\n";
    let analysis = analyze(&set_of(&[("main", true, src)], VocabularyMode::Declared), &Options::default());
    assert!(analysis.diagnostics.iter().all(|d| !d.message.contains("`room`")), "{:?}", analysis.diagnostics);
}

#[test]
fn imported_vocabulary_is_usable() {
    let src = "use lib\nThe API shall stop.\n";
    let library = "term API: entity\n";
    let analysis = analyze(&set_of(&[("main", true, src), ("lib", false, library)], VocabularyMode::Declared), &Options::default());
    assert!(analysis.diagnostics.is_empty(), "{:?}", analysis.diagnostics);
}

#[test]
fn a_use_against_the_declared_kind_is_an_error() {
    assert_eq!(run_codes("term room_type: value\nroom_type is Private.\n"), ["vocabulary-kind-conflict"]);
}

#[test]
fn entity_and_object_are_interchangeable() {
    assert!(run_codes("term API: object\nThe API shall stop.\n").is_empty());
}

#[test]
fn an_unknown_kind_is_an_error() {
    assert_eq!(run_codes("term API: thing\n"), ["vocabulary-unknown-kind"]);
}

#[test]
fn a_redeclaration_with_another_kind_is_an_error() {
    assert_eq!(run_codes("term API: entity\nterm API: value\n"), ["vocabulary-redeclared"]);
}

#[test]
fn an_undeclared_term_used_as_attribute_and_value_warns() {
    assert_eq!(run_codes("status is Open.\nOpen is Yes.\n"), ["vocabulary-kind-ambiguous"]);
}

#[test]
fn similar_spellings_warn() {
    assert_eq!(run_codes("The room_type shall stop.\nThe room_tpye shall start.\n").len(), 0, "transpositions are distance two");
    assert_eq!(run_codes("The room_type shall stop.\nThe room_typo shall start.\n"), ["vocabulary-similar"]);
}

#[test]
fn case_variants_warn_at_any_length() {
    assert_eq!(run_codes("The API shall stop.\nThe api shall start.\n"), ["vocabulary-similar"]);
}

#[test]
fn an_alias_merges_vocabulary_entries() {
    let analysis = run("alias the service = API\nThe service shall stop.\nThe API shall start.\n");
    assert_eq!(analysis.vocabulary["API"].occurrences, 2);
    assert!(!analysis.vocabulary.contains_key("service"));
}

#[test]
fn a_plural_and_its_singular_are_one_term() {
    let analysis = run("The API shall read an import.\nThe API shall write imports.\n");
    assert_eq!(analysis.vocabulary["import"].occurrences, 2);
    assert!(!analysis.vocabulary.contains_key("imports"));
    assert!(codes(&analysis).is_empty(), "{:?}", analysis.diagnostics);
}

#[test]
fn a_lone_word_ending_in_s_is_not_a_plural() {
    let analysis = run("The API shall return the status.\n");
    assert!(analysis.vocabulary.contains_key("status"));
}
