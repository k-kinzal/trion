//! The names of atoms are built from the nodes of the syntax tree by
//! `key.rs`. These tests read the sources of the formalizer and fail when a
//! name is again made from the text of a node, or when a list of
//! closed-class words comes back beside the one in the lexer.

use trion_language::syntax::words::{classify, WordClass};

const FORMALIZER: [&str; 6] = ["model.rs", "meaning.rs", "rules.rs", "grounding.rs", "vocabulary.rs", "instances.rs"];

fn source(file: &str) -> String {
    std::fs::read_to_string(format!("{}/src/reading/{file}", env!("CARGO_MANIFEST_DIR"))).unwrap()
}

/// The code of a source, without its comments.
fn code(file: &str) -> Vec<(usize, String)> {
    source(file).lines().enumerate().map(|(n, line)| (n + 1, line.split("//").next().unwrap_or_default().to_string())).collect()
}

#[test]
fn no_key_is_made_from_the_text_of_a_node() {
    for file in FORMALIZER {
        for (number, line) in code(file) {
            // A name of a declaration is read by `canon`; the text of a node is not.
            let canon_of_render = line.contains("canon(") && line.contains("render()");
            assert!(!canon_of_render, "crates/trion-language/src/reading/{file}:{number}: a name is made from the rendered text of a node: {line}");
            let formatted = line.contains("format!(") && line.contains("render()") && (line.contains("key") || line.contains("Atom::"));
            assert!(!formatted, "crates/trion-language/src/reading/{file}:{number}: a key is formatted from the rendered text of a node: {line}");
        }
    }
    let model = source("model.rs");
    for builder in ["fn np_key(", "fn action_key(", "fn event_key("] {
        let at = model.find(builder).unwrap_or_else(|| panic!("model.rs has no `{builder}`"));
        let body = &model[at..model[at..].find("\n}\n").map_or(model.len(), |end| at + end)];
        assert!(body.contains("crate::reading::key::"), "`{builder}` does not build its key from nodes");
        assert!(!body.contains(".render()"), "`{builder}` renders a node");
    }
}

#[test]
fn the_formalizer_keeps_no_list_of_closed_class_words() {
    for file in FORMALIZER {
        let text: String = code(file).into_iter().map(|(_, line)| line).collect::<Vec<_>>().join("\n");
        // Each array literal of string literals.
        let bytes = text.as_bytes();
        let mut at = 0;
        while let Some(open) = text[at..].find('[').map(|i| at + i) {
            let Some(close) = text[open..].find(']').map(|i| open + i) else { break };
            at = open + 1;
            let inner = &text[open + 1..close];
            if inner.contains('[') || !inner.trim_start().starts_with('"') {
                continue;
            }
            let items: Vec<&str> = inner.split(',').map(|item| item.trim().trim_matches('"')).filter(|item| !item.is_empty()).collect();
            let literal = inner.split(',').all(|item| item.trim().is_empty() || (item.trim().starts_with('"') && item.trim().ends_with('"')));
            if !literal || items.len() < 3 {
                continue;
            }
            let closed: Vec<&&str> = items.iter().filter(|item| item.split(' ').all(|w| matches!(classify(w), WordClass::Closed(_)))).collect();
            let line = bytes[..open].iter().filter(|b| **b == b'\n').count() + 1;
            assert!(closed.len() * 2 < items.len(), "crates/trion-language/src/reading/{file}:{line}: a list of closed-class words stands beside the lexer's: {items:?}");
        }
    }
}

#[test]
fn a_word_of_a_name_is_made_in_one_place() {
    let key = source("key.rs");
    let made = key.matches("class: Class::Word").count();
    assert_eq!(made, 1, "a part of the class `Word` is made in {made} places of key.rs");
    let at = key.find("class: Class::Word").unwrap();
    let arm = &key[key[..at].rfind('\n').unwrap()..at];
    assert!(arm.contains("WordClass::Open =>"), "a word of a name is made without asking the lexer for its class: {arm}");
    for file in FORMALIZER {
        assert!(!source(file).contains("Class::Word"), "{file} makes a word of a name beside key.rs");
    }
}

#[test]
fn an_occurrence_is_named_from_the_nodes_of_its_phrase() {
    // The origin and the order of a response name an occurrence by the key
    // of its noun phrase, never by the rendered text of the phrase.
    for (number, line) in code("temporal.rs") {
        let named = line.contains("Origin::Explicit") || line.contains("related:");
        assert!(!(named && line.contains("render()")), "crates/trion-language/src/reading/temporal.rs:{number}: an occurrence is named from rendered text: {line}");
    }
}

#[test]
fn an_individual_is_named_by_the_noun_of_its_statement() {
    // The name of an individual is a part of the local reading: it does not
    // come from the carrier, which other statements choose.
    let text = source("instances.rs");
    let at = text.find("fn individual(").expect("instances.rs names individuals in `individual`");
    let body = &text[at..text[at..].find("\n    }\n").map_or(text.len(), |end| at + end)];
    assert!(!body.contains("carriers"), "an individual is named by its carrier: {body}");
}
