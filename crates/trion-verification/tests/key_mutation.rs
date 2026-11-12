//! A closed-class word never becomes a word of a name. For each sentence of
//! a corpus, each closed-class word of the lexer is inserted at each
//! position. The result is rejected (by the parser or as a part without a
//! reading), or its model differs from the model of the sentence. It never
//! has the same model, and no key of it holds the word as a word of a name.

mod common;

use trion_language::syntax::words::{closed_words, Closed};
use trion_language::{parse_document, Package, SpecSet, VocabularyMode};
use trion_verification::{analyze, Analysis, Options};

const DECLARATIONS: &str = "primitive parser\nprimitive source file\nprimitive user\nprimitive request\nprimitive server\nprimitive response\nprimitive room\nprimitive message\nprimitive checker\nprimitive statement\nprimitive identifier\nprimitive guest\n";

const CORPUS: [&str; 6] = [
    "The parser shall read the source file.",
    "When the user sends a request, the server shall return a response to the user.",
    "While the room is archived, the user shall not delete the message.",
    "The checker shall report each statement that has no identifier.",
    "The room is archived.",
    "Each guest is a user.",
];

fn read(sentence: &str) -> Option<Analysis> {
    let text = format!("namespace main\n{DECLARATIONS}[S] {sentence}\n");
    let (parsed, diagnostics) = parse_document(&text, "main.trion");
    if !diagnostics.is_empty() {
        return None;
    }
    let documents = parsed
        .documents
        .into_iter()
        .map(|mut doc| {
            if doc.namespace == "main" {
                doc.namespace = String::new();
            }
            doc
        })
        .collect();
    Some(analyze(&SpecSet { packages: vec![Package { name: "main".to_string(), is_root: true, documents }], vocabulary_mode: VocabularyMode::Inferred }, &Options::default()))
}

/// What a model says, without the text of the sentence that it was read from.
fn said(analysis: &Analysis, sentence: &str) -> String {
    let contracts: Vec<String> = analysis.model.constraints.iter().map(|c| format!("{} => {}", c.assume, c.guarantee)).collect();
    let background: Vec<String> = analysis.model.background.iter().map(|f| f.to_string()).collect();
    format!("{contracts:?}\n{background:?}\n{:?}", analysis.model.temporal).replace(sentence, "")
}

fn rejected(analysis: &Analysis) -> bool {
    !analysis.silence.opaque.is_empty() || analysis.diagnostics.iter().any(|d| d.severity == trion_language::Severity::Error)
}

#[test]
fn a_closed_class_word_changes_the_model_or_is_rejected() {
    let mut failures = Vec::new();
    for sentence in CORPUS {
        let original = read(sentence).unwrap_or_else(|| panic!("the corpus sentence does not parse: {sentence}"));
        assert!(!rejected(&original), "the corpus sentence is rejected: {sentence}: {:?} {:?}", original.silence.opaque, original.diagnostics);
        let before = said(&original, sentence);
        let body = sentence.trim_end_matches('.');
        let words: Vec<&str> = body.split(' ').collect();
        for (word, kind) in closed_words() {
            // `eventually` says what every obligation without a deadline
            // says: the action completes at some later moment.
            if trion_language::syntax::words::is_liveness(word) {
                continue;
            }
            for at in 0..=words.len() {
                let before_article = words.get(at).is_some_and(|w| trion_language::syntax::words::is_article(w));
                // `is a member` and `is the member` name the class that `is member` names:
                // the article of a nominal predicate opens its noun phrase.
                if kind == Closed::Article && at > 0 && matches!(words[at - 1], "is" | "are" | "be") {
                    continue;
                }
                // `all the files` and `both the files` are the files.
                if matches!(word, "all" | "both") && before_article {
                    continue;
                }
                let mut mutant: Vec<&str> = words.clone();
                mutant.insert(at, word);
                let mut text = mutant.join(" ") + ".";
                if at == 0 {
                    // The sentence opens with the inserted word.
                    text = format!("{}{}", &text[..1].to_uppercase(), &text[1..]);
                }
                let Some(analysis) = read(&text) else { continue };
                if rejected(&analysis) {
                    continue;
                }
                for (name, parts) in &analysis.model.keys {
                    if parts.iter().any(|p| p.is_word() && p.text().eq_ignore_ascii_case(word)) {
                        failures.push(format!("`{word}` is a word of the name `{name}` in: {text}"));
                    }
                }
                if said(&analysis, &text) == before {
                    failures.push(format!("`{word}` changes nothing in: {text}"));
                }
            }
        }
    }
    assert!(failures.is_empty(), "{} closed-class insertions pass unread:\n{}", failures.len(), failures.join("\n"));
}
