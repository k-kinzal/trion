//! The two rules of the language, as properties of every text.
//!
//! 1. A simple sentence, a sentence without composite vocabulary, is read
//!    as exactly one contract.
//! 2. A composite sentence is read as the contracts of the simple sentences
//!    that it abbreviates: the contract of each of them, read alone, and no
//!    other contract.
//!
//! [`violation`] states both as one function of a text: it returns nothing
//! exactly when the text keeps the rules. A text that is no specification
//! keeps them: it is refused, and nothing is read from it. The tests put
//! through it every sentence of a grammar, every pair of sentences of a
//! pool, and thousands of damaged sentences. None of them knows what a
//! sentence means: a text that breaks a rule is a counterexample whatever
//! it says, and the shortest ones are printed.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::PathBuf;
use trion_language::reading::{authored_condition, build_table, compile, silence, DEFAULT_SCOPE};
use trion_language::syntax::composite::is_simple;
use trion_language::{parse_document, parse_sentence, rules, ConstraintKind, Lexicon, Model, Package, Severity, Spec, SpecSet, VocabularyMode};

/// A text read as a package of one namespace.
struct Read {
    set: SpecSet,
    model: Model,
}

impl Read {
    fn specs(&self) -> impl Iterator<Item = &Spec> {
        self.set.packages.iter().flat_map(|package| &package.documents).flat_map(|document| &document.specs)
    }

    /// The contracts of a statement: each as its kind, its assumption and
    /// its guarantee. What stands beside a contract (what a statement
    /// carries to others, what details it) is no contract of the statement.
    fn contracts(&self, id: &str) -> Vec<String> {
        self.model.constraints.iter().filter(|c| !matches!(c.kind, ConstraintKind::Refinement | ConstraintKind::Carried) && c.refs.first().is_some_and(|at| at.id == id)).map(|c| format!("{:?}: {} => {}", c.kind, authored_condition(&self.model, c), c.guarantee)).collect()
    }

    /// The temporal shape of a statement.
    fn shape(&self, id: &str) -> Vec<String> {
        self.model.temporal.iter().filter(|obligation| obligation.statement.id == id).flat_map(|obligation| obligation.lines()).collect()
    }
}

/// Reads a text as the statements of a package, or returns nothing when
/// the text is no specification: it is then refused with an error, or a
/// part of it is not read.
fn read(text: &str) -> Option<Read> {
    let (parsed, diagnostics) = parse_document(&format!("namespace main\n{text}\n"), "main.trion");
    if diagnostics.iter().any(|diagnostic| diagnostic.severity == Severity::Error) {
        return None;
    }
    let mut documents = parsed.documents;
    // The namespace of the package itself is read unqualified, as the loader reads it.
    documents.iter_mut().for_each(|document| document.namespace = String::new());
    let set = SpecSet { packages: vec![Package { name: "main".to_string(), is_root: true, documents }], vocabulary_mode: VocabularyMode::Inferred };
    let lexicon = Lexicon::of(&set);
    let model = compile(&set, &lexicon, DEFAULT_SCOPE);
    // A part of a sentence that no reading rule reads, or a claim that no
    // contract states: the text is rejected.
    let (vocabulary, _) = build_table(&set, &lexicon);
    let silence = silence(&set, &model, &vocabulary, &lexicon);
    (silence.opaque.is_empty() && silence.inexpressible.is_empty()).then_some(Read { set, model })
}

/// What a text shows against the two rules, or nothing when it keeps them.
fn violation(text: &str) -> Option<String> {
    let whole = read(text)?;
    for spec in whole.specs() {
        let id = spec.display_id();
        let contracts = whole.contracts(&id);
        // Every statement holds a simple sentence: a composite sentence
        // stands as the statements of the simple sentences that it abbreviates.
        if !is_simple(&spec.sentence) {
            return Some(format!("`{}` holds composite vocabulary and is read as a whole", spec.sentence.source));
        }
        // Rule 1: exactly one contract.
        if contracts.len() != 1 {
            return Some(format!("`{}` is read as {} contracts: {contracts:?}", spec.sentence.source, contracts.len()));
        }
        // A text of one simple sentence is that sentence alone.
        if spec.abbreviates.is_none() && whole.specs().count() == 1 {
            continue;
        }
        // Rule 2: the contract of a part is that of its simple sentence, read alone.
        let Some(alone) = read(&spec.sentence.source) else {
            return Some(format!("`{}` is no sentence of the language alone", spec.sentence.source));
        };
        let [own] = alone.specs().collect::<Vec<_>>()[..] else {
            return Some(format!("`{}` alone is not one statement", spec.sentence.source));
        };
        if own.sentence != spec.sentence {
            return Some(format!("`{}` alone is not read as itself", spec.sentence.source));
        }
        let (alone_contracts, alone_shape) = (alone.contracts(&own.display_id()), alone.shape(&own.display_id()));
        if alone_contracts != contracts || alone_shape != whole.shape(&id) {
            return Some(format!("`{}` is read as {contracts:?} in the text and as {alone_contracts:?} alone", spec.sentence.source));
        }
    }
    // Rule 2: no other contract. Each contract of the text is the contract of one of its statements.
    let ids: Vec<String> = whole.specs().map(Spec::display_id).collect();
    let foreign: Vec<String> = whole.model.constraints.iter().filter(|c| !matches!(c.kind, ConstraintKind::Refinement | ConstraintKind::Carried) && c.refs.first().is_none_or(|at| !ids.contains(&at.id))).map(|c| format!("{:?}: {} => {}", c.kind, c.assume, c.guarantee)).collect();
    if !foreign.is_empty() {
        return Some(format!("the text holds contracts of no statement: {foreign:?}"));
    }
    None
}

/// Fails with the shortest counterexamples among the texts.
fn keep_the_rules(texts: impl Iterator<Item = String>) -> (usize, usize) {
    let (mut accepted, mut refused) = (0, 0);
    let mut found: Vec<(String, String)> = Vec::new();
    for text in texts {
        match read(&text) {
            Some(_) => accepted += 1,
            None => refused += 1,
        }
        if let Some(why) = violation(&text) {
            found.push((text, why));
        }
    }
    found.sort_by_key(|(text, _)| text.len());
    let shown: Vec<String> = found.iter().take(12).map(|(text, why)| format!("  {text}\n    {why}")).collect();
    assert!(found.is_empty(), "{} texts break a rule; the shortest:\n{}", found.len(), shown.join("\n"));
    (accepted, refused)
}

const SUBJECTS: [&str; 9] = ["the API", "the gateway", "each client", "a user", "some user", "no user", "the API and the gateway", "the API or the gateway", "some user and each admin"];
const MODALS: [&str; 6] = ["shall", "shall not", "must", "should", "should not", "may"];
const ACTIONS: [&str; 16] = [
    "stop",
    "store the message",
    "log the call",
    "send the report to the client",
    "send the report to the client and the auditor",
    "store the message and the call",
    "store the message or the call",
    "store the message and log the call",
    "store the message or log the call",
    "store the message and log the call and notify the client",
    "notify the customer and shall not create an order",
    "either accept the request or reject the request",
    "respond within 5 seconds",
    "validate the request and send the response within 5 seconds",
    "create a report and send the report",
    "create a report and send a report",
];
const CONDITIONS: [&str; 5] = ["", "When the door closes, ", "While the pump runs, ", "If the key is present, then ", "When the door closes and the key is present, "];
const TAILS: [&str; 4] = ["", ", unless the key is present", " only when the door is open", " exactly when the door is open"];

/// Sentences without a modal verb: descriptions, relations, existence and definitions.
const STATED: [&str; 19] = [
    "No member is the owner.",
    "Each guest is a user.",
    "The system shall store each message that a member of a room posts to the room.",
    "When a user posts a message to a room whose mode is maintenance, the system shall reject the message.",
    "When a user that is a member of a room posts a message to the room, the system shall store the message.",
    "The door is open.",
    "The door and the window are open.",
    "The door or the window is open.",
    "The door is never open.",
    "The colour is red, green, or blue.",
    "Each room has a name.",
    "Each room has a name and an owner.",
    "Each order has exactly one buyer.",
    "No request is both accepted and rejected.",
    "There is a gateway.",
    "There is a gateway and a proxy.",
    "A gate means a door that is open.",
    "An author means a person or a program that writes a specification.",
    "The timeout is at most 5 seconds.",
];

fn capital(text: &str) -> String {
    let mut letters = text.chars();
    letters.next().map(|first| first.to_uppercase().chain(letters).collect()).unwrap_or_default()
}

/// Every sentence of the grammar: a condition, a subject, a modal verb, an
/// action and a tail, each from its list.
fn requirements() -> impl Iterator<Item = String> {
    CONDITIONS.iter().flat_map(|condition| {
        SUBJECTS.iter().flat_map(move |subject| {
            MODALS.iter().flat_map(move |modal| {
                ACTIONS.iter().flat_map(move |action| {
                    TAILS.iter().map(move |tail| {
                        let subject = if condition.is_empty() { capital(subject) } else { subject.to_string() };
                        format!("{condition}{subject} {modal} {action}{tail}.")
                    })
                })
            })
        })
    })
}

/// A sequence of numbers that is the same on every run.
struct Sequence(u64);

impl Sequence {
    fn below(&mut self, bound: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % bound as u64) as usize
    }
}

/// A sentence with one word removed, repeated, replaced or moved.
fn damaged(text: &str, sequence: &mut Sequence) -> String {
    const WORDS: [&str; 16] = ["and", "or", "not", "the", "a", "shall", "may", "when", "unless", "only", "either", "both", "no", "some", "each", ","];
    let mut words: Vec<String> = text.trim_end_matches('.').split(' ').map(str::to_string).collect();
    let at = sequence.below(words.len());
    match sequence.below(4) {
        0 => {
            words.remove(at);
        }
        1 => words.insert(at, words[at].clone()),
        2 => words[at] = WORDS[sequence.below(WORDS.len())].to_string(),
        _ => {
            let other = sequence.below(words.len());
            words.swap(at, other);
        }
    }
    format!("{}.", words.join(" "))
}

#[test]
fn every_sentence_of_the_grammar_keeps_the_rules() {
    let (accepted, refused) = keep_the_rules(requirements().chain(STATED.iter().map(|text| text.to_string())));
    // The grammar is no list of sentences that are known to pass: it holds
    // sentences that are read and sentences that are refused.
    assert!(accepted > 5000 && refused > 1000, "{accepted} accepted, {refused} refused");
}

#[test]
fn every_pair_of_sentences_keeps_the_rules() {
    // A specification is a set of sentences: beside another sentence, each
    // sentence has the contract that it has alone.
    let pool: Vec<String> = requirements().step_by(97).chain(STATED.iter().map(|text| text.to_string())).filter(|text| read(text).is_some()).collect();
    assert!(pool.len() > 60, "{}", pool.len());
    let pairs = pool.iter().flat_map(|first| pool.iter().map(move |second| format!("{first}\n{second}")));
    let (accepted, _) = keep_the_rules(pairs);
    assert!(accepted > 3000, "{accepted}");
}

#[test]
fn every_damaged_sentence_keeps_the_rules() {
    // A sentence with a word removed, repeated, replaced or moved is read
    // or refused: it is never read against a rule.
    let mut sequence = Sequence(0x9E37_79B9_7F4A_7C15);
    let sentences: Vec<String> = requirements().step_by(7).chain(STATED.iter().map(|text| text.to_string())).collect();
    let texts: Vec<String> = (0..12_000).map(|_| damaged(&sentences[sequence.below(sentences.len())], &mut sequence)).collect();
    let (accepted, refused) = keep_the_rules(texts.into_iter());
    assert!(accepted > 1000 && refused > 1000, "{accepted} accepted, {refused} refused");
}

#[test]
fn the_examples_of_the_rules_are_read_as_they_state() {
    // The first example: one sentence, one contract.
    let simple = read("the API shall store the message.").expect("a specification");
    let id = simple.specs().next().expect("a statement").display_id();
    assert_eq!(simple.contracts(&id), ["Spec: ⊤ => (Act(API|store message) ∧ ¬Forbid(API|store message) ∧ ¬Discouraged(API|store message))"]);
    // The second example: one sentence, the contracts of two.
    let composite = read("The API shall store the message and log the message.").expect("a specification");
    assert!(!is_simple(&parse_sentence("The API shall store the message and log the message.").expect("a sentence")));
    let contracts: Vec<Vec<String>> = composite.specs().map(|spec| composite.contracts(&spec.display_id())).collect();
    assert_eq!(contracts, [["Spec: ⊤ => (Act(API|store message) ∧ ¬Forbid(API|store message) ∧ ¬Discouraged(API|store message))"], ["Spec: ⊤ => (Act(API|log message) ∧ ¬Forbid(API|log message) ∧ ¬Discouraged(API|log message))"]]);
}

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The names of the reading rules of the reader: each construct of a
/// sentence that is read is read by one of them (`reading/rules.rs`).
fn rule_names() -> BTreeSet<String> {
    let source = fs::read_to_string(root().join("crates/trion-language/src/reading/rules.rs")).unwrap();
    let start = source.find("impl Walk {").expect("the walk of the account");
    let walk = &source[start..start + source[start..].find("\n}\n").expect("the end of the walk")];
    let mut names = BTreeSet::new();
    for inserted in walk.split("self.rules.insert(").skip(1) {
        // The names of one call: each literal that the call gives as its
        // result, at its start or after `=>` or `{`, up to the end of its statement.
        let call = &inserted[..inserted.find(";\n").unwrap_or(inserted.len())];
        let pieces: Vec<&str> = call.split('"').collect();
        for at in (1..pieces.len()).step_by(2) {
            let before = pieces[at - 1].trim_end();
            let result = at == 1 && before.is_empty() || before.ends_with("=>") || before.ends_with('{');
            if result && !pieces[at].is_empty() && pieces[at].chars().all(|c| c.is_ascii_lowercase() || c == '-') {
                names.insert(pieces[at].to_string());
            }
        }
    }
    // The scan reads the file as text: it must not come back with a handful of names.
    assert!(names.len() >= 90, "only {} rule names were read from rules.rs", names.len());
    for known in ["obligation", "frame-while", "noun-phrase-counted", "role-until", "content-of-verb", "statements-and"] {
        assert!(names.contains(known), "the scan of rules.rs lost `{known}`");
    }
    names
}

/// The examples of the specification: the kind and the input of each, by its name.
fn examples(file: &str) -> BTreeMap<String, (String, String)> {
    let text = fs::read_to_string(root().join("spec").join(file)).unwrap();
    let mut found = BTreeMap::new();
    for block in text.split("\n        example ").skip(1) {
        let name = block.split(':').next().unwrap().to_string();
        let kind = block.split("\n            kind ").nth(1).and_then(|rest| rest.lines().next()).unwrap_or_default().to_string();
        let input = match block.split_once("input \"\"\"\n") {
            Some((_, rest)) => rest.split("\n\"\"\"").next().unwrap().to_string(),
            None => block.split_once("input \"").map(|(_, rest)| rest.split("\"\n").next().unwrap().to_string()).unwrap_or_default(),
        };
        found.insert(name, (kind, input));
    }
    found
}

/// The reading rules that an input uses: those of the sentence as it is
/// written, and those of each statement that it is read as.
fn rules_of(input: &str) -> BTreeSet<String> {
    let mut used: BTreeSet<String> = parse_sentence(input).ok().map(|sentence| rules(&sentence)).unwrap_or_default().into_iter().map(str::to_string).collect();
    let (parsed, _) = parse_document(&format!("namespace main\n{input}\n"), "main.trion");
    used.extend(parsed.documents.iter().flat_map(|document| &document.specs).flat_map(|spec| rules(&spec.sentence)).map(str::to_string));
    used
}

/// The forms that the reader names and the language does not read: each
/// with a sentence that holds it. The sentence is rejected.
const NOT_READ: [(&str, &str); 16] = [
    ("concession-while-gerund", "The system shall close the door, while retaining the origin."),
    ("condition-only-if-denied", "The API shall not stop only when the door is open."),
    ("content-of-noun", "The API shall log the fact that the door is open."),
    ("frame-before", "Before the door opens, the API shall stop."),
    ("frame-counted-event", "When 3 users join, the app shall stop."),
    ("noun-phrase-kind-word", "The server shall send the first message to the client."),
    ("noun-phrase-reference", "The API shall notify another user."),
    ("object-zero-or-more", "The API shall send zero or more reports."),
    ("occurrences-in-a-row", "When the login fails twice in a row, the API shall stop."),
    ("permission-denied", "The API may not stop."),
    ("predicate-able-to", "The client is able to retry."),
    ("purpose", "The server shall send the message, in order to stop the client."),
    ("role-by", "The API shall respond by the deadline."),
    ("role-exclusion", "The API shall delete each file except the log."),
    ("role-rate", "The API shall send 3 messages per second."),
    ("subject-counted-descriptive", "At most 5 users have a profile."),
];

/// The reading rules of a flow. A flow is a structure of a trion file that
/// writes sentences: it is no form of sentence of the language.
const OF_A_FILE: [&str; 2] = ["composition-flow", "flow-choice"];

/// The reading rules of composite vocabulary, each with its example.
const COMPOSITE: [(&str, &str); 2] = [("statements-and", "COMPOSITE-CLAUSES"), ("actions-and", "COMPOSITE-VERB-PHRASES")];

#[test]
fn every_reading_rule_is_in_the_catalog_or_its_form_is_rejected() {
    let mut defined = examples("catalog.trion");
    // The forms that the sections of the specification define with an example of their own.
    for file in ["sentences.trion", "composition.trion", "words.trion", "verification.trion"] {
        examples(file).into_iter().for_each(|(name, example)| {
            defined.entry(name).or_insert(example);
        });
    }
    let names = rule_names();
    for (rule, _) in NOT_READ {
        assert!(names.contains(rule), "`{rule}` is no reading rule");
    }
    let mut missing = Vec::new();
    for rule in &names {
        if OF_A_FILE.contains(&rule.as_str()) {
            continue;
        }
        if let Some((_, sentence)) = NOT_READ.iter().find(|(name, _)| name == rule) {
            // The form is rejected: at the parse, or because no rule gives it a meaning.
            if parse_sentence(sentence).is_ok() {
                assert!(rules_of(sentence).contains(rule), "`{sentence}` does not hold the form `{rule}`");
            }
            assert!(read(sentence).is_none(), "`{sentence}` holds the form `{rule}` and is read");
            continue;
        }
        let name = COMPOSITE.iter().find(|(composite, _)| composite == rule).map_or(rule.to_uppercase(), |(_, example)| example.to_string());
        let Some((kind, input)) = defined.get(&name) else {
            missing.push(format!("{rule}: the specification holds no example {name}"));
            continue;
        };
        assert_eq!(kind, "reading", "the example {name}");
        assert!(rules_of(input).contains(rule), "the example {name} does not hold the form `{rule}`: {input}");
        assert!(read(input).is_some(), "the example {name} is not read: {input}");
        assert_eq!(violation(input), None, "the example {name}");
    }
    assert!(missing.is_empty(), "{} reading rules are neither in the catalog nor rejected:\n  {}", missing.len(), missing.join("\n  "));
}

#[test]
fn every_example_of_the_catalog_keeps_the_rules() {
    let catalog = examples("catalog.trion");
    assert!(catalog.len() > 80, "{}", catalog.len());
    for (name, (kind, input)) in &catalog {
        if kind == "syntax" {
            // A sentence that joins requirements and abbreviates no simple sentences.
            assert!(read(input).is_none(), "the example {name} is read: {input}");
            continue;
        }
        let whole = read(input).unwrap_or_else(|| panic!("the example {name} is not read: {input}"));
        assert_eq!(violation(input), None, "the example {name}");
        let statements = whole.specs().count();
        if name.starts_with("COMPOSITE") {
            // Composite vocabulary: one sentence, the contracts of two or more.
            assert!(!is_simple(&parse_sentence(input).expect("a sentence")), "the example {name} holds no composite vocabulary");
            assert!(statements >= 2, "the example {name} is read as {statements} statements");
        } else {
            // A simple sentence: exactly one contract.
            assert_eq!(statements, 1, "the example {name} is read as {statements} statements");
        }
    }
}
