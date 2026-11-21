//! The native specification tables account for the reader and its formal vocabulary.

use super::{ledger, root, rule_names, text};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use trion_language::document::{Document, Table, TableCell};
use trion_language::syntax::ast::Core;
use trion_language::{
    parse_document, reading, rules, Lexicon, Package, Severity, SpecRef, SpecSet, VocabularyMode,
};
use trion_solver::{Atom, Formula};

fn documents(path: &str, source: &str) -> Vec<Document> {
    let (parsed, diagnostics) = parse_document(source, path);
    assert!(
        diagnostics
            .iter()
            .all(|entry| entry.severity != Severity::Error),
        "{path}: {diagnostics:?}"
    );
    parsed.documents
}

fn spec(path: &str) -> Vec<Document> {
    documents(path, &fs::read_to_string(root().join(path)).unwrap())
}

fn tables<'a>(
    docs: &'a [Document],
    headings: &'static [&'static str],
) -> impl Iterator<Item = &'a Table> {
    docs.iter()
        .flat_map(|doc| &doc.tables)
        .filter(move |table| table.headings == headings)
}

type Edges = BTreeMap<String, BTreeSet<String>>;

fn names(cell: &str) -> BTreeSet<String> {
    if cell == "None" {
        return BTreeSet::new();
    }
    let words: Vec<_> = cell.split(',').map(|name| name.trim().to_owned()).collect();
    let unique: BTreeSet<_> = words.iter().cloned().collect();
    assert_eq!(unique.len(), words.len(), "duplicate name in {cell}");
    unique
}

fn forward(docs: &[Document]) -> (Edges, BTreeSet<String>) {
    let mut mappings = Edges::new();
    let mut rejected = BTreeSet::new();
    for table in tables(
        docs,
        &["Reading rule", "Pattern", "Contract mapping", "Introduces"],
    ) {
        for row in &table.rows {
            let [TableCell::Text(rule), TableCell::Text(_), TableCell::Text(mapping), TableCell::Text(constructors)] =
                row.cells.as_slice()
            else {
                panic!("{}:{} has an invalid mapping row", table.title, row.line)
            };
            let constructors = names(constructors);
            if mapping == "Rejected" {
                assert!(constructors.is_empty(), "{rule} must have no lowering");
                rejected.insert(rule.clone());
            }
            assert!(
                mappings.insert(rule.clone(), constructors).is_none(),
                "duplicate reading rule {rule}"
            );
        }
    }
    (mappings, rejected)
}

fn backward(docs: &[Document]) -> Edges {
    let mut constructors = Edges::new();
    for table in tables(
        docs,
        &["Constructor", "Signature", "Meaning", "Source rule"],
    ) {
        for row in &table.rows {
            let [TableCell::Text(name), TableCell::Text(_), TableCell::Text(_), TableCell::Text(rules)] =
                row.cells.as_slice()
            else {
                panic!(
                    "{}:{} has an invalid constructor row",
                    table.title, row.line
                )
            };
            let rules = names(rules);
            assert!(!rules.is_empty(), "{name} must have a source rule");
            assert!(
                constructors.insert(name.clone(), rules).is_none(),
                "duplicate constructor {name}"
            );
        }
    }
    constructors
}

fn constructors(formula: &Formula, found: &mut BTreeSet<&'static str>) {
    let kind = match formula {
        Formula::True => "True",
        Formula::Atom(atom) => match atom {
            Atom::Act { .. } => "Act",
            Atom::Forbid { .. } => "Forbid",
            Atom::Discouraged { .. } => "Discouraged",
            Atom::Event { .. } => "Event",
            Atom::Config { .. } => "Config",
            Atom::Val { .. } => "Val",
            Atom::Dom { .. } => "Dom",
            Atom::Num { .. } => "Num",
            Atom::Lin { .. } => "Lin",
            Atom::Before { .. } => "Before",
            Atom::Rel { .. } => "Rel",
            Atom::Role { .. } => "Role",
        },
        Formula::Not(inner) => {
            constructors(inner, found);
            "Not"
        }
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                constructors(item, found);
            }
            if matches!(formula, Formula::And(_)) {
                "And"
            } else {
                "Or"
            }
        }
        Formula::Implies(left, right) => {
            constructors(left, found);
            constructors(right, found);
            "Implies"
        }
    };
    found.insert(kind);
}

#[test]
fn every_reading_rule_and_constructor_has_a_mapping_in_the_specification() {
    let (mut mappings, rejected) = forward(&spec("spec/grammar.trion"));
    let implemented = rule_names();
    assert_eq!(
        mappings.keys().cloned().collect::<BTreeSet<_>>(),
        implemented
    );
    let recorded_rejections: BTreeSet<_> = ledger()
        .iter()
        .filter(|entry| text(entry, "meaning") == "rejected")
        .map(|entry| text(entry, "id"))
        .filter(|id| implemented.contains(*id))
        .map(str::to_owned)
        .collect();
    assert_eq!(rejected, recorded_rejections);

    let (extensions, _) = forward(&spec("spec/extensions.trion"));
    for (rule, targets) in extensions {
        assert!(
            mappings.insert(rule.clone(), targets).is_none(),
            "duplicate rule {rule}"
        );
    }
    let vocabulary = backward(&spec("spec/sentences.trion"));
    let introduced: BTreeSet<_> = mappings.values().flatten().collect();
    assert_eq!(
        introduced,
        vocabulary.keys().collect(),
        "the forward table and formal vocabulary must have the same targets"
    );
    for (target, origins) in vocabulary {
        for origin in origins {
            assert!(
                mappings
                    .get(&origin)
                    .is_some_and(|targets| targets.contains(&target)),
                "{target} has no forward mapping from {origin}"
            );
        }
    }
}

#[test]
fn extension_sentence_mappings_name_supported_readings() {
    let (grammar, rejected) = forward(&spec("spec/grammar.trion"));
    let extensions = spec("spec/extensions.trion");
    let ledger_ids: BTreeSet<_> = ledger()
        .iter()
        .map(|entry| text(entry, "id").to_owned())
        .collect();
    let mut found = BTreeSet::new();
    for table in tables(
        &extensions,
        &["Extension rule", "Extended pattern", "Controlled form and mapping", "Target reading rules"],
    ) {
        for row in &table.rows {
            let [TableCell::Text(extension), TableCell::Text(_), TableCell::Text(_), TableCell::Text(targets)] =
                row.cells.as_slice()
            else {
                panic!("{}:{} has an invalid extension mapping", table.title, row.line);
            };
            assert!(ledger_ids.contains(extension), "unknown extension {extension}");
            assert!(found.insert(extension.as_str()), "duplicate extension {extension}");
            let targets = names(targets);
            assert!(!targets.is_empty(), "{extension} must name a target reading");
            for target in targets {
                assert!(
                    target == "Sentence" || (grammar.contains_key(&target) && !rejected.contains(&target)),
                    "{extension} has no supported reading {target}"
                );
            }
        }
    }
    assert_eq!(
        found,
        BTreeSet::from([
            "doc-table", "doc-shared-context", "doc-for-each", "doc-otherwise",
            "doc-concept", "doc-diagram", "composition-flow", "flow-choice",
        ])
    );
}

#[test]
fn published_sentence_readings_introduce_only_mapped_constructors() {
    let (mappings, rejected) = forward(&spec("spec/grammar.trion"));
    let mut discrepancies = Vec::new();
    for file in ["spec/catalog.trion", "spec/sentences.trion"] {
        for example in spec(file).into_iter().flat_map(|doc| doc.examples) {
            if example.kind != "reading" || example.form.as_deref() != Some("contract") {
                continue;
            }
            let source = format!("namespace test\n{}\n", example.input.as_deref().unwrap());
            let docs = documents(file, &source);
            for spec in docs.iter().flat_map(|doc| &doc.specs) {
                let sentence = &spec.sentence;
                let rule_ids = rules(sentence);
                let allowed: BTreeSet<_> = rule_ids
                    .iter()
                    .flat_map(|rule| &mappings[*rule])
                    .map(String::as_str)
                    .collect();
                assert!(
                    rule_ids.iter().all(|rule| !rejected.contains(*rule)),
                    "{}",
                    sentence.source
                );
                let reference = SpecRef {
                    id: spec.display_id(),
                    file: file.into(),
                    line: example.line,
                    text: sentence.source.clone(),
                };
                let reading = reading::read_sentence(
                    sentence,
                    spec.otherwise,
                    &reference,
                    &Lexicon::default(),
                );
                if matches!(&sentence.core, Core::Definition { .. }) {
                    assert_eq!(reading.condition, Formula::True);
                    assert!(reading.claim.is_none());
                    continue;
                }
                let mut actual = BTreeSet::new();
                constructors(&reading.condition, &mut actual);
                if let Some(claim) = &reading.claim {
                    constructors(claim, &mut actual);
                }
                let missing: Vec<_> = actual.difference(&allowed).copied().collect();
                if !missing.is_empty() {
                    discrepancies.push(format!(
                        "{}: {missing:?} in {} from {rule_ids:?}",
                        reference.id, sentence.source
                    ));
                }
            }
        }
    }
    assert!(discrepancies.is_empty(), "{}", discrepancies.join("\n"));
}

#[test]
fn every_formal_constructor_is_produced_by_a_declared_source_rule() {
    let vocabulary = backward(&spec("spec/sentences.trion"));
    let mut covered = BTreeSet::new();
    for (rule, source, targets) in [
        (
            "obligation",
            "[WITNESS] The API shall stop.",
            &["True", "And", "Act", "Not"][..],
        ),
        ("prohibition", "[WITNESS] The API shall not stop.", &["Forbid"]),
        ("recommendation-against", "[WITNESS] The API should not stop.", &["Discouraged"]),
        ("clause-verbal", "[WITNESS] The API shall stop if the door opens.", &["Event"]),
        ("frame-where", "[WITNESS] Where the car has a sunroof, the car shall stop.", &["Config"]),
        ("predicate-words", "[WITNESS] While the door is open, the API shall stop.", &["Val"]),
        ("predicate-enumeration", "[WITNESS] The door is open or closed.", &["Dom"]),
        ("predicate-comparison", "[WITNESS] The size is at most 10 MB.", &["Num"]),
        ("relation", "[WITNESS] The timeout exceeds the retry interval.", &["Lin"]),
        (
            "composition-sequence",
            "[WITNESS] The API shall perform the following actions in order:\n    stop;\n    log the stop;",
            &["Before"],
        ),
        ("description", "[WITNESS] The API is a service.", &["Rel"]),
        ("doc-bind", "role interface:\n    activate: The $subject shall stop.\nbind API as example.interface.", &["Role"]),
        ("actions-either", "[WITNESS] The API shall either stop or restart.", &["Or"]),
        ("condition-if-and-only-if", "[WITNESS] The API shall start exactly when the bell rings.", &["Implies"]),
    ] {
        let mut docs = documents("witness.trion", &format!("namespace example\n{source}\n"));
        for doc in &mut docs {
            doc.namespace.clear();
        }
        if rule == "doc-bind" {
            assert_eq!(docs.iter().map(|doc| doc.bindings.len()).sum::<usize>(), 1);
        } else {
            let sentence = docs.iter().flat_map(|doc| &doc.specs).next().unwrap();
            assert!(rules(&sentence.sentence).contains(&rule), "{rule}: {source}");
        }
        let set = SpecSet {
            packages: vec![Package { name: "example".into(), is_root: true, documents: docs }],
            vocabulary_mode: VocabularyMode::Inferred,
        };
        let model = reading::compile(&set, &Lexicon::of(&set), reading::DEFAULT_SCOPE);
        let mut found = BTreeSet::new();
        for entry in &model.constraints {
            if rule == "doc-bind" || entry.refs.first().is_some_and(|reference| reference.id == "WITNESS") {
                constructors(&entry.assume, &mut found);
                constructors(&entry.guarantee, &mut found);
            }
        }
        for target in targets {
            assert!(vocabulary[*target].contains(rule), "{target} lacks its source rule {rule}");
            assert!(found.contains(target), "{rule} didn't generate {target}: {found:?}");
            covered.insert(*target);
        }
    }
    assert_eq!(covered, vocabulary.keys().map(String::as_str).collect());
}
