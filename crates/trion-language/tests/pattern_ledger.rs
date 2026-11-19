//! The pattern ledger (`spec/patterns/ledger.toml`) names every reading rule
//! of the account of a reading, classifies each pattern, and points only at
//! code and tests that exist. A new reading rule does not pass without an
//! entry, and an entry does not pass with a stale pointer.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

#[path = "pattern_ledger/contract_mapping.rs"]
mod contract_mapping;

const REQUIRED: [&str; 11] = ["id", "group", "surface", "parser", "parse", "meaning", "lowering", "evidence", "claims", "open", "acceptance"];
const PARSE: [&str; 3] = ["accepted", "rejected", "partial"];
const MEANING: [&str; 4] = ["rule", "nonnormative", "unresolved", "rejected"];
const CLAIMS: [&str; 5] = ["background_sat", "contract_sat", "situation_total", "property_entails", "scenario_satisfiable"];
/// The groups that a pattern may belong to.
const GROUPS: [&str; 18] = [
    "packages",
    "vocabulary",
    "descriptions",
    "modality",
    "conditions",
    "exceptions",
    "phrases",
    "reference-quantity",
    "numeric",
    "composition",
    "time",
    "measure",
    "priority",
    "diagrams",
    "blocks",
    "sources",
    "extensions",
    "concession-purpose-quality",
];
/// What an identifier that is no rule name begins with.
const PREFIXES: [&str; 3] = ["doc-", "rej-", "variant-"];

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn ledger() -> Vec<toml::Table> {
    let text = fs::read_to_string(root().join("spec/patterns/ledger.toml")).expect("spec/patterns/ledger.toml");
    let document: toml::Table = text.parse().expect("the ledger is a TOML document");
    document["pattern"].as_array().expect("an array of [[pattern]] tables").iter().map(|entry| entry.as_table().expect("a table").clone()).collect()
}

fn text<'a>(entry: &'a toml::Table, key: &str) -> &'a str {
    entry.get(key).and_then(toml::Value::as_str).unwrap_or_else(|| panic!("{:?}: `{key}` is a string", entry.get("id")))
}

fn list<'a>(entry: &'a toml::Table, key: &str) -> Vec<&'a str> {
    let id = entry.get("id");
    let items = entry.get(key).and_then(toml::Value::as_array).unwrap_or_else(|| panic!("{id:?}: `{key}` is an array"));
    items.iter().map(|item| item.as_str().unwrap_or_else(|| panic!("{id:?}: `{key}` holds strings"))).collect()
}

/// The argument of the call that opens at `open`, the index of its `(`.
fn argument(source: &str, open: usize) -> &str {
    let (mut depth, mut inside) = (0usize, false);
    let mut previous = ' ';
    for (at, c) in source[open..].char_indices() {
        match c {
            '"' if previous != '\\' => inside = !inside,
            '(' if !inside => depth += 1,
            ')' if !inside => {
                depth -= 1;
                if depth == 0 {
                    return &source[open + 1..open + at];
                }
            }
            _ => {}
        }
        previous = c;
    }
    panic!("an unclosed call in rules.rs");
}

/// Every rule name that `Walk` can insert: the string literal that is the
/// argument of `self.rules.insert(...)`, or the result of an arm of the
/// `match` or of a branch of the `if` that is the argument.
fn rule_names() -> BTreeSet<String> {
    let source = fs::read_to_string(root().join("crates/trion-language/src/reading/rules.rs")).unwrap();
    let start = source.find("impl Walk {").expect("the walk of the account");
    let end = start + source[start..].find("\n}\n").expect("the end of the walk");
    let walk = &source[start..end];
    let result = regex::Regex::new(r#"(?:\A|=>|\{)\s*"([a-z]+(?:-[a-z]+)*)""#).unwrap();
    let call = "self.rules.insert(";
    let mut names = BTreeSet::new();
    let mut from = 0;
    while let Some(found) = walk[from..].find(call) {
        let open = from + found + call.len() - 1;
        let inserted_by = argument(walk, open);
        let inserted: Vec<String> = result.captures_iter(inserted_by).map(|c| c[1].to_string()).collect();
        assert!(!inserted.is_empty(), "no rule name is read from `self.rules.insert({inserted_by})`: write the name as a literal");
        names.extend(inserted);
        from = open + 1;
    }
    // The scan reads the file as text: it must not come back with a handful of names.
    assert!(names.len() >= 80, "only {} rule names were read from rules.rs", names.len());
    for known in ["obligation", "frame-while", "noun-phrase-counted", "role-until", "content-of-verb"] {
        assert!(names.contains(known), "the scan of rules.rs lost `{known}`");
    }
    names
}

/// The files and functions that `file:function; file:function` names.
fn locations(field: &str) -> Vec<(&str, &str)> {
    field.split(';').map(str::trim).filter(|part| !part.is_empty()).map(|part| part.split_once(".rs:").map(|(file, function)| (file, function)).unwrap_or_else(|| panic!("`{part}` is not `file.rs:function`"))).collect()
}

fn source_of(cache: &mut BTreeMap<String, Option<String>>, path: &str) -> Option<String> {
    cache.entry(path.to_string()).or_insert_with(|| fs::read_to_string(root().join(path)).ok()).clone()
}

#[test]
fn every_reading_rule_has_a_pattern() {
    let ids: BTreeSet<String> = ledger().iter().map(|entry| text(entry, "id").to_string()).collect();
    let missing: Vec<String> = rule_names().into_iter().filter(|name| !ids.contains(name)).collect();
    assert!(missing.is_empty(), "spec/patterns/ledger.toml has no [[pattern]] for the reading rules {missing:?}: classify each as rule, nonnormative, unresolved or rejected");
}

#[test]
fn every_pattern_is_classified() {
    let rules = rule_names();
    for entry in ledger() {
        for key in REQUIRED {
            assert!(entry.contains_key(key), "{:?} has no `{key}`", entry.get("id"));
        }
        let id = text(&entry, "id");
        assert!(rules.contains(id) || PREFIXES.iter().any(|prefix| id.starts_with(prefix)), "`{id}` is no rule name of rules.rs and has none of the prefixes {PREFIXES:?}");
        assert!(id.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-'), "`{id}` is not kebab-case");
        assert!(GROUPS.contains(&text(&entry, "group")), "{id}: the group `{}` is no row of the plan", text(&entry, "group"));
        let surface = list(&entry, "surface");
        assert!((1..=3).contains(&surface.len()), "{id}: one to three surface forms");
        assert!(!text(&entry, "parser").is_empty(), "{id}: a pattern names where it is recognised");
        let (parse, meaning) = (text(&entry, "parse"), text(&entry, "meaning"));
        assert!(PARSE.contains(&parse), "{id}: parse = `{parse}`");
        assert!(MEANING.contains(&meaning), "{id}: meaning = `{meaning}`");
        let lowering = text(&entry, "lowering");
        // A meaning rule is produced somewhere; a form that the parser rejects has no meaning.
        assert!(meaning != "rule" || !lowering.is_empty(), "{id}: a meaning rule names its lowering");
        assert!(parse != "rejected" || meaning == "rejected", "{id}: a form that the parser rejects has meaning = \"rejected\"");
        // An unresolved pattern says what is unresolved.
        assert!(meaning != "unresolved" || !list(&entry, "open").is_empty(), "{id}: an unresolved pattern states its open question");
        list(&entry, "evidence");
        for claim in list(&entry, "claims") {
            assert!(CLAIMS.contains(&claim), "{id}: `{claim}` is no claim of the first practical edition");
        }
        for example in list(&entry, "acceptance") {
            // A01-A23 of the plan; a case that is split in two carries a letter, as `A03b` does.
            let plain = example.strip_suffix(|c: char| c.is_ascii_lowercase()).unwrap_or(example);
            let number = plain.strip_prefix('A').and_then(|n| n.parse::<u32>().ok());
            assert!(plain.len() == 3 && number.is_some_and(|n| (1..=23).contains(&n)), "{id}: `{example}` is no acceptance example A01-A23");
        }
        if let Some(rule) = entry.get("rule") {
            let rule = rule.as_str().unwrap_or_default();
            assert!(rules.contains(rule), "{id}: `{rule}` is no rule name of rules.rs");
        }
    }
}

#[test]
fn pattern_identifiers_are_unique() {
    let mut seen = BTreeSet::new();
    for entry in ledger() {
        let id = text(&entry, "id").to_string();
        assert!(seen.insert(id.clone()), "the identifier `{id}` occurs twice");
    }
}

#[test]
fn a_pattern_points_at_code_and_tests_that_exist() {
    let mut cache = BTreeMap::new();
    let mut stale = Vec::new();
    for entry in ledger() {
        let id = text(&entry, "id");
        for key in ["parser", "lowering"] {
            for (file, function) in locations(text(&entry, key)) {
                let path = format!("{file}.rs");
                let name = function.rsplit("::").next().unwrap_or(function);
                let found = source_of(&mut cache, &path).is_some_and(|source| source.contains(&format!("fn {name}(")) || source.contains(&format!("fn {name}<")));
                if !found {
                    stale.push(format!("{id}: {key} `{path}:{function}`"));
                }
            }
        }
        for evidence in list(&entry, "evidence") {
            let Some((path, test)) = evidence.split_once("::") else {
                stale.push(format!("{id}: evidence `{evidence}` is not `path::test_fn`"));
                continue;
            };
            if !source_of(&mut cache, path).is_some_and(|source| source.contains(&format!("fn {test}("))) {
                stale.push(format!("{id}: evidence `{evidence}`"));
            }
        }
    }
    assert!(stale.is_empty(), "the ledger points at what does not exist:\n{}", stale.join("\n"));
}
