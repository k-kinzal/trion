//! A definition constrains: a description that denies what the definition
//! says leaves no environment with it (`incompatible`), and the same
//! statement is consistent where the term is a primitive without the
//! definition. Each test reads the definition from the
//! specification of trion or from its standard vocabulary, so it follows
//! their wording. No test names an atom.

mod common;
use common::*;
use std::fs;

/// The definition of `term` in a file of the repository.
fn definition(file: &str, term: &str) -> String {
    let text = fs::read_to_string(repo_root().join(file)).unwrap();
    let found = text.lines().map(str::trim).find(|line| ["A", "An", "The"].iter().any(|article| line.starts_with(&format!("{article} {term} means "))));
    found.unwrap_or_else(|| panic!("{file} does not define `{term}`")).to_string()
}

fn package(body: &str) -> Fixture {
    let indented: String = body.lines().map(|line| if line.is_empty() { "\n".to_string() } else { format!("    {line}\n") }).collect();
    Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\nentry = \"a.trion\"\n"), ("a.trion", &format!("package p edition \"1\"\n\nnamespace p.x:\n{indented}"))])
}

fn codes(body: &str) -> (i32, Vec<String>) {
    let out = package(body).verify(&["--json"]);
    let report = out.json();
    let mut codes = report_codes(&report);
    for list in ["opaque", "ungrounded"] {
        if report[list].as_array().is_some_and(|l| !l.is_empty()) {
            codes.push(list.to_string());
        }
    }
    (out.code, codes)
}

/// The definition of `term` contradicts `denial`, and `denial` alone, over
/// primitives, is consistent. `others` are the further terms of the denial.
fn constrains(file: &str, term: &str, others: &[&str], denial: &str) {
    let text = definition(file, term);
    let declared: String = others.iter().map(|t| format!("primitive {t}\n")).collect();
    let (code, with) = codes(&format!("{declared}\n[DEFINITION] {text}\n\n[DENIAL] {denial}\n"));
    // The denial is a description of no actor of a system: an assumption.
    // With the definition it allows no environment.
    assert!(with.iter().any(|c| c == "incompatible"), "the definition of `{term}` does not exclude `{denial}`: it constrains nothing here (codes {with:?})\n{text}");
    assert_eq!(code, 1);
    let (code, without) = codes(&format!("primitive {term}\n{declared}\n[DENIAL] {denial}\n"));
    assert!(without.is_empty() && code == 0, "`{denial}` must be consistent without the definition of `{term}`: {without:?}");
}

#[test]
fn a_contract_is_a_pair() {
    constrains("stdlib/formal/trion.trion", "contract", &["pair", "assumption", "guarantee"], "No contract is a pair.");
}

#[test]
fn a_model_is_a_situation() {
    constrains("stdlib/formal/trion.trion", "model", &["situation", "formula", "formula set"], "No model is a situation.");
}

#[test]
fn a_command_is_a_program() {
    constrains("stdlib/software/trion.trion", "command", &["program", "person"], "No command is a program.");
}

#[test]
fn a_statement_is_a_sentence() {
    constrains("spec/trion.trion", "statement", &["sentence", "trion language"], "No statement is a sentence.");
}

#[test]
fn a_simple_sentence_is_a_statement() {
    constrains("spec/sentences.trion", "simple sentence", &["statement", "composite vocabulary"], "No simple sentence is a statement.");
}

#[test]
fn a_permission_over_an_action_list_is_one_permission() {
    // One permission over the composition: a prohibition of one item denies
    // the permission of the list, as it denies a permission of that item.
    let list = "primitive user\nprimitive report\n\n[P] The user may perform all of the following actions:\n    create a report;\n    send the report;\n";
    let (_, single) = codes("primitive user\nprimitive report\n\n[P] The user may send the report.\n[N] The user shall not send the report.\n");
    assert!(single.iter().any(|c| c == "contradiction"), "{single:?}");
    let (_, denied) = codes(&format!("{list}\n[N] The user shall not send the report.\n"));
    assert!(denied.iter().any(|c| c == "contradiction"), "a prohibition of one item must deny the permission of the list: {denied:?}");
    // The list is one entry of the kind permission, not one permission for each item.
    let model = package(list).inspect(&["model", "--json"]).json();
    let constraints = model.get("constraints").or_else(|| model["model"].get("constraints")).and_then(|c| c.as_array()).cloned().unwrap_or_default();
    let permissions = constraints.iter().filter(|c| c["kind"] == "Permission" && c["refs"][0]["id"] == "P").count();
    assert_eq!(permissions, 1, "`all of the following actions` under `may` is one permission: {constraints:#?}");
    // Permission creates no obligation: the list alone is consistent.
    let (code, alone) = codes(list);
    assert!(alone.is_empty() && code == 0, "{alone:?}");
}
