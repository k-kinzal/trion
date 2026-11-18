//! `trion-format-rust-test`: an extension format of `trion` (spec/tool.trion,
//! `An extension format means an output format that a program outside the
//! trion processor adds`). `trion --out DIR --format rust-test` runs it.
//!
//! It reads the JSON report of the conversion on its standard input and
//! writes `DIR/specification_tests.rs`: one test for each guarantee of the
//! package, named after its statement, with the statement, its place and
//! its contract by responsibility as the documentation of the test. The
//! body of a test is the implementer's: it is written as `todo!()`, and the
//! test is ignored until it has one. An assumption and a permission are no
//! tests: what the environment does, and what is merely allowed, is told
//! in the documentation of the module.
//!
//! The conversion is shown by examples and proved by nothing; a test that
//! passes shows that one behaviour keeps a contract, not that every one does.

use serde::Deserialize;
use std::io::Read;
use std::path::PathBuf;
use trion_solver::Formula;

#[derive(Deserialize)]
struct Report {
    #[serde(default)]
    contracts: Vec<Contract>,
    #[serde(default)]
    control: Control,
}

#[derive(Deserialize, Default)]
struct Control {
    #[serde(default)]
    system: Vec<String>,
    #[serde(default)]
    environment: Vec<String>,
}

#[derive(Deserialize)]
struct Contract {
    statement: Statement,
    role: String,
    assume: Formula,
    guarantee: Formula,
}

#[derive(Deserialize)]
struct Statement {
    id: String,
    file: String,
    line: usize,
    text: String,
}

/// A Rust identifier for a statement identifier: `STORE-1` is `store_1`.
fn test_name(id: &str, taken: &mut std::collections::BTreeSet<String>) -> String {
    let mut name: String = id.chars().map(|c| if c.is_ascii_alphanumeric() { c.to_ascii_lowercase() } else { '_' }).collect();
    if name.is_empty() || name.starts_with(|c: char| c.is_ascii_digit()) {
        name.insert_str(0, "statement_");
    }
    let mut unique = name.clone();
    let mut n = 2;
    while !taken.insert(unique.clone()) {
        unique = format!("{name}_{n}");
        n += 1;
    }
    unique
}

/// The test code of a report.
fn render(report: &Report) -> String {
    let mut out = String::new();
    out.push_str("//! Tests of the contracts of a trion package, written by `trion --format rust-test`.\n//!\n");
    out.push_str(&format!("//! The system: {}.\n", if report.control.system.is_empty() { "(none declared)".to_string() } else { report.control.system.join(", ") }));
    out.push_str(&format!("//! The environment: {}.\n", if report.control.environment.is_empty() { "(none declared)".to_string() } else { report.control.environment.join(", ") }));
    let others: Vec<&Contract> = report.contracts.iter().filter(|c| c.role != "guarantee").collect();
    if !others.is_empty() {
        out.push_str("//!\n//! Not tested here: what the environment is assumed to do, and what is allowed or advised.\n");
        for contract in others {
            out.push_str(&format!("//! - [{}] ({}) {}\n", contract.statement.id, contract.role, contract.statement.text));
        }
    }
    out.push_str("\n#[cfg(test)]\nmod specification {\n");
    let mut taken = std::collections::BTreeSet::new();
    for contract in report.contracts.iter().filter(|c| c.role == "guarantee") {
        let statement = &contract.statement;
        out.push_str(&format!("    /// [{}] {}\n", statement.id, statement.text));
        out.push_str(&format!("    ///\n    /// {}:{}\n", statement.file, statement.line));
        out.push_str(&format!("    ///\n    /// A = {}\n    /// G = {}\n", contract.assume, contract.guarantee));
        out.push_str("    #[test]\n    #[ignore = \"the behaviour that keeps the contract is the implementer's to write\"]\n");
        out.push_str(&format!("    fn {}() {{\n        todo!(\"bring about A and observe G\")\n    }}\n\n", test_name(&statement.id, &mut taken)));
    }
    out.push_str("}\n");
    out
}

fn main() -> std::process::ExitCode {
    let Some(dir) = std::env::args_os().nth(1).map(PathBuf::from) else {
        eprintln!("usage: trion-format-rust-test DIR < report.json");
        return std::process::ExitCode::from(2);
    };
    let mut input = String::new();
    if let Err(e) = std::io::stdin().read_to_string(&mut input) {
        eprintln!("cannot read the report: {e}");
        return std::process::ExitCode::from(2);
    }
    let report: Report = match serde_json::from_str(&input) {
        Ok(report) => report,
        Err(e) => {
            eprintln!("the report is not a report of trion: {e}");
            return std::process::ExitCode::from(2);
        }
    };
    let path = dir.join("specification_tests.rs");
    if let Err(e) = std::fs::write(&path, render(&report)) {
        eprintln!("cannot write {}: {e}", path.display());
        return std::process::ExitCode::from(2);
    }
    println!("{}", path.display());
    std::process::ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn each_guarantee_is_one_ignored_test_documented_with_its_contract() {
        let report: Report = serde_json::from_str(r#"{
            "control": {"system": ["API"], "environment": ["user"]},
            "contracts": [
                {"statement": {"id": "STORE", "file": "a.trion", "line": 3, "text": "The API shall store the message."}, "role": "guarantee", "assume": "True",
                 "guarantee": {"And": [{"Atom": {"Act": {"key": "API|store message"}}}, {"Not": {"Atom": {"Forbid": {"key": "API|store message"}}}}]}},
                {"statement": {"id": "SEND", "file": "a.trion", "line": 4, "text": "A user sends a message."}, "role": "assumption", "assume": {"Atom": {"Event": {"key": "user send message"}}}, "guarantee": "True"}
            ]}"#).unwrap();
        let code = render(&report);
        assert!(code.contains("fn store()"), "{code}");
        assert!(code.contains("/// [STORE] The API shall store the message."), "{code}");
        assert!(code.contains("/// G = (Act(API|store message) ∧ ¬Forbid(API|store message))"), "{code}");
        // An assumption is told, and is no test.
        assert!(code.contains("//! - [SEND] (assumption) A user sends a message."), "{code}");
        assert!(!code.contains("fn send()"), "{code}");
    }
}
