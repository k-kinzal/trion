//! Proves that trion manages trion: these tests run against the repository.

mod common;
use common::*;
use std::fs;
use trion_cli::project;

fn repo(args: &[&str]) -> Result {
    trion_in(&repo_root(), args)
}

/// `trion verify` on the repository, run once for the tests of this file.
fn verified() -> &'static Result {
    static RUN: std::sync::OnceLock<Result> = std::sync::OnceLock::new();
    RUN.get_or_init(|| repo(&["verify"]))
}

fn read(path: &str) -> String {
    fs::read_to_string(repo_root().join(path)).unwrap_or_else(|e| panic!("{path}: {e}"))
}

#[test]
fn the_workspace_holds_its_four_packages() {
    let workspace = read("Cargo.toml");
    for package in ["trion-solver", "trion-language", "trion-verification", "trion-cli"] {
        assert!(workspace.contains(&format!("crates/{package}")), "{package}");
        assert!(read(&format!("crates/{package}/Cargo.toml")).contains(&format!("name = \"{package}\"")), "{package}");
    }
    // The workspace consists of these and of no other package.
    let members = fs::read_dir(repo_root().join("crates")).unwrap().flatten().filter(|entry| entry.path().join("Cargo.toml").is_file()).count();
    assert_eq!(members, 4);
}

#[test]
fn the_cli_package_builds_the_trion_command() {
    let manifest = read("crates/trion-cli/Cargo.toml");
    assert!(manifest.contains("[[bin]]\nname = \"trion\""), "{manifest}");
    let help = repo(&["--help"]);
    assert_eq!(help.code, 0);
    assert!(help.stdout.contains("trion"), "{}", help.stdout);
}

#[test]
fn the_workspace_is_rust() {
    for root in ["crates/trion-solver/src/lib.rs", "crates/trion-language/src/lib.rs", "crates/trion-verification/src/lib.rs", "crates/trion-cli/src/main.rs"] {
        assert!(repo_root().join(root).is_file(), "{root}");
    }
}

#[test]
fn the_syntax_layer_derives_from_spec_oracle() {
    let module = read("crates/trion-language/src/syntax/mod.rs");
    assert!(module.contains("so_lang"), "{module}");
    assert!(trion_language::syntax::parse("The pump shall stop.").is_ok());
}

#[test]
fn the_repository_passes_its_own_check_and_requirements() {
    let result = verified();
    assert_eq!(result.code, 0, "{}{}", result.stdout, result.stderr);
    for gate in ["check", "sources", "prover", "properties", "stability"] {
        assert!(result.stdout.contains(&format!("gate {gate}: passed")), "{}", result.stdout);
    }
    assert!(result.stdout.trim_end().ends_with("\nverified"), "{}", result.stdout);
}

#[test]
fn the_packages_below_the_command_read_no_files() {
    let mut stack: Vec<_> = ["trion-solver", "trion-language", "trion-verification"].iter().map(|package| repo_root().join("crates").join(package).join("src")).collect();
    while let Some(dir) = stack.pop() {
        for entry in fs::read_dir(&dir).unwrap().flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "rs") {
                let text = fs::read_to_string(&path).unwrap();
                for forbidden in ["std::fs", "std::process", "File::open"] {
                    assert!(!text.contains(forbidden), "{} uses {forbidden}", path.display());
                }
            }
        }
    }
}

#[test]
fn the_specification_is_english() {
    let loaded = project::load(&repo_root()).unwrap();
    assert!(loaded.files.len() > 5);
    for spec in loaded.root_specs() {
        assert!(spec.sentence.source.is_ascii(), "{}: {}", spec.display_id(), spec.sentence.source);
    }
    // Outside the quotes of a source, every line is English.
    for path in loaded.files.values() {
        let text = fs::read_to_string(path).unwrap();
        let mut in_quote = false;
        for line in text.lines() {
            let opens = line.matches("\"\"\"").count() % 2 == 1;
            // A formula in an `expect` line of a reading example is literal data in the notation of the model.
            let quoted = in_quote || line.trim_start().starts_with("quote ") || line.trim_start().starts_with("expect \"");
            if !quoted {
                assert!(line.is_ascii(), "{}: {line}", path.display());
            }
            if opens {
                in_quote = !in_quote;
            }
        }
    }
}

#[test]
fn the_specification_holds_no_note_and_no_comment() {
    let loaded = project::load(&repo_root()).unwrap();
    for path in loaded.files.values() {
        let text = fs::read_to_string(path).unwrap();
        let mut in_quote = false;
        for (index, line) in text.lines().enumerate() {
            let quoted = in_quote;
            if line.matches("\"\"\"").count() % 2 == 1 {
                in_quote = !in_quote;
            }
            if quoted {
                continue;
            }
            let trimmed = line.trim_start();
            assert!(!trimmed.starts_with("note "), "{}:{}: {line}", path.display(), index + 1);
            assert!(!trimmed.starts_with("//"), "{}:{}: {line}", path.display(), index + 1);
        }
    }
}

#[test]
fn every_statement_of_the_specification_has_a_formal_reading() {
    let loaded = project::load(&repo_root()).unwrap();
    let analysis = trion_verification::analyze(&loaded.set, &trion_verification::Options::default());
    let modelled: std::collections::BTreeSet<&str> = analysis.model.constraints.iter().flat_map(|c| &c.refs).map(|r| r.id.as_str()).collect();
    let silent: Vec<String> = loaded
        .root_specs()
        .filter(|s| !matches!(s.sentence.core, trion_language::syntax::ast::Core::Definition { .. }))
        .map(|s| s.display_id())
        .filter(|id| !modelled.contains(id.as_str()))
        .collect();
    assert!(silent.is_empty(), "statements without a contract: {silent:?}");
}

#[test]
fn the_verify_command_states_the_completion_as_gates() {
    let result = verified();
    // Each condition of the completion is a gate with a state of its own.
    for gate in ["check", "sources", "prover", "properties", "stability"] {
        assert!(result.stdout.lines().any(|line| line.starts_with(&format!("gate {gate}: "))), "no state of the gate `{gate}`:\n{}", result.stdout);
    }
    // The last line says whether the package is verified, and the exit code says the same.
    let last = result.stdout.lines().last().unwrap_or_default();
    assert_eq!(last == "verified", result.code == 0, "{last}");
}
