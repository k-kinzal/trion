//! Proves that trion manages trion: these tests run against the repository.

mod common;
use common::*;
use std::fs;
use trion_cli::project;

fn repo(args: &[&str]) -> Result {
    verify_in(&repo_root(), args)
}

/// `trioc check` on the repository, run once for the tests of this file.
fn verified() -> &'static Result {
    static RUN: std::sync::OnceLock<Result> = std::sync::OnceLock::new();
    RUN.get_or_init(|| repo(&[]))
}

fn read(path: &str) -> String {
    fs::read_to_string(repo_root().join(path)).unwrap_or_else(|e| panic!("{path}: {e}"))
}

/// The packages that a manifest depends on, in any of its dependency
/// sections (`name = …`, `name.workspace = true`, `[dependencies.name]`).
fn dependencies(manifest: &str) -> Vec<String> {
    let mut names = Vec::new();
    let mut section = "";
    for line in manifest.lines().map(str::trim) {
        if let Some(header) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
            section = header;
            if let Some(name) = ["dependencies.", "dev-dependencies.", "build-dependencies."].iter().find_map(|p| header.strip_prefix(p)) {
                names.push(name.to_string());
            }
            continue;
        }
        if section.ends_with("dependencies") && !line.is_empty() && !line.starts_with('#') {
            let name = line.split(['=', '.']).next().unwrap_or("").trim();
            names.push(name.trim_matches('"').to_string());
        }
    }
    names
}

/// The format crates: each models one format of formal methods (its
/// grammar, reader and printer) and knows nothing of trion.
const FORMATS: [&str; 6] = ["smtlib", "moxi", "alethe", "eunoia", "cpc", "mmt"];

// The workspace holds the packages that produce a result, the package that
// checks apart from them, one package for each command, and the format
// crates: `trion` writes what `trioc` verifies, and `trion-lsp` serves
// editors with the light check of `trioc`. This test states which package
// may depend on which, so that neither the checker nor `trioc` can come to
// depend on what it checks, and no format crate can come to depend on trion.
#[test]
fn the_workspace_holds_its_packages_and_its_formats_and_what_checks_stands_apart() {
    let workspace = read("Cargo.toml");
    let trion_packages = ["trion-solver", "trion-language", "trion-verification", "trion-checker", "trion-cli", "trioc-cli", "trion-lsp", "trion-format-rust-test"];
    for package in trion_packages.iter().chain(&FORMATS) {
        assert!(workspace.contains(&format!("crates/{package}")), "{package}");
        assert!(read(&format!("crates/{package}/Cargo.toml")).contains(&format!("name = \"{package}\"")), "{package}");
    }
    // The workspace consists of these and of no other package.
    let members = fs::read_dir(repo_root().join("crates")).unwrap().flatten().filter(|entry| entry.path().join("Cargo.toml").is_file()).count();
    assert_eq!(members, trion_packages.len() + FORMATS.len());
    // A format crate depends on no trion crate, and on another format crate
    // only where one format is built on another: MoXI, Alethe and CPC on
    // SMT-LIB, CPC on Eunoia. trion's commands may depend on any of them.
    let allowed: [(&str, &[&str]); 6] = [("smtlib", &[]), ("moxi", &["smtlib"]), ("alethe", &["smtlib"]), ("eunoia", &[]), ("cpc", &["smtlib", "eunoia"]), ("mmt", &[])];
    for (format, may) in allowed {
        for dependency in dependencies(&read(&format!("crates/{format}/Cargo.toml"))) {
            let in_workspace = trion_packages.contains(&dependency.as_str()) || FORMATS.contains(&dependency.as_str());
            assert!(!in_workspace || may.contains(&dependency.as_str()), "the format crate {format} depends on {dependency}");
            assert!(!dependency.starts_with("trion") && !dependency.starts_with("trioc"), "the format crate {format} depends on {dependency}");
        }
    }
    // An extension format is a program outside the trion processor: it
    // reads the report of the conversion and depends on no part of trion
    // that reads or proves (spec/tool.trion).
    let extension = read("crates/trion-format-rust-test/Cargo.toml");
    assert!(["trion-language", "trion-verification", "trion-cli", "trioc-cli", "trion-checker"].iter().all(|p| !extension.contains(p)), "{extension}");
    // The checker reads the language and decides with the solver; it does
    // not depend on the verification, and the verification does not depend on it.
    let checker = read("crates/trion-checker/Cargo.toml");
    assert!(!checker.contains("trion-verification") && !checker.contains("trion-cli") && !checker.contains("trioc-cli"), "{checker}");
    assert!(!read("crates/trion-verification/Cargo.toml").contains("trion-checker"));
    assert!(!read("crates/trion-language/Cargo.toml").contains("trion-checker"));
    // `trioc` verifies what `trion` writes: it does not depend on `trion`.
    let trioc = read("crates/trioc-cli/Cargo.toml");
    assert!(!trioc.contains("trion-cli") && !trioc.contains("trion-lsp"), "{trioc}");
    // The checker of certificates shares no code with the search.
    let certificates = read("crates/trion-checker/src/certificate.rs");
    for word in ["decide", "Instance", "Prover", "trion_verification", "trion_language"] {
        assert!(!certificates.lines().filter(|l| !l.trim_start().starts_with("//")).any(|l| l.contains(word)), "the checker of certificates names `{word}`");
    }
    // The reference evaluator builds no formula and asks no solver.
    let evaluator = read("crates/trion-checker/src/eval.rs");
    for word in ["trion_solver", "Formula", "Atom::", "unroll", "compile("] {
        assert!(!evaluator.lines().filter(|l| !l.trim_start().starts_with("//")).any(|l| l.contains(word)), "the reference evaluator names `{word}`");
    }
}

#[test]
fn each_command_package_builds_its_command() {
    // `trion` and `trioc` are built by one package, so that each test of
    // one can run the other; the library of `trioc` builds no command.
    for (package, command) in [("trion-cli", "trion"), ("trion-cli", "trioc"), ("trion-lsp", "trion-lsp")] {
        let manifest = read(&format!("crates/{package}/Cargo.toml"));
        assert!(manifest.contains(&format!("[[bin]]\nname = \"{command}\"")), "{manifest}");
    }
    assert!(!read("crates/trioc-cli/Cargo.toml").contains("[[bin]]"));
    let help = convert_in(&repo_root(), &["--help"]);
    assert_eq!(help.code, 0);
    assert!(help.stdout.contains("Usage: trion [OPTIONS] [PATH]"), "{}", help.stdout);
}

#[test]
fn the_workspace_is_rust() {
    for root in ["crates/trion-solver/src/lib.rs", "crates/trion-language/src/lib.rs", "crates/trion-verification/src/lib.rs", "crates/trion-checker/src/lib.rs", "crates/trion-cli/src/main.rs", "crates/trion-cli/src/bin/trioc.rs", "crates/trioc-cli/src/lib.rs", "crates/trion-lsp/src/main.rs"] {
        assert!(repo_root().join(root).is_file(), "{root}");
    }
}

#[test]
fn the_syntax_layer_derives_from_spec_oracle() {
    let module = read("crates/trion-language/src/syntax/mod.rs");
    assert!(module.contains("so_lang"), "{module}");
    assert!(trion_language::syntax::parse("The pump shall stop.").is_ok());
}

/// The obligations that `trion` stated, and the verdict of each that `trioc` gave.
fn obligations(stdout: &str) -> (Vec<String>, Vec<(String, String)>) {
    let mut stated = Vec::new();
    let mut proved = Vec::new();
    for line in stdout.lines().filter_map(|line| line.strip_prefix("obligation ")) {
        let Some((name, rest)) = line.split_once(" (") else { continue };
        let Some((_, verdict)) = rest.split_once("): ") else { continue };
        if verdict.starts_with("not proved here") {
            stated.push(name.to_string());
        } else {
            proved.push((name.to_string(), verdict.split(':').next().unwrap_or(verdict).to_string()));
        }
    }
    (stated, proved)
}

#[test]
fn the_repository_passes_its_own_check_and_requirements() {
    // The specification of trion conforms to its language, and every obligation of its MMT form is proved.
    let result = verified();
    assert_eq!(result.code, 0, "{}{}", result.stdout, result.stderr);
    assert!(result.stdout.lines().any(|line| line == "converted"), "{}", result.stdout);
    let (stated, proved) = obligations(&result.stdout);
    assert!(stated.iter().any(|name| name == "consistency") && stated.iter().any(|name| name == "compatibility"), "{stated:?}");
    assert!(proved.iter().all(|(_, verdict)| verdict == "proved"), "{proved:?}");
    assert!(result.stdout.lines().any(|line| line.ends_with(" proved, 0 refuted, 0 unproved; no result holds beyond its bound")), "{}", result.stdout);
    assert!(result.stdout.trim_end().ends_with("\nproved"), "{}", result.stdout);
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
fn the_command_states_each_obligation_and_its_verdict() {
    let result = verified();
    // `trioc` gives one verdict for each obligation that `trion` wrote into the MMT form, in its order.
    let (stated, proved) = obligations(&result.stdout);
    assert!(!stated.is_empty());
    assert_eq!(stated, proved.iter().map(|(name, _)| name.clone()).collect::<Vec<_>>(), "{}", result.stdout);
    // The last line says whether every obligation is proved, and the exit code says the same.
    let last = result.stdout.lines().last().unwrap_or_default();
    assert_eq!(last == "proved", result.code == 0, "{last}");
}
