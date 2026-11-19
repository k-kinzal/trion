//! Proves that trion manages trion: these tests run against the repository.

mod common;
use common::*;
use cargo_metadata::{CargoOpt, Metadata, MetadataCommand, Source};
use std::collections::HashSet;
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

fn cargo_workspace() -> &'static Metadata {
    static WORKSPACE: std::sync::OnceLock<Metadata> = std::sync::OnceLock::new();
    WORKSPACE.get_or_init(|| {
        MetadataCommand::new()
            .current_dir(repo_root())
            .features(CargoOpt::AllFeatures)
            .other_options(vec!["--locked".into()])
            .exec()
            .expect("Cargo should resolve the locked workspace")
    })
}

#[test]
fn the_core_has_no_language_or_backend_dependencies() {
    let workspace = cargo_workspace();
    let core = workspace
        .workspace_packages()
        .into_iter()
        .find(|package| package.name.as_str() == "trion-core")
        .expect("the workspace contains the Core");
    for dependency in &core.dependencies {
        assert!(
            ["serde", "serde_json", "sha2"].contains(&dependency.name.as_str())
                && dependency.source.as_ref().is_some_and(Source::is_crates_io),
            "unexpected Core dependency: {}",
            dependency.name
        );
    }

    let resolve = workspace.resolve.as_ref().expect("Cargo resolved the dependencies");
    let mut reached = HashSet::new();
    let mut pending = vec![&core.id];
    while let Some(id) = pending.pop() {
        for dependency in &resolve[id].deps {
            let package = &workspace[&dependency.pkg];
            assert!(
                package.source.as_ref().is_some_and(Source::is_crates_io),
                "Core transitively depends on {}",
                package.name
            );
            if reached.insert(&dependency.pkg) {
                pending.push(&dependency.pkg);
            }
        }
    }
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
    let packages = cargo_workspace().workspace_packages();
    let trion_packages = [
        "trion-solver", "trion-language", "trion-verification", "trion-checker",
        "trion-cli", "trioc-cli", "trion-lsp", "trion-format-rust-test",
        "trion-core", "trion-reference", "trion-cnl", "trion-boolean", "trion-analysis",
    ];
    let package = |name: &str| {
        packages.iter().copied().find(|pkg| pkg.name.as_str() == name)
            .unwrap_or_else(|| panic!("missing workspace package {name}"))
    };
    for name in trion_packages.iter().chain(&FORMATS) {
        assert!(package(name).manifest_path.ends_with(format!("crates/{name}/Cargo.toml")));
    }
    assert_eq!(packages.len(), trion_packages.len() + FORMATS.len());
    let dependencies = |name: &str| {
        package(name).dependencies.iter().map(|dep| dep.name.as_str())
    };

    // MoXI, Alethe and CPC use SMT-LIB, and CPC uses Eunoia.
    let allowed: [(&str, &[&str]); 6] = [
        ("smtlib", &[]), ("moxi", &["smtlib"]), ("alethe", &["smtlib"]),
        ("eunoia", &[]), ("cpc", &["smtlib", "eunoia"]), ("mmt", &[]),
    ];
    for (format, may) in allowed {
        for dependency in dependencies(format) {
            let in_workspace = trion_packages.contains(&dependency) || FORMATS.contains(&dependency);
            assert!(!in_workspace || may.contains(&dependency), "the format crate {format} depends on {dependency}");
            assert!(!dependency.starts_with("trion") && !dependency.starts_with("trioc"), "the format crate {format} depends on {dependency}");
        }
    }

    // The extension consumes the conversion report. The checker and trioc
    // stay independent of the packages whose answers they check.
    for (name, forbidden) in [
        ("trion-format-rust-test", &["trion-language", "trion-verification", "trion-cli", "trioc-cli", "trion-checker"][..]),
        ("trion-checker", &["trion-verification", "trion-cli", "trioc-cli"]),
        ("trion-verification", &["trion-checker"]),
        ("trion-language", &["trion-checker"]),
        ("trioc-cli", &["trion-cli", "trion-lsp"]),
    ] {
        for dependency in dependencies(name) {
            assert!(!forbidden.contains(&dependency), "{name} depends on {dependency}");
        }
    }
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
    for requirement in 1..=8 {
        let id = format!("F{requirement:02}");
        let present = loaded.root_specs().any(|spec| {
            spec.file == "spec/propositional/analysis.trion"
                && spec.display_id().split('/').next() == Some(id.as_str())
        });
        assert!(present, "the current specification is missing propositional requirement {id}");
    }
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
