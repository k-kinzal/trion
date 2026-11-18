//! Every diagnostic code can be reported: for each code that trion lists,
//! `fixtures/codes/<CODE>` holds a package with a seeded defect and the
//! arguments of the command that reports the code.

mod common;
use common::*;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

/// The codes that no fixture reaches through the command. A defect of the
/// solver, of the writer or of the reader cannot be written into a package:
/// the fixture of such a code names a seeded fault in its `ENV` file, which
/// the command reads from `TRION_FAULT`.
const WITHOUT_FIXTURE: &[(&str, &str)] = &[
    // The language server reports this where `trioc prove` cannot run the
    // proof of a package that conforms; no package seeds it.
    ("prover-failed", "the proof of the language server could not run"),
];

fn fixtures() -> std::path::PathBuf {
    repo_root().join("crates/trion-cli/fixtures/codes")
}

fn copy_tree(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap().flatten() {
        let (path, target) = (entry.path(), to.join(entry.file_name()));
        if path.is_dir() {
            copy_tree(&path, &target);
        } else {
            fs::copy(&path, &target).unwrap();
        }
    }
}

fn codes() -> BTreeSet<String> {
    trion_language::CODES.iter().map(|code| code.to_string()).collect()
}

#[test]
fn the_language_lists_every_diagnostic_code() {
    let codes = codes();
    assert_eq!(codes.len(), trion_language::CODES.len(), "a code is listed twice");
    // Every code that a source names in a diagnostic is listed. A code that
    // is passed on in a variable is caught where it is reported: a debug
    // build stops on a diagnostic whose code is not listed.
    let mut stack: Vec<_> = ["trion-solver", "trion-language", "trion-verification", "trion-cli"].iter().map(|package| repo_root().join("crates").join(package).join("src")).collect();
    while let Some(dir) = stack.pop() {
        for entry in fs::read_dir(dir).unwrap().flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
                continue;
            }
            let text = fs::read_to_string(&path).unwrap();
            for constructor in ["Diagnostic::error(\"", "Diagnostic::warning(\"", "Diagnostic::info(\""] {
                for (at, _) in text.match_indices(constructor) {
                    let rest = &text[at + constructor.len()..];
                    let code = &rest[..rest.find('"').unwrap()];
                    assert!(codes.contains(code), "{}: the code `{code}` is not listed", path.display());
                }
            }
        }
    }
}

#[test]
fn each_diagnostic_code_has_a_fixture_with_a_seeded_defect_that_reports_it() {
    let codes = codes();
    let exempt: BTreeSet<&str> = WITHOUT_FIXTURE.iter().map(|(code, _)| *code).collect();
    let present: BTreeSet<String> = fs::read_dir(fixtures()).unwrap().flatten().map(|e| e.file_name().to_string_lossy().into_owned()).collect();
    for code in &codes {
        assert!(present.contains(code) != exempt.contains(code.as_str()), "the diagnostic code `{code}` has no fixture, or has one and is still listed as without");
    }
    for name in &present {
        assert!(codes.contains(name), "the fixture `{name}` is for a code that trion does not report");
    }
    let mut silent = Vec::new();
    for code in present {
        let dir = fixtures().join(&code);
        let work = tempfile::tempdir().unwrap();
        copy_tree(&dir.join("package"), work.path());
        let arguments = fs::read_to_string(dir.join("ARGS")).unwrap();
        let arguments: Vec<&str> = arguments.lines().collect();
        // `ENV` holds `NAME=VALUE` lines: the seeded fault of the run.
        let environment = fs::read_to_string(dir.join("ENV")).unwrap_or_default();
        let variables: Vec<(&str, &str)> = environment.lines().filter_map(|line| line.split_once('=')).collect();
        let result = verify_with(work.path(), &arguments, &variables);
        let reported = result.stdout.contains(&format!("\"code\": \"{code}\"")) || result.stdout.contains(&format!("[{code}]"));
        if !reported {
            silent.push(format!("the fixture of `{code}` does not report it:\n{}{}", result.stdout.lines().filter(|l| l.contains("\"code\"") || l.starts_with("error") || l.starts_with("warning")).collect::<Vec<_>>().join("\n"), result.stderr));
        }
    }
    assert!(silent.is_empty(), "{} fixtures report nothing:\n{}", silent.len(), silent.join("\n"));
}
