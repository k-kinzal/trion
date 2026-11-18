//! Differential tests against the reference tool, moxi-mc-flow (commit
//! `common::MCFLOW_COMMIT`), the implementation of MoXI by the authors of
//! the language, read from `.tools/moxi-mc-flow` or `MOXI_MC_FLOW` at test
//! time (GPLv3; none of its files is copied here). The tests are ignored by
//! default and run with `cargo test -- --include-ignored`; a run without
//! the tool fails.
//!
//! What the tool's verdict covers: its sort checker (driven as described at
//! `common::sortcheck`) parses a script and checks its static semantics.
//! This crate reads the grammar only, so the two verdicts are comparable
//! only on well-sorted input: an acceptance by the tool says the text is
//! grammatical (and the reader must read it), a rejection may be for a
//! rule the reader does not check. So:
//!
//! - where the tool accepts, the reader must read, except for the files
//!   listed in [`REJECTED_BY_THE_READER_ONLY`], each with the rule of
//!   description.md or SMT-LIB that the reader follows;
//! - where the tool rejects, the reader may read (a defect of the static
//!   semantics, left to the tool: [`LEFT_TO_THE_TOOL`]) or reject (a defect
//!   of the grammar both see);
//! - every script the reader reads prints to text that reads back equal,
//!   and where the tool accepts the original it accepts the printed form
//!   (the printer keeps the meaning the tool gives the text), except for
//!   the files listed in [`READ_DIFFERENTLY`], where the reader and the tool
//!   read the same text as different scripts. A run of the tool that
//!   reports any error counts as a rejection: its lexer reports an illegal
//!   character, skips it and may still accept.
//!
//! A disagreement not listed, or a listed one that no longer occurs, fails
//! the test.

mod common;

use std::str::FromStr;
use common::generate::{mutate, script, Mutation, MUTATIONS};
use moxi::{CheckSystemResponse, Script};
use std::path::{Path, PathBuf};

/// Corpus files the tool accepts and the reader rejects, with the reason.
const REJECTED_BY_THE_READER_ONLY: &[(&str, &str)] = &[
    ("Delay.moxi", "`:subsys` after `:inv`; \"Composite Systems\": every :subsys attribute occurs after :input, :output and :local but before :init, :trans and :inv"),
    ("QF_BV/Temporal.moxi", "`:init ( (and …) )`: a parenthesized term is not an SMT-LIB term (SMT-LIB §3.6, ⟨term⟩); \"the formulas I, T and P are SMT-LIB terms of type Bool\""),
    ("QF_BV/ThreeBitCounter.moxi", "`reset` is a variable name, but command names are reserved words (SMT-LIB §3.1); \"the system's identifier, input, output and local variables are SMT-LIB symbols\""),
    ("QF_BV/ThreeBitCounterBad.moxi", "`:trans ( (= …) )`: a parenthesized term, as in Temporal.moxi"),
    ("ThreeBitCounter.moxi", "a parenthesized term, as in Temporal.moxi"),
];

/// Corpus files both accept but read differently, with the reason: the
/// tool rejects the printed form, which says what the reader read.
const READ_DIFFERENTLY: &[(&str, &str)] = &[
    ("QF_BV/QuotedSymbols.moxi", "`|$out|'`: the tool reads the primed |$out|; SMT-LIB §3.1 ends a quoted symbol at its closing |, so the reader reads the symbol |$out| and then the symbol ' (the next-state copy of |$out| is |$out'|), and prints them apart, which the tool rejects"),
    ("QuotedInit.moxi", "`|x|'`, as above"),
];

/// Corpus files the reader reads and the tool rejects for a rule of the
/// static semantics, with the tool's reason.
const LEFT_TO_THE_TOOL: &[(&str, &str)] = &[
    ("Bad/DoubleDelayBadSubsys.moxi", "subsystem signature does not match target system (Delay)"),
    ("Bad/DoubleDelayBadVar.moxi", "variable 'in' not declared"),
];

fn corpus() -> (PathBuf, Vec<PathBuf>) {
    let root = common::mcflow().join("test/moxi");
    let mut stack = vec![root.clone()];
    let mut files = Vec::new();
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())) {
            let path = entry.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else {
                files.push(path);
            }
        }
    }
    files.sort();
    (root, files)
}

fn relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root).unwrap().to_string_lossy().replace('\\', "/")
}

// Every .moxi file of the corpus, as described in the module documentation.
#[test]
#[ignore = "needs moxi-mc-flow (commit b61c98188d246e157a6f5f759b012749855b8fbc) in .tools/moxi-mc-flow or MOXI_MC_FLOW; run with --include-ignored"]
fn corpus_agrees_with_sortcheck() {
    let (root, files) = corpus();
    let (mut rejected_by_us, mut read_differently, mut left_to_the_tool, mut count) = (Vec::new(), Vec::new(), Vec::new(), 0);
    for path in files.iter().filter(|p| p.extension().is_some_and(|e| e == "moxi")) {
        count += 1;
        let name = relative(&root, path);
        let text = std::fs::read_to_string(path).unwrap();
        let ours = Script::from_str(&text);
        let (reference, output) = common::sortcheck(path);
        match (&ours, reference) {
            (Ok(script), _) => {
                let printed = script.to_string();
                assert_eq!(Script::from_str(&printed).unwrap(), *script, "{name}");
                if reference {
                    let (accepted, output) = common::sortcheck_text(&printed, "printed");
                    if READ_DIFFERENTLY.iter().any(|(file, _)| *file == name) {
                        assert!(!accepted, "{name} is listed as read differently, but moxi-mc-flow accepts the printed form\n{printed}");
                        read_differently.push(name);
                    } else {
                        assert!(accepted, "{name}: moxi-mc-flow rejects the printed form\n{printed}\n{output}");
                    }
                } else {
                    let (_, reason) = LEFT_TO_THE_TOOL.iter().find(|(file, _)| *file == name).unwrap_or_else(|| panic!("{name}: read here, rejected by moxi-mc-flow, and not listed\n{output}"));
                    assert!(output.contains(reason), "{name}: moxi-mc-flow rejects for another reason than {reason:?}\n{output}");
                    left_to_the_tool.push(name);
                }
            }
            (Err(e), true) => {
                assert!(REJECTED_BY_THE_READER_ONLY.iter().any(|(file, _)| *file == name), "{name}: rejected here ({e}), accepted by moxi-mc-flow, and not listed");
                rejected_by_us.push(name);
            }
            (Err(_), false) => {}
        }
    }
    assert!(count >= 50, "only {count} corpus files under {}", root.display());
    for (file, _) in REJECTED_BY_THE_READER_ONLY {
        assert!(rejected_by_us.iter().any(|d| d == file), "{file} is listed as rejected by the reader only, but both now agree");
    }
    for (file, _) in READ_DIFFERENTLY {
        assert!(read_differently.iter().any(|d| d == file), "{file} is listed as read differently, but is not");
    }
    for (file, _) in LEFT_TO_THE_TOOL {
        assert!(left_to_the_tool.iter().any(|d| d == file), "{file} is listed as left to the tool, but both now agree");
    }
}

// The witness files of the corpus (`*.witness.expect`) are not in the
// format of "Check-system Response": they start with the system's name,
// have no `:verbosity`, a trace without `:lasso`, and trail states not
// enclosed in a list. The reader reads the format of the document and
// rejects them, at the system name.
#[test]
#[ignore = "needs moxi-mc-flow (commit b61c98188d246e157a6f5f759b012749855b8fbc) in .tools/moxi-mc-flow or MOXI_MC_FLOW; run with --include-ignored"]
fn corpus_witnesses_are_in_another_format() {
    let (root, files) = corpus();
    let witnesses: Vec<&PathBuf> = files.iter().filter(|p| p.to_string_lossy().ends_with(".witness.expect")).collect();
    assert!(!witnesses.is_empty());
    for path in witnesses {
        let text = std::fs::read_to_string(path).unwrap();
        for chunk in text.split("(check-system-response").skip(1) {
            let response = format!("(check-system-response{chunk}");
            let error = CheckSystemResponse::from_str(response.trim_end()).expect_err(&relative(&root, path));
            assert_eq!((error.position().unwrap().line(), error.position().unwrap().column()), (1, 24), "{}: {error}", relative(&root, path));
        }
    }
}

// Generated well-formed scripts (`common::generate`), read and printed by
// this crate, are accepted by moxi-mc-flow.
#[test]
#[ignore = "needs moxi-mc-flow (commit b61c98188d246e157a6f5f759b012749855b8fbc) in .tools/moxi-mc-flow or MOXI_MC_FLOW; run with --include-ignored"]
fn printed_scripts_are_accepted_by_sortcheck() {
    for seed in 0..64u64 {
        let generated = script(seed.wrapping_mul(7919).wrapping_add(17));
        let printed = Script::from_str(&generated.text).unwrap().to_string();
        let (accepted, output) = common::sortcheck_text(&printed, &format!("generated-{seed}"));
        assert!(accepted, "seed {seed}: moxi-mc-flow rejects\n{printed}\n{output}");
    }
}

// Generated scripts with one rule of the static semantics broken: the
// reader reads each of them (the rules are not grammar), and moxi-mc-flow
// rejects them, except for the rules it does not check, listed in
// `lenient`. Those defects are caught by neither: a program that must avoid
// them needs a check of its own.
#[test]
#[ignore = "needs moxi-mc-flow (commit b61c98188d246e157a6f5f759b012749855b8fbc) in .tools/moxi-mc-flow or MOXI_MC_FLOW; run with --include-ignored"]
fn static_semantics_is_left_to_sortcheck() {
    let lenient = |m: Mutation| matches!(m, Mutation::Redefinition | Mutation::IntFormula | Mutation::UndefinedLabel | Mutation::TheorySymbolVariable | Mutation::PrimedOutputInAssumption);
    let mut table = Vec::new();
    for (k, mutation) in MUTATIONS.iter().enumerate() {
        for seed in 0..3u64 {
            let text = mutate(&script(seed * 31 + k as u64), *mutation);
            let printed = Script::from_str(&text).unwrap_or_else(|e| panic!("{mutation:?}: {e}\n{text}")).to_string();
            let (accepted, output) = common::sortcheck_text(&printed, &format!("mutated-{k}-{seed}"));
            if accepted != lenient(*mutation) {
                table.push(format!("{mutation:?}: reference {}\n{}", if accepted { "accepts" } else { "rejects" }, output.lines().filter(|l| l.contains("ERROR")).collect::<Vec<_>>().join("\n")));
            }
        }
    }
    assert!(table.is_empty(), "{}", table.join("\n"));
}
