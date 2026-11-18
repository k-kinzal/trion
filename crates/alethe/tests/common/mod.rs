//! Helpers shared by the integration tests: the cvc5 corpus and the tools.

#![allow(dead_code)]

use alethe::{read_output, Proof, SolverResponse};
use smtlib::command::{Command, Script};
use smtlib::response::CheckSatResponse;
use std::path::{Path, PathBuf};

/// The directory of the cvc5 corpus.
pub fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus")
}

/// The flags the corpus was produced with.
pub const CVC5_FLAGS: &[&str] = &["--incremental", "--dump-proofs", "--proof-format-mode=alethe"];

/// The ignore message of the tests that run cvc5.
pub const NEEDS_CVC5: &str = "needs cvc5 (cvc5 1.4.2) in .tools/bin or on PATH; run with --include-ignored";

/// The corpus entries whose proofs this crate rejects as unsupported, with
/// why.
pub const UNSUPPORTED: &[(&str, &str)] = &[("uf_define_fun", "cvc5 turns define-fun into an assume with lambda, which a ⟨proof_term⟩ (SMT-LIB 2.6) lacks")];

/// The stems of the corpus inputs, sorted.
pub fn corpus_stems() -> Vec<String> {
    let mut out: Vec<String> = std::fs::read_dir(corpus_dir())
        .expect("the corpus directory")
        .filter_map(|e| e.ok())
        .filter_map(|e| e.file_name().to_str().and_then(|n| n.strip_suffix(".smt2")).map(str::to_string))
        .collect();
    out.sort();
    out
}

/// The input script of a corpus entry.
pub fn input(stem: &str) -> String {
    std::fs::read_to_string(corpus_dir().join(format!("{stem}.smt2"))).expect("the corpus input")
}

/// The stored cvc5 output of a corpus entry.
pub fn output(stem: &str) -> String {
    std::fs::read_to_string(corpus_dir().join(format!("{stem}.cvc5.out"))).expect("the corpus output")
}

/// The input script of a corpus entry, read.
pub fn script(stem: &str) -> Script {
    Script::parse(&input(stem)).expect("the corpus input is SMT-LIB")
}

/// A proof with its problem: the script's prefix ending at the check
/// command the proof answers (§2.1: "the implicit problem constructed at
/// the invocation of a get-proof command").
#[derive(Debug, Clone)]
pub struct Pair {
    pub problem: Script,
    pub proof: Proof,
}

/// Each proof a solver printed for `script`, with its problem.
pub fn split(script: &Script, output: &str) -> alethe::Result<Vec<Pair>> {
    let checks: Vec<usize> = script.commands().iter().enumerate().filter(|(_, c)| matches!(c, Command::CheckSat | Command::CheckSatAssuming(_))).map(|(i, _)| i).collect();
    let mut answered = None;
    let mut answers = 0;
    let mut out = Vec::new();
    for (_, response) in read_output(output)? {
        match response {
            SolverResponse::CheckSat(answer) => {
                answered = Some((checks[answers], answer == CheckSatResponse::Unsat));
                answers += 1;
            }
            SolverResponse::Proof(commands) => {
                let (check, unsat) = answered.expect("a proof follows an answer");
                assert!(unsat, "a proof follows unsat");
                out.push(Pair { problem: Script::new(script.commands()[..=check].to_vec()), proof: commands.into_iter().map(|(_, c)| c).collect() });
            }
            _ => {}
        }
    }
    Ok(out)
}

/// The proofs of a corpus entry, with their problems.
pub fn pairs(stem: &str) -> alethe::Result<Vec<Pair>> {
    split(&script(stem), &output(stem))
}

/// The proof file of the problem file `problem`: `<problem>.alethe`, the
/// naming Carcara's README uses.
pub fn proof_path(problem: &Path) -> PathBuf {
    let mut name = problem.as_os_str().to_owned();
    name.push(".alethe");
    PathBuf::from(name)
}

/// Writes `<dir>/<name>.smt2` and its proof file; returns the problem file.
pub fn write(pair: &Pair, dir: &Path, name: &str) -> PathBuf {
    let problem = dir.join(format!("{name}.smt2"));
    std::fs::write(&problem, pair.problem.to_text(&smtlib::Dialect::strict())).expect("the problem file");
    std::fs::write(proof_path(&problem), pair.proof.to_text()).expect("the proof file");
    problem
}

/// The names of `count` pairs of one entry: `stem` alone for one,
/// `stem-1`, …, `stem-count` for several.
pub fn names(stem: &str, count: usize) -> Vec<String> {
    if count == 1 {
        vec![stem.to_string()]
    } else {
        (1..=count).map(|k| format!("{stem}-{k}")).collect()
    }
}

/// The supported corpus entries.
pub fn supported_stems() -> Vec<String> {
    corpus_stems().into_iter().filter(|s| !UNSUPPORTED.iter().any(|(u, _)| u == s)).collect()
}

/// A tool in `.tools/bin` of the workspace, or on PATH; a test that needs
/// a missing tool fails here, naming it.
pub fn tool(name: &str) -> PathBuf {
    let local = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.tools/bin").join(name);
    if local.is_file() {
        return local;
    }
    let on_path = std::env::var_os("PATH").and_then(|paths| std::env::split_paths(&paths).map(|dir| dir.join(name)).find(|p| p.is_file()));
    on_path.unwrap_or_else(|| panic!("{name} is needed by this test and is neither in .tools/bin nor on PATH"))
}

/// A fresh scratch directory under the target directory.
pub fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a scratch directory");
    dir
}
