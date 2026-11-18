//! The inputs of the tests, found at run time, and the stored corpus.
//!
//! Tools are looked for in the repository's `.tools/bin`, then on `PATH`; the
//! signature in `$CPC_SIGNATURE_DIR`, else in the repository's
//! `.tools/cvc5-signature`. A test whose input is missing prints what it needs
//! and returns; with `CPC_REQUIRE_TOOLS=1` it fails instead. A tool of another
//! version than the pinned one always fails the test.

#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

use cpc::{ProofDocument, SessionOptions, Variant};

/// cvc5, whose CPC output the stored corpus is.
pub const CVC5_VERSION: &str = "1.4.2";
/// Ethos, the version that cvc5 1.4.2 pins in `contrib/get-ethos-checker`.
pub const ETHOS_VERSION: &str = "0.2.5";
pub const ETHOS_COMMIT: &str = "08e4aa40c4f8a6e00833f10e8d8985777e424027";

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Says that `what` is missing: `None` (skip), or a failure under `CPC_REQUIRE_TOOLS=1`.
fn missing<T>(what: &str) -> Option<T> {
    let message = format!("needs {what}");
    if std::env::var_os("CPC_REQUIRE_TOOLS").is_some_and(|v| v == "1") {
        panic!("{message}");
    }
    eprintln!("skipped: {message}");
    None
}

fn locate(tool: &str) -> Option<PathBuf> {
    let local = repository().join(".tools/bin").join(tool);
    if local.is_file() {
        return Some(local);
    }
    std::env::var_os("PATH").and_then(|paths| std::env::split_paths(&paths).map(|d| d.join(tool)).find(|p| p.is_file()))
}

fn first_line(tool: &Path, arg: &str) -> String {
    let out = Command::new(tool).arg(arg).output().unwrap_or_else(|e| panic!("run {}: {e}", tool.display()));
    String::from_utf8_lossy(&out.stdout).lines().next().unwrap_or_default().to_string()
}

/// cvc5 1.4.2, or `None` when there is no cvc5. A cvc5 of another version fails.
pub fn cvc5() -> Option<PathBuf> {
    let Some(tool) = locate("cvc5") else { return missing(&format!("cvc5 {CVC5_VERSION} in .tools/bin or on PATH")) };
    let version = first_line(&tool, "--version");
    assert!(version.starts_with(&format!("cvc5 {CVC5_VERSION} ")), "{} is not cvc5 {CVC5_VERSION}: {version}", tool.display());
    Some(tool)
}

/// Ethos 0.2.5, or `None` when there is no Ethos. An Ethos of another version fails.
pub fn ethos() -> Option<PathBuf> {
    let Some(tool) = locate("ethos") else { return missing(&format!("ethos {ETHOS_VERSION} (commit {ETHOS_COMMIT}) in .tools/bin or on PATH")) };
    let version = first_line(&tool, "--show-config");
    assert!(version.contains(&format!("version {ETHOS_VERSION}")), "{} is not ethos {ETHOS_VERSION}: {version}", tool.display());
    Some(tool)
}

/// The official CPC signature of cvc5 1.4.2 (`proofs/eo/cpc` of the tag
/// `cvc5-1.4.2`), or `None` when it is not there.
pub fn signature_dir() -> Option<PathBuf> {
    let dir = std::env::var_os("CPC_SIGNATURE_DIR").map(PathBuf::from).unwrap_or_else(|| repository().join(".tools/cvc5-signature"));
    if dir.join("Cpc.eo").is_file() && dir.join("expert/CpcExpert.eo").is_file() {
        return Some(dir.canonicalize().unwrap());
    }
    missing(&format!("proofs/eo/cpc of cvc5 tag cvc5-1.4.2 in {} (or $CPC_SIGNATURE_DIR)", dir.display()))
}

pub fn data() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data")
}

/// The stems of the stored problems.
pub fn problems() -> Vec<String> {
    let mut out: Vec<String> = std::fs::read_dir(data()).unwrap().filter_map(|e| e.unwrap().file_name().to_str().and_then(|n| n.strip_suffix(".smt2")).map(str::to_string)).collect();
    out.sort();
    out
}

pub fn read(stem: &str, suffix: &str) -> String {
    std::fs::read_to_string(data().join(format!("{stem}.{suffix}"))).unwrap()
}

/// The commands of a stored problem, read by `smtlib`.
pub fn commands(stem: &str) -> Vec<smtlib::Command> {
    smtlib::Script::parse(&read(stem, "smt2")).unwrap_or_else(|e| panic!("{stem}.smt2: {e}")).into_commands()
}

/// The cvc5 runs that produce the stored outputs: suffix, options of cvc5,
/// and how the reader is told about them.
pub fn runs(stem: &str) -> Vec<(&'static str, Vec<&'static str>, SessionOptions)> {
    if stem == "incremental" {
        vec![("cvc5.out", vec!["--incremental", "--proof-format-mode=cpc"], SessionOptions::new())]
    } else {
        let dump = SessionOptions::new().with_dump_proofs(true);
        vec![("cvc5.out", vec!["--dump-proofs", "--proof-format-mode=cpc"], dump), ("cvc5-ref.out", vec!["--dump-proofs", "--proof-format-mode=cpc", "--proof-print-reference"], dump)]
    }
}

pub fn options(stem: &str, suffix: &str) -> SessionOptions {
    runs(stem).into_iter().find(|(s, _, _)| *s == suffix).map(|(_, _, o)| o).unwrap()
}

/// The documents of a stored output.
pub fn documents_of(stem: &str, suffix: &str, dir: &str, variant: Variant) -> Vec<ProofDocument> {
    ProofDocument::from_cvc5_output(&read(stem, suffix), &commands(stem), options(stem, suffix), dir, variant).unwrap_or_else(|e| panic!("{stem}.{suffix}: {e}"))
}

/// The documents of `<stem>.cvc5.out`, including the signature from `/cpc`.
pub fn documents(stem: &str) -> Vec<ProofDocument> {
    documents_of(stem, "cvc5.out", "/cpc", Variant::Expert)
}
