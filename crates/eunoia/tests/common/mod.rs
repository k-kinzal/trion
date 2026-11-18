//! The inputs of the conformance tests, found at run time.
//!
//! The Ethos sources at commit 08e4aa40c4f8a6e00833f10e8d8985777e424027
//! (`user_manual.md`, `tests/`) are not part of the repository. They are
//! looked for in `$EUNOIA_ETHOS_SOURCES`, else in the repository's
//! `.tools/ethos-08e4aa40c4f8a6e00833f10e8d8985777e424027`. Ethos itself is
//! looked for in the repository's `.tools/bin`, then on `PATH`. Without them a
//! test that needs them prints what it needs and returns; with
//! `EUNOIA_REQUIRE_INPUTS=1` it fails instead. An Ethos of another version
//! always fails the test.

#![allow(dead_code)]

use std::path::{Path, PathBuf};

pub const ETHOS_COMMIT: &str = "08e4aa40c4f8a6e00833f10e8d8985777e424027";
pub const ETHOS_VERSION: &str = "0.2.5";

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn missing<T>(what: &str) -> Option<T> {
    let message = format!("needs {what}");
    if std::env::var_os("EUNOIA_REQUIRE_INPUTS").is_some_and(|v| v == "1") {
        panic!("{message}");
    }
    eprintln!("skipped: {message}");
    None
}

/// The Ethos sources, or `None` (after saying what is missing) when the test
/// is to be skipped.
pub fn ethos_sources() -> Option<PathBuf> {
    let dir = match std::env::var_os("EUNOIA_ETHOS_SOURCES") {
        Some(d) => PathBuf::from(d),
        None => repository().join(".tools").join(format!("ethos-{ETHOS_COMMIT}")),
    };
    if dir.join("user_manual.md").is_file() && dir.join("tests/CMakeLists.txt").is_file() {
        return Some(dir);
    }
    missing(&format!("the Ethos sources at commit {ETHOS_COMMIT} in {} (or $EUNOIA_ETHOS_SOURCES)", dir.display()))
}

/// The Ethos binary of the pinned version, or `None` when there is none.
pub fn ethos() -> Option<PathBuf> {
    let local = repository().join(".tools/bin/ethos");
    let found = if local.is_file() { Some(local) } else { std::env::var_os("PATH").and_then(|p| std::env::split_paths(&p).map(|d| d.join("ethos")).find(|p| p.is_file())) };
    let Some(tool) = found else { return missing(&format!("ethos {ETHOS_VERSION} (commit {ETHOS_COMMIT}) in .tools/bin or on PATH")) };
    let out = std::process::Command::new(&tool).arg("--show-config").output().unwrap_or_else(|e| panic!("run {}: {e}", tool.display()));
    let version = String::from_utf8_lossy(&out.stdout).lines().next().unwrap_or_default().to_string();
    assert!(version.contains(&format!("version {ETHOS_VERSION}")), "{} is not ethos {ETHOS_VERSION}: {version}", tool.display());
    Some(tool)
}
