//! Helpers shared by the integration tests.

#![allow(dead_code)]

use std::path::{Path, PathBuf};

use mmt::uri::{DPath, MPath};
use mmt::{Archive, Error, Library};

/// The directory of the crate.
pub fn crate_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// The directory `.tools` of the repository: `bin/java`, `mmt.jar` (MMT v27.0.0) and `urtheories` (commit 8bc91e38df43decdd55b1eda471c4d7b9c75dfdd).
pub fn tools() -> PathBuf {
    crate_dir().join("../../.tools")
}

/// A document URI for test sources.
pub fn base() -> DPath {
    "http://test.org/t/test.mmt".parse().unwrap()
}

/// A module URI.
pub fn mpath(s: &str) -> MPath {
    s.parse().unwrap()
}

/// A library with the stand-in for LF's notations (`tests/data/minilf.mmt`, written for these tests).
pub fn mini_lf() -> Library {
    let mut lib = Library::new();
    let path = crate_dir().join("tests/data/minilf.mmt");
    let base: DPath = "http://test.org/minilf.mmt".parse().unwrap();
    let e = lib.load_file(&path, &base);
    assert!(e.is_ok(), "{}", show(e.errors()));
    lib
}

/// A library with the real MMT/urtheories archive (only in ignored tests).
pub fn urtheories() -> (Library, Archive) {
    let a = Archive::open(tools().join("urtheories")).expect("needs MMT/urtheories (commit 8bc91e38df43decdd55b1eda471c4d7b9c75dfdd) in .tools/urtheories");
    let mut lib = Library::new();
    let load = lib.load_archives(std::slice::from_ref(&a));
    assert!(load.errors().is_empty() || !load.files().is_empty());
    (lib, a)
}

/// Adds a source to a library and returns its errors.
pub fn add(lib: &mut Library, text: &str) -> Vec<Error> {
    lib.add_source(text, &base(), Some(Path::new("test.mmt"))).into_errors()
}

/// Renders errors for assertion messages.
pub fn show(errors: &[Error]) -> String {
    errors.iter().map(ToString::to_string).collect::<Vec<_>>().join("\n")
}

/// The number of cases of a property test: `PROPTEST_CASES` if it is set
/// (a configuration given in the test would otherwise override it), else
/// the default of the test.
#[allow(dead_code)]
pub fn cases(default: u32) -> u32 {
    std::env::var("PROPTEST_CASES").ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}
