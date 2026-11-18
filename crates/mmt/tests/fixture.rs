//! A real workload: the MMT form of trion's own specification, as `trion`
//! writes it (`tests/data/specification`, an archive with
//! `META-INF/MANIFEST.MF` and `source/specification.mmt`, 1.2 MB). It is read,
//! printed back so that it reads as the same theories, and both take
//! bounded time. MMT v27.0.0 accepts this archive over MMT/urtheories
//! (`crates/trion-cli/tests/mmt_form.rs` runs MMT on the forms that trion
//! writes); this crate only reads it.
//!
//! The tests run over the stand-in for LF (`tests/data/minilf.mmt`); the
//! tests marked as needing `.tools/urtheories` repeat them over the real
//! archive.

mod common;

use std::time::{Duration, Instant};

use common::*;
use mmt::uri::MPath;
use mmt::{Archive, Declaration, Document, Library};

fn archive() -> Archive {
    Archive::open(crate_dir().join("tests/data/specification")).unwrap()
}

fn source() -> String {
    std::fs::read_to_string(crate_dir().join("tests/data/specification/source/specification.mmt")).unwrap()
}

fn contracts() -> MPath {
    mpath("http://trion.dev/meta?Contracts")
}

fn trion() -> MPath {
    mpath("http://trion.dev/form/trion?trion")
}

fn count_constants(lib: &Library, p: &MPath) -> usize {
    lib.theory(p).unwrap().declarations().iter().filter(|d| matches!(d, Declaration::Constant(_))).count()
}

#[test]
fn fixture_manifest_and_structure() {
    let a = archive();
    assert_eq!(a.id(), "trion/trion");
    assert_eq!(a.manifest().dependencies(), ["MMT/urtheories"]);
    assert_eq!(a.source_files().unwrap(), vec![vec!["specification.mmt".to_string()]]);
    // the structural syntax reads and prints back to the same document
    let doc = Document::parse(&source()).unwrap();
    assert_eq!(Document::parse(&doc.to_string()).unwrap(), doc);
}

/// Reads the archive, prints the theories, reads the printed document into a fresh library and compares.
fn reads_and_prints_back(mut lib: Library, mut fresh: Library) {
    let start = Instant::now();
    let load = lib.load_archives(&[archive()]);
    let read = start.elapsed();
    assert!(load.errors().is_empty(), "{}", show(load.errors()));
    assert_eq!(load.missing_dependencies(), [("trion/trion".to_string(), "MMT/urtheories".to_string())]);
    assert!(count_constants(&lib, &contracts()) > 90);
    assert!(count_constants(&lib, &trion()) > 2000);
    let start = Instant::now();
    let printed = lib.print_theories(&[contracts(), trion()]).unwrap();
    let print = start.elapsed();
    let e = fresh.add_source(&printed, &"http://test.org/printed.mmt".parse().unwrap(), Some("printed.mmt".as_ref()));
    assert!(e.is_ok(), "{}", show(e.errors()));
    for p in [contracts(), trion()] {
        assert_eq!(lib.theory(&p), fresh.theory(&p), "{p}");
    }
    // printing is deterministic and a fixed point after one round
    assert_eq!(fresh.print_theories(&[contracts(), trion()]).unwrap(), printed);
    // generous bounds for an unoptimized build: reading and printing are near linear
    eprintln!("read {read:?}, printed {print:?}");
    assert!(read < Duration::from_secs(30) && print < Duration::from_secs(30), "read {read:?}, printed {print:?}");
}

#[test]
fn fixture_reads_and_prints_back_over_mini_lf() {
    reads_and_prints_back(mini_lf(), mini_lf());
}

#[test]
#[ignore = "needs MMT/urtheories (commit 8bc91e38df43decdd55b1eda471c4d7b9c75dfdd) in .tools/urtheories"]
fn fixture_reads_and_prints_back_over_urtheories() {
    reads_and_prints_back(urtheories().0, urtheories().0);
}
