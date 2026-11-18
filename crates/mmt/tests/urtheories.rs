//! The archive MMT/urtheories (`.tools/urtheories`, commit
//! 8bc91e38df43decdd55b1eda471c4d7b9c75dfdd; not part of this repository):
//! which theories this crate reads, which it rejects because they use
//! features outside the supported subset, and that what it reads prints back
//! to the same theories. Run with `--ignored --nocapture` to see the report.

mod common;

use common::*;
use mmt::uri::MPath;
use mmt::{ErrorKind, Library};

/// The features outside the supported subset that make the other theories rejected.
const UNSUPPORTED: &[&str] = &["fixity declarations", "TermLiteralRule", "InformalLiterals", "views", "structures", "derived", "realize", "implicit", "patterns", "parameters", "defined theories", "ambiguous"];

#[test]
#[ignore = "needs MMT/urtheories (commit 8bc91e38df43decdd55b1eda471c4d7b9c75dfdd) in .tools/urtheories"]
fn urtheories_report() {
    let (lib, a) = urtheories();
    let mut again = Library::new();
    let load = again.load_archives(std::slice::from_ref(&a));
    println!("archive {} ({} files)", a.id(), load.files().len());
    for (f, ts) in load.files() {
        println!("  {}: {}", f.file_name().unwrap().to_string_lossy(), ts.iter().map(ToString::to_string).collect::<Vec<_>>().join(", "));
    }
    for (a, d) in load.missing_dependencies() {
        println!("  dependency of {a} not given: {d}");
    }
    for e in load.errors() {
        println!("  rejected: {e}");
        match e.kind() {
            ErrorKind::Unsupported => assert!(UNSUPPORTED.iter().any(|r| e.to_string().contains(r)), "{e}"),
            // theories that depend on a rejected theory or refer to a theory outside the archive
            ErrorKind::Unresolved => {}
            _ => panic!("unexpected error {e}"),
        }
    }
    let read: Vec<String> = lib.theories().map(|t| t.path().to_string()).collect();
    println!("read {} theories: {}", read.len(), read.join(", "));
    for needed in ["http://cds.omdoc.org/urtheories?LF", "http://cds.omdoc.org/mmt?mmt", "http://cds.omdoc.org/urtheories?Strings"] {
        assert!(read.iter().any(|r| r == needed), "{needed}");
    }
}

#[test]
#[ignore = "needs MMT/urtheories (commit 8bc91e38df43decdd55b1eda471c4d7b9c75dfdd) in .tools/urtheories"]
fn urtheories_print_back_to_the_same_theories() {
    let (lib, _) = urtheories();
    let roots: Vec<MPath> = lib.theories().filter(|t| t.parent().is_none()).map(|t| t.path().clone()).collect();
    let printed = lib.print_theories(&roots).unwrap();
    let mut fresh = Library::new();
    let e = fresh.add_source(&printed, &"http://test.org/printed.mmt".parse().unwrap(), Some("printed.mmt".as_ref()));
    assert!(e.is_ok(), "{}", show(e.errors()));
    for t in lib.theories() {
        assert_eq!(Some(t), fresh.theory(t.path()), "{}", t.path());
    }
}
