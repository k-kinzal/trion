//! Archives on disk: sources below `source`, a cycle of symbolic links that
//! ends, and errors attributed to the file they occur in.

mod common;

use std::path::PathBuf;

use common::*;
use mmt::{Archive, ErrorKind, Library};

/// A fresh directory for one test.
fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("mmt-archives-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("META-INF")).unwrap();
    std::fs::create_dir_all(dir.join("source/sub")).unwrap();
    std::fs::write(dir.join("META-INF/MANIFEST.MF"), "id: test/a\nnarration-base: http://test.org/a\n").unwrap();
    dir
}

#[test]
fn sources_are_listed_once_and_errors_name_their_file() {
    let dir = scratch("files");
    std::fs::write(dir.join("source/a.mmt"), "namespace http://test.org/a❚ theory A = c❙ ❚").unwrap();
    std::fs::write(dir.join("source/sub/b.mmt"), "namespace http://test.org/a❚ theory B =\n  include ?A❙\n  d = nothing❙\n❚").unwrap();
    std::fs::write(dir.join("source/sub/notes.txt"), "not a source").unwrap();
    let a = Archive::open(&dir).unwrap();
    assert_eq!(a.source_files().unwrap(), vec![vec!["a.mmt".to_string()], vec!["sub".to_string(), "b.mmt".to_string()]]);
    assert_eq!(a.document_uri(&["sub".to_string(), "b.mmt".to_string()]).unwrap().to_string(), "http://test.org/a/sub/b.mmt");
    let mut lib = Library::new();
    let load = lib.load_archives(std::slice::from_ref(&a));
    assert_eq!(load.errors().len(), 1, "{}", show(load.errors()));
    let e = &load.errors()[0];
    assert_eq!(e.kind(), ErrorKind::Unresolved);
    assert_eq!(e.file(), Some(dir.join("source/sub/b.mmt").as_path()));
    assert_eq!(e.pos().map(|p| (p.line(), p.column())), Some((3, 7)));
    assert!(lib.theory(&mpath("http://test.org/a?A")).is_some());
    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(unix)]
#[test]
fn a_cycle_of_symbolic_links_ends() {
    let dir = scratch("links");
    std::fs::write(dir.join("source/sub/b.mmt"), "namespace http://test.org/a❚ theory B = c❙ ❚").unwrap();
    std::os::unix::fs::symlink(dir.join("source"), dir.join("source/sub/back")).unwrap();
    let a = Archive::open(&dir).unwrap();
    assert_eq!(a.source_files().unwrap(), vec![vec!["sub".to_string(), "b.mmt".to_string()]]);
    let _ = std::fs::remove_dir_all(&dir);
}
