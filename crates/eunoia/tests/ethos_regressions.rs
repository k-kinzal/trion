//! The regression tests of Ethos (`tests/` at commit
//! 08e4aa40c4f8a6e00833f10e8d8985777e424027, read from the Ethos sources,
//! which are not part of the repository; see `common`).
//!
//! `tests/CMakeLists.txt` lists the files that Ethos must accept
//! (`ethos_test_file_list`) and those it must refuse with a given message
//! (`ethos_fail_test`).
//!
//! - Every listed file parses and prints back to an equal script, except three
//!   files that Ethos refuses while reading, which are refused here too.
//! - Differential, with Ethos 0.2.5 itself: every `.eo` file of the directory
//!   is replaced by its printed form, and Ethos run on every listed file gives
//!   the same verdict and the same output (positions masked, since the layout
//!   changes) as on the original. Ethos's verdict covers parsing, type
//!   checking and the checking of proofs: printing changes none of them.

mod common;

use std::path::{Path, PathBuf};
use std::process::Command as Process;

use eunoia::{parse_script, ParseErrorKind};

fn cmake(data: &Path) -> String {
    std::fs::read_to_string(data.join("CMakeLists.txt")).unwrap()
}

/// The files of `set(ethos_test_file_list ...)`.
fn accepted(data: &Path) -> Vec<String> {
    let text = cmake(data);
    let start = text.find("set(ethos_test_file_list").unwrap();
    let end = start + text[start..].find(')').unwrap();
    text[start..end].split_whitespace().skip(1).map(str::to_string).collect()
}

/// The files and expected messages of `ethos_fail_test(file "regex")`.
fn refused(data: &Path) -> Vec<(String, String)> {
    let text = cmake(data);
    let mut out = Vec::new();
    for chunk in text.split("ethos_fail_test(").skip(2) {
        let mut parts = chunk.splitn(2, char::is_whitespace);
        let file = parts.next().unwrap().to_string();
        let rest = parts.next().unwrap();
        let msg = rest.split('"').nth(1).unwrap().to_string();
        out.push((file, msg));
    }
    out
}

fn data() -> Option<PathBuf> {
    common::ethos_sources().map(|d| d.join("tests"))
}

/// The files that Ethos refuses while reading, with the reason this crate gives.
const UNREADABLE: [&str; 3] = ["parser-overflow-declare-sort.eo", "nullary-arrow-type.eo", "apply-no-operator.eo"];

#[test]
fn the_lists_are_read() {
    let Some(data) = data() else { return };
    assert!(accepted(&data).len() > 180, "{}", accepted(&data).len());
    assert_eq!(refused(&data).len(), 22);
}

#[test]
fn every_listed_file_parses_and_round_trips() {
    let Some(data) = data() else { return };
    let mut files = accepted(&data);
    files.extend(refused(&data).into_iter().map(|(f, _)| f));
    for file in files {
        let text = std::fs::read_to_string(data.join(&file)).unwrap();
        match parse_script(&text) {
            Ok(script) => {
                assert!(!UNREADABLE.contains(&file.as_str()), "{file} is refused by Ethos while reading");
                let printed = script.to_string();
                let again = parse_script(&printed).unwrap_or_else(|e| panic!("{file}: printed text does not parse: {e}\n{printed}"));
                assert_eq!(script, again, "{file}");
            }
            Err(e) => {
                assert!(UNREADABLE.contains(&file.as_str()), "{file}: {e}");
                assert!(matches!(e.kind, ParseErrorKind::InvalidLiteral(_) | ParseErrorKind::Syntax(_)), "{file}: {e}");
            }
        }
    }
}

/// Copies `from` to `to`, replacing every `.eo` file that parses by its printed form.
fn copy_printed(from: &Path, to: &Path) -> usize {
    let mut printed = 0;
    std::fs::create_dir_all(to).unwrap();
    for entry in std::fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let (src, dst) = (entry.path(), to.join(entry.file_name()));
        if entry.file_type().unwrap().is_dir() {
            printed += copy_printed(&src, &dst);
        } else if src.extension().is_some_and(|e| e == "eo") {
            let text = std::fs::read_to_string(&src).unwrap();
            match parse_script(&text) {
                Ok(script) => {
                    std::fs::write(&dst, script.to_string()).unwrap();
                    printed += 1;
                }
                Err(_) => std::fs::write(&dst, text).unwrap(),
            }
        } else {
            std::fs::copy(&src, &dst).unwrap();
        }
    }
    printed
}

/// Ethos's verdict and output on `file` in `dir`, with the directory and
/// the positions (`:line.column:`) masked.
fn ethos(ethos: &Path, dir: &Path, file: &str) -> (bool, String) {
    let out = Process::new(ethos).arg(dir.join(file)).current_dir(dir).output().expect("run ethos");
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr)).replace(&dir.display().to_string(), "<dir>");
    let mut masked = String::new();
    let mut rest = text.as_str();
    // `:<digits>.<digits>:` becomes `:L.C:`
    while let Some(i) = rest.find(':') {
        masked.push_str(&rest[..=i]);
        rest = &rest[i + 1..];
        let digits = |s: &str| s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
        let a = digits(rest);
        if a > 0 && rest[a..].starts_with('.') {
            let b = digits(&rest[a + 1..]);
            if b > 0 && rest[a + 1 + b..].starts_with(':') {
                masked.push_str("L.C");
                rest = &rest[a + 1 + b..];
            }
        }
    }
    masked.push_str(rest);
    (out.status.success(), masked)
}

#[test]
fn ethos_gives_the_same_verdict_on_the_printed_files() {
    let (Some(data), Some(tool)) = (data(), common::ethos()) else { return };
    let copy = std::env::temp_dir().join(format!("eunoia-ethos-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&copy);
    let printed = copy_printed(&data, &copy);
    let (data, copy) = (data.canonicalize().unwrap(), copy.canonicalize().unwrap());
    assert!(printed > 200, "{printed}");
    let mut files: Vec<(String, Option<String>)> = accepted(&data).into_iter().map(|f| (f, None)).collect();
    files.extend(refused(&data).into_iter().map(|(f, m)| (f, Some(m))));
    let mut differences = Vec::new();
    for (file, refusal) in &files {
        let original = ethos(&tool, &data, file);
        let ours = ethos(&tool, &copy, file);
        assert_eq!(original.0, refusal.is_none(), "{file}: Ethos on the original: {}", original.1);
        if original != ours {
            differences.push(format!("{file}:\n  original: {:?}\n  printed:  {:?}", original, ours));
        }
    }
    std::fs::remove_dir_all(&copy).unwrap();
    assert!(differences.is_empty(), "{} difference(s):\n{}", differences.len(), differences.join("\n"));
}
