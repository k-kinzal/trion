//! The formats that `trion` writes: its own (MMT, Markdown, HTML) and the
//! extension formats that a program outside the trion processor adds
//! (spec/tool.trion). An extension format reads the JSON report of the
//! conversion and writes into the directory of `--out`; code is written so.

mod common;
use common::*;
use std::os::unix::fs::PermissionsExt;
use std::process::Command;

/// A directory that holds the program of the extension format `demo`: it
/// keeps the report that it reads, as a format that writes code would read
/// it, and prints the file that it wrote.
fn extension() -> tempfile::TempDir {
    let bin = tempfile::tempdir().unwrap();
    let program = bin.path().join("trion-format-demo");
    std::fs::write(&program, "#!/bin/sh\ncat > \"$1/demo.json\"\necho \"$1/demo.json\"\n").unwrap();
    std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o755)).unwrap();
    bin
}

#[test]
fn an_extension_format_is_written_by_its_program_from_the_report_of_the_conversion() {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "system API\nprimitive API, message\n[STORE] The API shall store the message.\n")]);
    let bin = extension();
    let out = tempfile::tempdir().unwrap();
    let path = format!("{}:{}", bin.path().display(), tools_path());
    let run = Command::new(env!("CARGO_BIN_EXE_trion")).env("PATH", &path).args(["--out", &out.path().to_string_lossy(), "--format", "demo", "--format", "markdown"]).current_dir(f.path()).output().unwrap();
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(run.status.success(), "{stdout}{}", String::from_utf8_lossy(&run.stderr));
    // The program read the report: the contract of each statement by
    // responsibility and the obligations that `trioc` proves.
    let read: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(out.path().join("demo.json")).unwrap()).unwrap();
    let contract = read["contracts"].as_array().unwrap().iter().find(|c| c["statement"]["id"] == "STORE").unwrap();
    assert_eq!(contract["role"], "guarantee");
    assert_eq!(read["control"]["system"][0], "API");
    assert!(read["obligations"].as_array().unwrap().iter().any(|o| o["property"] == "consistency"));
    // What it wrote is reported as written, beside the formats of trion.
    assert!(stdout.contains("demo.json") && stdout.contains("specification.md"), "{stdout}");
}

#[test]
fn a_format_without_a_program_is_an_error_and_nothing_is_proved_or_assumed() {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "system API\nprimitive API, message\n[STORE] The API shall store the message.\n")]);
    let out = tempfile::tempdir().unwrap();
    let run = Command::new(env!("CARGO_BIN_EXE_trion")).env("PATH", tools_path()).args(["--out", &out.path().to_string_lossy(), "--format", "no-such-format"]).current_dir(f.path()).output().unwrap();
    assert_eq!(run.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&run.stderr).contains("trion-format-no-such-format"), "{}", String::from_utf8_lossy(&run.stderr));
    // A name that no program could have is refused before anything runs.
    let run = Command::new(env!("CARGO_BIN_EXE_trion")).args(["--out", &out.path().to_string_lossy(), "--format", "Bad Name"]).current_dir(f.path()).output().unwrap();
    assert_eq!(run.status.code(), Some(2));
}
