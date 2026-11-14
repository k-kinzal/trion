#![allow(dead_code)]

mod inspect;
pub use inspect::inspect_in;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use tempfile::TempDir;

pub fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap()
}

/// A project on disk, removed when dropped.
///
/// A test writes only what it is about. Every `.trion` file without a
/// `namespace` block is wrapped in one named after its package, and each
/// package without an entry file gets one that includes all of its files.
pub struct Fixture {
    pub dir: TempDir,
}

/// The value of `name = "..."` in the `[package]` table of a manifest.
fn package_name(manifest: &str) -> Option<String> {
    let table = manifest.split("[package]").nth(1)?;
    let line = table.lines().find(|l| l.trim_start().starts_with("name"))?;
    Some(line.split_once('=')?.1.trim().trim_matches('"').to_string())
}

fn has_entry_field(manifest: &str) -> bool {
    manifest.lines().any(|l| l.trim_start().starts_with("entry"))
}

/// Wraps statements in a namespace block of the package.
pub fn wrap(package: &str, text: &str) -> String {
    let first = text.lines().map(str::trim_start).find(|l| !l.is_empty() && !l.starts_with("//")).unwrap_or_default();
    if ["namespace ", "package ", "include "].iter().any(|k| first.starts_with(k)) {
        return text.to_string();
    }
    format!("namespace {package}\n{text}\n")
}

impl Fixture {
    pub fn new(files: &[(&str, &str)]) -> Self {
        Self::build(files, true)
    }

    /// Writes the files exactly as given.
    pub fn raw(files: &[(&str, &str)]) -> Self {
        Self::build(files, false)
    }

    fn build(files: &[(&str, &str)], complete: bool) -> Self {
        let fixture = Self { dir: tempfile::tempdir().unwrap() };
        if !complete {
            for (path, text) in files {
                fixture.write(path, text);
            }
            return fixture;
        }
        // The directory of each package, longest first, so that the nearest wins.
        let mut packages: Vec<(String, String, bool)> = files
            .iter()
            .filter(|(p, _)| Path::new(p).file_name().is_some_and(|n| n == "trion.toml"))
            .map(|(p, text)| {
                let dir = Path::new(p).parent().unwrap().to_string_lossy().into_owned();
                (dir, package_name(text).unwrap_or_else(|| "main".to_string()), has_entry_field(text))
            })
            .collect();
        packages.sort_by_key(|(dir, _, _)| std::cmp::Reverse(dir.len()));
        let owner = |path: &str| packages.iter().find(|(dir, _, _)| dir.is_empty() || path.starts_with(&format!("{dir}/"))).cloned();
        let mut includes: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (path, text) in files {
            if !path.ends_with(".trion") {
                fixture.write(path, text);
                continue;
            }
            let package = owner(path);
            let name = package.as_ref().map_or("main".to_string(), |(_, n, _)| n.clone());
            fixture.write(path, &wrap(&name, text));
            if let Some((dir, _, _)) = package {
                let relative = if dir.is_empty() { path.to_string() } else { path[dir.len() + 1..].to_string() };
                includes.entry(dir).or_default().push(relative);
            }
        }
        for (dir, name, has_entry) in &packages {
            let entry = if dir.is_empty() { "trion.trion".to_string() } else { format!("{dir}/trion.trion") };
            if *has_entry || files.iter().any(|(p, _)| *p == entry) {
                continue;
            }
            let mut text = format!("package {name} edition \"test\"\n");
            for file in includes.get(dir).into_iter().flatten() {
                text.push_str(&format!("include \"{file}\"\n"));
            }
            fixture.write(&entry, &text);
        }
        fixture
    }

    pub fn path(&self) -> &Path {
        self.dir.path()
    }

    pub fn write(&self, path: &str, text: &str) {
        let full = self.path().join(path);
        fs::create_dir_all(full.parent().unwrap()).unwrap();
        fs::write(full, text).unwrap();
    }

    pub fn read(&self, path: &str) -> String {
        fs::read_to_string(self.path().join(path)).unwrap()
    }

    pub fn trion(&self, args: &[&str]) -> Result {
        trion_in(self.path(), args)
    }

    /// A view of what the libraries read from this project.
    pub fn inspect(&self, args: &[&str]) -> Result {
        inspect_in(self.path(), args)
    }
}

pub struct Result {
    pub code: i32,
    pub stdout: String,
    pub stderr: String,
}

impl Result {
    fn from(output: Output) -> Self {
        Self {
            code: output.status.code().unwrap_or(-1),
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        }
    }

    pub fn json(&self) -> serde_json::Value {
        serde_json::from_str(&self.stdout).unwrap_or_else(|e| panic!("{e}: {}{}", self.stdout, self.stderr))
    }
}

/// Runs the command with environment variables, as a fixture with a seeded fault does.
pub fn trion_with(dir: &Path, args: &[&str], variables: &[(&str, &str)]) -> Result {
    Result::from(Command::new(env!("CARGO_BIN_EXE_trion")).args(args).envs(variables.iter().copied()).current_dir(dir).output().unwrap())
}

pub fn trion_in(dir: &Path, args: &[&str]) -> Result {
    Result::from(Command::new(env!("CARGO_BIN_EXE_trion")).args(args).current_dir(dir).output().unwrap())
}

pub fn sha256(text: &str) -> String {
    use sha2::{Digest, Sha256};
    Sha256::digest(text.as_bytes()).iter().map(|b| format!("{b:02x}")).collect()
}

fn escape(text: &str) -> String {
    text.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n")
}

/// A `source` block with a local copy of `text` at `path` and the given quotes.
pub fn source_block(name: &str, kind: &str, path: &str, text: &str, extra: &str, quotes: &[(&str, &str)]) -> String {
    let mut block = format!("source {name}:\n    kind {kind}\n    path \"{path}\"\n    sha256 \"{}\"\n", sha256(text));
    // Every source names its title and its locator.
    if !extra.contains("title ") {
        block.push_str(&format!("    title \"{name}\"\n"));
    }
    if !extra.contains("locator ") {
        block.push_str(&format!("    locator \"file:{path}\"\n"));
    }
    for line in extra.lines().filter(|l| !l.trim().is_empty()) {
        block.push_str(&format!("    {}\n", line.trim()));
    }
    for (quote, body) in quotes {
        block.push_str(&format!("    quote {quote} \"{}\"\n", escape(body)));
    }
    block
}

/// The codes of the diagnostics of the analysis alone. A report holds its
/// findings in several lists, so an empty result here is no success: a
/// test that means `nothing was found` asserts [`report_codes`], and one
/// that means `the package is verified` asserts [`assert_verified`].
pub fn analysis_codes(value: &serde_json::Value) -> Vec<String> {
    value["diagnostics"].as_array().unwrap().iter().map(|d| d["code"].as_str().unwrap().to_string()).collect()
}

/// The codes of every finding of a JSON report: the diagnostics of the
/// analysis, and what a statement says that no rule reads, grounds or can
/// express. Empty only when none of these lists holds a finding.
pub fn report_codes(value: &serde_json::Value) -> Vec<String> {
    let mut codes: Vec<String> = value["diagnostics"].as_array().unwrap().iter().map(|d| d["code"].as_str().unwrap().to_string()).collect();
    for list in ["opaque", "ungrounded", "inexpressible"] {
        for d in value[list].as_array().into_iter().flatten() {
            let code = d["code"].as_str().unwrap().to_string();
            if !codes.contains(&code) {
                codes.push(code);
            }
        }
    }
    codes
}

/// The codes of what keeps a report from being a success: the blockers of
/// its outcome, from every gate. Empty exactly when the package is verified.
pub fn unverified(value: &serde_json::Value) -> Vec<String> {
    value["outcome"]["blockers"].as_array().unwrap().iter().map(|b| b["code"].as_str().unwrap().to_string()).collect()
}

/// Asserts that a report is a success in each of its parts: the outcome, the
/// gates, the claims, the meaning obligations and every list of findings. A
/// test that means `the package is verified` asserts this, and not that the
/// diagnostics of the analysis are empty.
pub fn assert_verified(value: &serde_json::Value) {
    assert_eq!(value["outcome"]["verified"], true, "{value}");
    assert!(unverified(value).is_empty(), "{value}");
    for gate in value["gates"].as_array().unwrap() {
        assert_ne!(gate["state"], "failed", "the gate {} failed: {value}", gate["name"]);
    }
    // The gates that every verification runs are run: a skip of one is no pass.
    for name in ["check", "meaning", "claims", "sources", "prover"] {
        assert!(value["gates"].as_array().unwrap().iter().any(|gate| gate["name"] == name && gate["state"] == "passed"), "the gate {name} did not pass: {value}");
    }
    for list in ["opaque", "ungrounded", "inexpressible", "obligations", "prover", "properties", "stability"] {
        assert!(value[list].as_array().unwrap().is_empty(), "`{list}` is not empty: {value}");
    }
    assert!(value["diagnostics"].as_array().unwrap().iter().all(|d| d["severity"] != "error"), "{value}");
    assert!(value["sources"]["diagnostics"].as_array().unwrap().iter().all(|d| d["severity"] != "error"), "{value}");
    for claim in value["claims"].as_array().unwrap() {
        if claim["required"] == true {
            assert!(claim["verdict"] == "proved" && claim["vacuous"] == false, "the claim {} is not proved: {value}", claim["claim"]);
        }
    }
    assert_eq!(value["consistency"]["verdict"], "consistent", "{value}");
}

pub const MANIFEST: &str = "[package]\nname = \"p\"\n";
