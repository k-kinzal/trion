#![allow(dead_code)]

mod inspect;
pub use inspect::inspect_in;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use tempfile::TempDir;

pub fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}

/// The search path of the commands: the tools in `.tools/bin` of the
/// repository (the checkers of the certificates, and Java for MMT) come
/// first, then `PATH`. trion and trioc run none of them.
pub fn tools_path() -> String {
    let tools = repo_root().join(".tools/bin");
    format!(
        "{}:{}",
        tools.display(),
        std::env::var("PATH").unwrap_or_default()
    )
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
    manifest
        .lines()
        .any(|l| l.trim_start().starts_with("entry"))
}

/// Wraps statements in a namespace block of the package.
pub fn wrap(package: &str, text: &str) -> String {
    let first = text
        .lines()
        .map(str::trim_start)
        .find(|l| !l.is_empty() && !l.starts_with("//"))
        .unwrap_or_default();
    if ["namespace ", "package ", "include "]
        .iter()
        .any(|k| first.starts_with(k))
    {
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
        let fixture = Self {
            dir: tempfile::tempdir().unwrap(),
        };
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
                let dir = Path::new(p)
                    .parent()
                    .unwrap()
                    .to_string_lossy()
                    .into_owned();
                (
                    dir,
                    package_name(text).unwrap_or_else(|| "main".to_string()),
                    has_entry_field(text),
                )
            })
            .collect();
        packages.sort_by_key(|(dir, _, _)| std::cmp::Reverse(dir.len()));
        let owner = |path: &str| {
            packages
                .iter()
                .find(|(dir, _, _)| dir.is_empty() || path.starts_with(&format!("{dir}/")))
                .cloned()
        };
        let mut includes: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (path, text) in files {
            if !path.ends_with(".trion") {
                fixture.write(path, text);
                continue;
            }
            let package = owner(path);
            let name = package
                .as_ref()
                .map_or("main".to_string(), |(_, n, _)| n.clone());
            fixture.write(path, &wrap(&name, text));
            if let Some((dir, _, _)) = package {
                let relative = if dir.is_empty() {
                    path.to_string()
                } else {
                    path[dir.len() + 1..].to_string()
                };
                includes.entry(dir).or_default().push(relative);
            }
        }
        for (dir, name, has_entry) in &packages {
            let entry = if dir.is_empty() {
                "trion.trion".to_string()
            } else {
                format!("{dir}/trion.trion")
            };
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

    /// Converts the package and proves its obligations: see [`verify_in`].
    pub fn verify(&self, args: &[&str]) -> Result {
        verify_in(self.path(), args)
    }

    /// Converts the package: `trion`.
    pub fn convert(&self, args: &[&str]) -> Result {
        convert_in(self.path(), args)
    }

    /// Proves the obligations of an MMT form: `trioc prove`.
    pub fn prove(&self, args: &[&str]) -> Result {
        let mut arguments = vec!["prove"];
        arguments.extend(args);
        Result::from(
            Command::new(env!("CARGO_BIN_EXE_trioc"))
                .env("PATH", tools_path())
                .args(&arguments)
                .current_dir(self.path())
                .output()
                .unwrap(),
        )
    }

    /// The package as an HTML document: see [`document_in`].
    pub fn document(&self, args: &[&str]) -> Result {
        document_in(self.path(), args)
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
        serde_json::from_str(&self.stdout)
            .unwrap_or_else(|e| panic!("{e}: {}{}", self.stdout, self.stderr))
    }
}

/// Converts the package with `trion --out` and proves the obligations of
/// the MMT form that it wrote with `trioc prove`, with environment
/// variables, as a fixture with a seeded fault does. `--decision-limit N`
/// and `--against FILE` go to `trioc`, `--json` to both, and
/// every other argument to `trion`. The run fails when either command fails; its text
/// is that of `trion` followed by that of `trioc`, and its JSON is that of
/// `trion` with the result of `trioc` under `proof` and the findings of
/// both under `diagnostics`. A package that does not convert is not proved.
pub fn verify_with(dir: &Path, args: &[&str], variables: &[(&str, &str)]) -> Result {
    let form = tempfile::tempdir().unwrap();
    let target = form.path().to_string_lossy().into_owned();
    let (mut converting, mut proving): (Vec<&str>, Vec<&str>) = (
        vec!["--out", target.as_str()],
        vec!["prove", target.as_str()],
    );
    let mut rest = args.iter();
    let json = args.contains(&"--json");
    while let Some(arg) = rest.next() {
        match *arg {
            "--json" => {
                converting.push(arg);
                proving.push(arg);
            }
            "--decision-limit" | "--against" => {
                proving.push(arg);
                proving.extend(rest.next());
            }
            _ => converting.push(arg),
        }
    }
    let converted = Result::from(
        Command::new(env!("CARGO_BIN_EXE_trion"))
            .env("PATH", tools_path())
            .args(&converting)
            .envs(variables.iter().copied())
            .current_dir(dir)
            .output()
            .unwrap(),
    );
    if converted.code != 0 || !form.path().join("source/specification.mmt").is_file() {
        return converted;
    }
    let proved = Result::from(
        Command::new(env!("CARGO_BIN_EXE_trioc"))
            .env("PATH", tools_path())
            .args(&proving)
            .envs(variables.iter().copied())
            .current_dir(dir)
            .output()
            .unwrap(),
    );
    let code = if proved.code != 0 {
        proved.code
    } else {
        converted.code
    };
    if !json {
        return Result {
            code,
            stdout: format!("{}{}", converted.stdout, proved.stdout),
            stderr: format!("{}{}", converted.stderr, proved.stderr),
        };
    }
    let (Ok(mut value), Ok(proof)) = (
        serde_json::from_str::<serde_json::Value>(&converted.stdout),
        serde_json::from_str::<serde_json::Value>(&proved.stdout),
    ) else {
        return Result {
            code,
            stdout: format!("{}{}", converted.stdout, proved.stdout),
            stderr: format!("{}{}", converted.stderr, proved.stderr),
        };
    };
    if let (Some(all), Some(found)) = (
        value["diagnostics"].as_array().cloned(),
        proof["diagnostics"].as_array(),
    ) {
        value["diagnostics"] =
            serde_json::Value::Array(all.into_iter().chain(found.iter().cloned()).collect());
    }
    value["proof"] = proof;
    Result {
        code,
        stdout: serde_json::to_string_pretty(&value).unwrap(),
        stderr: format!("{}{}", converted.stderr, proved.stderr),
    }
}

/// Converts and proves the package: [`verify_with`] without variables.
pub fn verify_in(dir: &Path, args: &[&str]) -> Result {
    verify_with(dir, args, &[])
}

/// Runs `trion`: the conversion of a package.
pub fn convert_in(dir: &Path, args: &[&str]) -> Result {
    Result::from(
        Command::new(env!("CARGO_BIN_EXE_trion"))
            .env("PATH", tools_path())
            .args(args)
            .current_dir(dir)
            .output()
            .unwrap(),
    )
}

/// Runs the command so that it writes the package as an HTML document, and
/// returns the run with the document in place of its standard output:
/// nothing when no document was written.
pub fn document_in(dir: &Path, args: &[&str]) -> Result {
    let out = tempfile::tempdir().unwrap();
    let target = out.path().to_string_lossy().into_owned();
    let mut arguments = vec!["--out", target.as_str(), "--format", "html"];
    arguments.extend(args);
    let mut result = convert_in(dir, &arguments);
    result.stdout = fs::read_to_string(out.path().join("specification.html")).unwrap_or_default();
    result
}

pub fn sha256(text: &str) -> String {
    use sha2::{Digest, Sha256};
    Sha256::digest(text.as_bytes())
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

fn escape(text: &str) -> String {
    text.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
}

/// A `source` block with a local copy of `text` at `path` and the given quotes.
pub fn source_block(
    name: &str,
    kind: &str,
    path: &str,
    text: &str,
    extra: &str,
    quotes: &[(&str, &str)],
) -> String {
    let mut block = format!(
        "source {name}:\n    kind {kind}\n    path \"{path}\"\n    sha256 \"{}\"\n",
        sha256(text)
    );
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
    value["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .map(|d| d["code"].as_str().unwrap().to_string())
        .filter(|code| code != SYSTEM_UNDECLARED)
        .collect()
}

/// The warning that a package declares no system. Most packages of the
/// tests declare none, and the warning is about none of them: the lists of
/// codes leave it out, and `tests/trioc.rs` asserts it where it is meant.
pub const SYSTEM_UNDECLARED: &str = "system-undeclared";

/// The codes of every finding of a JSON report: the diagnostics of the
/// analysis, and what a statement says that no rule reads, grounds or can
/// express. Empty only when none of these lists holds a finding.
pub fn report_codes(value: &serde_json::Value) -> Vec<String> {
    let mut codes = analysis_codes(value);
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

/// The codes of what keeps a report from being a success: each error of
/// the conversion, in each of its lists, and each finding of the proof.
/// Empty exactly when the package converts and every obligation is proved.
pub fn unverified(value: &serde_json::Value) -> Vec<String> {
    let mut codes = Vec::new();
    for list in [
        &value["diagnostics"],
        &value["checker"],
        &value["opaque"],
        &value["ungrounded"],
        &value["inexpressible"],
        &value["sources"]["diagnostics"],
    ] {
        for d in list
            .as_array()
            .into_iter()
            .flatten()
            .filter(|d| d["severity"] == "error")
        {
            let code = d["code"].as_str().unwrap().to_string();
            if !codes.contains(&code) {
                codes.push(code);
            }
        }
    }
    for result in value["proof"]["results"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|r| r["verdict"] != "proved")
    {
        let name = result["obligation"].as_str().unwrap().to_string();
        if !codes.contains(&name) {
            codes.push(name);
        }
    }
    codes
}

/// The verdict of each obligation of a report, by its name.
pub fn verdicts(value: &serde_json::Value) -> BTreeMap<String, String> {
    value["proof"]["results"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|r| {
            (
                r["obligation"].as_str().unwrap().to_string(),
                r["verdict"].as_str().unwrap().to_string(),
            )
        })
        .collect()
}

/// Asserts that a report is a success in each of its parts: the package
/// converts with no error in any list, and every obligation of its MMT
/// form is proved. A test that means `the package is verified` asserts
/// this, and not that the diagnostics of the analysis are empty.
pub fn assert_verified(value: &serde_json::Value) {
    assert_eq!(value["conforms"], true, "{value}");
    assert!(
        unverified(value).is_empty(),
        "{:?}: {value}",
        unverified(value)
    );
    for list in ["opaque", "ungrounded", "inexpressible", "checker"] {
        assert!(
            value[list].as_array().unwrap().is_empty(),
            "`{list}` is not empty: {value}"
        );
    }
    let results = value["proof"]["results"]
        .as_array()
        .unwrap_or_else(|| panic!("nothing was proved: {value}"));
    assert!(
        results
            .iter()
            .any(|r| r["obligation"] == "consistency" && r["verdict"] == "proved"),
        "{value}"
    );
}

pub const MANIFEST: &str = "[package]\nname = \"p\"\n";
