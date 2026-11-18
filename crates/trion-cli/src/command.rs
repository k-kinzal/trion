//! The `trion` command: it converts a package. It reads the package as
//! contracts, reports what does not conform to the language, and into the
//! directory that `--out` names it writes the MMT form of the package with
//! its proof obligations and each document that `--format` names. It proves
//! nothing, and a document does not wait for a proof: `trioc prove` proves
//! the obligations of the MMT form. The exit code tells whether the package
//! conforms to the language.
//!
//! An extension format is added by a program outside the trion processor
//! (spec/tool.trion): `--format NAME` for a name that is no format of its
//! own runs the program `trion-format-NAME`, found next to the `trion`
//! executable or on the `PATH`. The program reads the JSON report of the
//! conversion on its standard input (the report of `--json`: the contracts
//! by responsibility, the actors of the system and of the environment, the
//! proof obligations and the readings), takes the directory of `--out` as
//! its one argument, writes its files into it, and prints the path of each
//! file that it wrote, one on each line. Model code and test code are such
//! formats (`crates/trion-format-rust-test`).

use crate::convert::{convert, Converted};
use crate::project::{self, Project};
use clap::Parser;
use std::path::PathBuf;
use std::process::ExitCode;
use trioc_cli::check::written;
use trion_verification::Bounds;

/// A format that a package is converted into.
#[derive(Clone, PartialEq, Eq)]
enum Format {
    /// The MMT form: the contracts and the proof obligations, as an MMT archive.
    Mmt,
    Markdown,
    Html,
    /// An extension format: the program `trion-format-NAME` writes it.
    Extension(String),
}

impl Format {
    /// The file of a format of its own in the directory of `--out`.
    fn file(&self) -> Option<&'static str> {
        match self {
            Format::Mmt => Some(trioc_cli::mmt::FILE),
            Format::Markdown => Some("specification.md"),
            Format::Html => Some("specification.html"),
            Format::Extension(_) => None,
        }
    }
}

/// `mmt`, `markdown`, `html`, or the name of an extension format: lower
/// case letters, digits and hyphens, beginning with a letter.
fn format_of(text: &str) -> Result<Format, String> {
    Ok(match text {
        "mmt" => Format::Mmt,
        "markdown" => Format::Markdown,
        "html" => Format::Html,
        name if name.starts_with(|c: char| c.is_ascii_lowercase()) && name.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-') => Format::Extension(name.to_string()),
        other => return Err(format!("`{other}` is neither `mmt`, `markdown` nor `html`, nor the name of an extension format (lower case letters, digits and hyphens)")),
    })
}

/// The program of an extension format: next to this executable, or on the `PATH`.
fn extension_program(name: &str) -> Option<PathBuf> {
    let file = format!("trion-format-{name}{}", std::env::consts::EXE_SUFFIX);
    let beside = std::env::current_exe().ok().and_then(|exe| exe.parent().map(|dir| dir.join(&file)));
    let on_path = std::env::var_os("PATH").into_iter().flat_map(|paths| std::env::split_paths(&paths).collect::<Vec<_>>()).map(|dir| dir.join(&file));
    beside.into_iter().chain(on_path).find(|candidate| candidate.is_file())
}

/// Runs the program of an extension format with the JSON report on its
/// standard input and the directory of `--out` as its argument; the paths
/// that it prints are the files that it wrote.
fn run_extension(name: &str, report: &serde_json::Value, dir: &std::path::Path) -> Result<Vec<PathBuf>, String> {
    use std::io::Write;
    let program = extension_program(name).ok_or_else(|| format!("the format `{name}` is no format of trion, and no program `trion-format-{name}` is next to `trion` or on the PATH"))?;
    std::fs::create_dir_all(dir).map_err(|e| format!("cannot create {}: {e}", dir.display()))?;
    let mut child = std::process::Command::new(&program).arg(dir).stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).spawn().map_err(|e| format!("cannot run {}: {e}", program.display()))?;
    let input = serde_json::to_vec(report).map_err(|e| e.to_string())?;
    child.stdin.take().ok_or("no standard input")?.write_all(&input).map_err(|e| format!("cannot write to {}: {e}", program.display()))?;
    let output = child.wait_with_output().map_err(|e| format!("{}: {e}", program.display()))?;
    if !output.status.success() {
        return Err(format!("the program of the format `{name}`, {}, failed with {}", program.display(), output.status));
    }
    Ok(String::from_utf8_lossy(&output.stdout).lines().map(str::trim).filter(|l| !l.is_empty()).map(PathBuf::from).collect())
}

/// Convert a package: report what does not conform to the language, and
/// write the MMT form of the package and its documents. Nothing is proved;
/// `trioc prove` proves the obligations of the MMT form.
#[derive(Parser)]
#[command(name = "trion", version)]
struct Cli {
    #[arg(default_value = ".")]
    path: PathBuf,
    /// Print a JSON report instead of text.
    #[arg(long)]
    json: bool,
    /// Write each format that `--format` names into this directory; without
    /// `--format`, the MMT form.
    #[arg(long, value_name = "DIR")]
    out: Option<PathBuf>,
    /// A format to write into the directory of `--out`: `mmt`, `markdown`,
    /// `html`, or an extension format that the program `trion-format-NAME`
    /// writes.
    #[arg(long, value_parser = format_of, value_name = "FORMAT", requires = "out")]
    format: Vec<Format>,
    /// Write only this file of the package as the document.
    #[arg(long, requires = "format")]
    file: Option<String>,
    /// The obligations are about traces of this many moments.
    #[arg(long, value_name = "K")]
    trace_length: Option<usize>,
    /// The obligations read the statements about individuals over this many
    /// individuals of each type.
    #[arg(long, value_name = "N")]
    scope: Option<usize>,
    /// Examine the properties of the reader as well: context independence,
    /// relation locality, order independence, the round trip, and the
    /// behaviours next to each scenario.
    #[arg(long)]
    properties: bool,
}

/// The bounds that the obligations are about: the manifest says them, and
/// an argument takes the place of what it names.
fn bounds(cli: &Cli, project: &Project) -> Bounds {
    let stated = &project.manifest.verify;
    let default = Bounds::default();
    Bounds { decisions: stated.decision_limit, trace_length: cli.trace_length.or(stated.trace_length).unwrap_or(default.trace_length).max(2), scope: cli.scope.or(stated.scope).unwrap_or(default.scope).min(6) }
}

fn write(path: &std::path::Path, text: &str) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).map_err(|e| format!("cannot create {}: {e}", parent.display()))?;
    }
    std::fs::write(path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))
}

fn report(converted: &Converted, written: &[PathBuf]) -> serde_json::Value {
    let analysis = &converted.analysis;
    serde_json::json!({
        "conforms": !converted.failed(),
        "diagnostics": converted.diagnostics,
        // What a normative statement says and no rule reads, gives a meaning, or can express.
        "opaque": analysis.silence.opaque,
        "ungrounded": analysis.silence.ungrounded,
        "inexpressible": analysis.silence.inexpressible,
        "checker": converted.checker,
        // What the package declares and nothing checks.
        "declared": converted.declared,
        "sources": converted.sources,
        "relations": analysis.relations,
        "individuals": analysis.model.individuals,
        "readings": analysis.model.individuals.iter().flat_map(|i| &i.meanings).map(|m| serde_json::json!({"statement": m.statement, "version": m.version, "lines": m.lines()})).collect::<Vec<_>>(),
        "control": converted.control,
        "contracts": converted.contracts,
        // The examples that demonstrate the conversion: each observed what it expects, or the package does not convert.
        "demonstrations": converted.demonstrated,
        // What the checker showed of the reading: each difference is an error above.
        "checked": converted.checked,
        "obligations": converted.obligations.obligations.iter().map(|o| serde_json::json!({"name": o.name, "property": o.property, "proposition": o.proposition, "statements": o.statements})).collect::<Vec<_>>(),
        "written": written,
        "proved": false,
    })
}

fn dispatch(cli: Cli) -> Result<bool, String> {
    let project = project::load(&cli.path)?;
    let properties = cli.properties || project.manifest.verify.properties;
    let converted = convert(&project, bounds(&cli, &project), properties);
    let mut paths = Vec::new();
    // A package that does not conform to the language is not converted.
    if let (Some(dir), false) = (&cli.out, converted.failed()) {
        let formats = if cli.format.is_empty() { vec![Format::Mmt] } else { cli.format.clone() };
        for format in formats {
            let text = match &format {
                // The form is read back before it is written: one that does
                // not read back as itself is an error of trion, and it is not
                // written. Its typing in LF is MMT's verdict (tests/mmt_form.rs).
                Format::Mmt => converted.form(&project).write().map_err(|e| format!("internal error of trion: the MMT form of the package is not written: {e}"))?,
                Format::Markdown => crate::markdown::render(&project, &converted, cli.file.as_deref())?,
                Format::Html => crate::doc::render(&project, &converted, cli.file.as_deref())?,
                Format::Extension(name) => {
                    paths.extend(run_extension(name, &report(&converted, &[]), dir)?);
                    continue;
                }
            };
            let Some(file) = format.file() else { continue };
            let path = dir.join(file);
            write(&path, &text)?;
            paths.push(path);
            // The MMT form is an archive: its manifest names it to MMT.
            if format == Format::Mmt {
                let manifest = dir.join(trioc_cli::mmt::MANIFEST);
                write(&manifest, &converted.form(&project).manifest())?;
                paths.push(manifest);
            }
        }
    } else if cli.out.is_some() {
        eprintln!("nothing is written: the package does not conform to the language");
    }
    if cli.json {
        println!("{}", serde_json::to_string_pretty(&report(&converted, &paths)).unwrap_or_default());
    } else {
        for diagnostic in converted.all() {
            print!("{}", written(diagnostic));
        }
        for declared in &converted.declared {
            println!("declared, not checked: {declared}");
        }
        // The reading of each statement over individuals, as the JSON report
        // and the document show it.
        if let Some(individuals) = &converted.analysis.model.individuals {
            let types: std::collections::BTreeSet<&str> = individuals.types.iter().map(|(_, carrier)| carrier.as_str()).collect();
            println!("individuals: semantic version {}; domains of {} individuals of each declared type ({})", individuals.version, individuals.scope, types.into_iter().collect::<Vec<_>>().join(", "));
            for meaning in &individuals.meanings {
                println!("reading [{}]:", meaning.statement);
                for line in meaning.lines() {
                    println!("  {line}");
                }
            }
        }
        for obligation in &converted.obligations.obligations {
            println!("obligation {} ({}): not proved here: {}", obligation.name, obligation.property, obligation.proposition);
        }
        for path in &paths {
            println!("wrote {}", path.display());
        }
        println!("{}", if converted.failed() { "does not conform" } else { "converted" });
    }
    Ok(converted.failed())
}

/// Runs the command that the arguments of the process name.
pub fn run() -> ExitCode {
    match dispatch(Cli::parse()) {
        Ok(false) => ExitCode::SUCCESS,
        Ok(true) => ExitCode::from(1),
        Err(message) => {
            eprintln!("error: {message}");
            ExitCode::from(2)
        }
    }
}
