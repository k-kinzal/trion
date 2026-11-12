//! The commands of `trion`: `verify` verifies a package, `doc` writes a
//! verified package as a document, and `lsp` serves editors. The exit code
//! tells whether the command failed.

use crate::project::{self, Project};
use crate::verify::{self, Settings, Verification};
use clap::{Args, Parser, Subcommand};
use serde::Serialize;
use std::path::PathBuf;
use std::process::ExitCode;
use trion_language::{Diagnostic, Severity};
use trion_verification::Analysis;

#[derive(Parser)]
#[command(name = "trion", version, about = "Verify specifications written in the trion language")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

/// How a package is verified. Each argument takes the place of the field of
/// the same name under `[verify]` in trion.toml.
#[derive(Args)]
struct VerifyArgs {
    /// Examine traces of this many moments; a result holds within that bound.
    #[arg(long, value_name = "K")]
    trace_length: Option<usize>,
    /// Read the statements about individuals over this many individuals of
    /// each type; a result holds within that bound. With 0 no statement is
    /// read over individuals.
    #[arg(long, value_name = "N")]
    scope: Option<usize>,
    /// Stop each solver query after this many decisions; a result that the
    /// limit leaves open is reported as unknown.
    #[arg(long, value_name = "N")]
    decision_limit: Option<u64>,
    /// Check the properties of the reading: context independence, relation
    /// locality, order independence and round trip.
    #[arg(long)]
    properties: bool,
    /// Decide the package again with each bound raised, and report each
    /// outcome that depends on the bounds.
    #[arg(long)]
    stability: bool,
    /// Write the queries of the result into this directory as SMT-LIB, for
    /// another solver.
    #[arg(long, value_name = "DIR")]
    smt: Option<PathBuf>,
    /// Ask this external prover each query of the result, in place of
    /// `z3 -in`: a command that reads SMT-LIB on its standard input.
    #[arg(long, value_name = "COMMAND")]
    prover: Option<String>,
}

impl VerifyArgs {
    /// The settings of a project with the arguments in place of what they name.
    fn settings(&self, project: &Project) -> Settings {
        let mut settings = Settings::of(project);
        if let Some(length) = self.trace_length {
            settings.bounds.trace_length = length.max(2);
        }
        if let Some(scope) = self.scope {
            settings.bounds.scope = scope.min(6);
        }
        if self.decision_limit.is_some() {
            settings.bounds.decisions = self.decision_limit;
        }
        settings.properties |= self.properties;
        settings.stability |= self.stability;
        if let Some(dir) = &self.smt {
            settings.smt = Some(dir.clone());
        }
        if let Some(command) = &self.prover {
            settings.prover = command.split_whitespace().map(str::to_string).collect();
        }
        settings
    }
}

#[derive(Subcommand)]
enum Command {
    /// Verify a package: find contradictions, form violations, missing cases
    /// and vocabulary problems, ask an external prover each question that
    /// the result rests on, and check the sources of the statements.
    Verify {
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Print a JSON report instead of text.
        #[arg(long)]
        json: bool,
        #[command(flatten)]
        verify: VerifyArgs,
    },
    /// Write a verified package as one HTML document: prose, figures, terms
    /// and the status of each statement. A package that is not verified has
    /// no document.
    Doc {
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Write only this file of the package.
        #[arg(long)]
        file: Option<String>,
        /// Write the document to this file instead of standard output.
        #[arg(long)]
        out: Option<PathBuf>,
        #[command(flatten)]
        verify: VerifyArgs,
    },
    /// Start the language server on standard input and output.
    Lsp,
}

/// How a diagnostic is written: its level and code, its message, and the
/// places that it is about.
fn written(d: &Diagnostic) -> String {
    let level = match d.severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
        Severity::Info => "info",
    };
    let mut out = format!("{level}[{}]: {}\n", d.code, d.message);
    for r in &d.refs {
        out.push_str(&format!("  {}:{} [{}] {}\n", r.file, r.line, r.id, r.text));
    }
    out
}

fn print_diagnostics(diags: &[Diagnostic]) {
    for d in diags {
        print!("{}", written(d));
    }
}

fn to_json<T: Serialize>(value: &T) -> String {
    serde_json::to_string_pretty(value).unwrap_or_else(|e| format!("{{\"error\":\"{e}\"}}"))
}

/// Prints what each conflict set rests on, the conditions that hold emptily
/// and the consistency result with its method and bounds.
fn print_verification(analysis: &Analysis) {
    for conflict in &analysis.conflicts {
        let size = if conflict.minimal { "minimal" } else { "sufficient, not proved minimal" };
        // A conflict under two conditions together has no row of certificates.
        println!("conflict [{}] ({size}):", conflict.code);
        if let Some(condition) = &conflict.condition {
            println!("  under the condition: {condition}");
        }
        for element in &conflict.elements {
            println!("  [{}] {}", element.reference.id, element.expansion);
            if !element.scopes.is_empty() {
                println!("    scopes: {}", element.scopes.join("; "));
            }
            if !element.terms.is_empty() {
                println!("    terms: {}", element.terms.join(", "));
            }
        }
        for step in &conflict.derivation {
            println!("  derivation {}: {} => {}", step.origin, step.assume, step.guarantee);
        }
        for definition in &conflict.definitions {
            println!("  definition [{}] {}", definition.id, definition.text);
        }
    }
    // Which statement wins where two statements conflict.
    for priority in &analysis.model.priorities {
        let scope = if priority.condition == "⊤" { "everywhere".to_string() } else { format!("where {}", priority.condition) };
        let how = match priority.kind.as_str() {
            "default" => format!("[{}] is a default and yields to [{}]", priority.yields.id, priority.to.id),
            "narrows" => format!("[{}] restricts the permission [{}]", priority.to.id, priority.yields.id),
            _ => format!("[{}] overrides [{}]", priority.to.id, priority.yields.id),
        };
        println!("priority: {how} {scope}");
    }
    if let Some(preference) = &analysis.preference {
        let names = |refs: &[trion_language::SpecRef]| refs.iter().map(|r| format!("[{}]", r.id)).collect::<Vec<_>>().join(", ");
        let reach = if preference.optimal { "no other set weighs more" } else { "chosen by weight, greatest first; not proved best" };
        println!("recommendations: keep {} (weight {}); drop {} (weight {}); {reach}", names(&preference.kept), preference.kept_weight, names(&preference.dropped), preference.dropped_weight);
    }
    for vacuous in &analysis.coverage.vacuous {
        println!("coverage: [{}] holds only because its condition is {}: {}", vacuous.reference.id, vacuous.reason, vacuous.condition);
    }
    let c = &analysis.consistency;
    let decisions = c.bounds.decisions.map_or(String::new(), |n| format!("{n} decisions for each query, "));
    // The domain bound is part of the result only when a statement relates individuals.
    let domains = analysis.model.instance_scope.map_or(String::new(), |n| format!(", domains of {n} individuals"));
    let bounds = format!("{decisions}traces of {} moments{domains}", c.bounds.trace_length);
    let reach = if c.exhaustive { "the search within the bounds was exhaustive" } else { "the bounds ended the search" };
    println!("consistency: {} (status {}; revision {}; bounds: {bounds}; {reach})", c.verdict, c.status.as_str(), c.subject_revision.as_deref().map_or("unknown", |r| &r[..r.len().min(12)]));
    if let Some(situations) = &c.situations {
        println!("  situations: {situations}");
    }
    println!("  method: {}", c.method);
    println!("  profile: {}", c.profile);
    println!("  assumptions: {}", c.assumptions.join("; "));
}

/// More findings of one kind than this are counted, not listed; the JSON report lists each.
const LISTED: usize = 10;

fn count(diags: &[Diagnostic], severity: Severity) -> usize {
    diags.iter().filter(|d| d.severity == severity).count()
}

/// The report of a verification as JSON.
fn report(verification: &Verification) -> serde_json::Value {
    let analysis = &verification.analysis;
    serde_json::json!({
        "diagnostics": verification.diagnostics,
        "consistency": analysis.consistency,
        "conflicts": analysis.conflicts,
        "coverage": analysis.coverage,
        "guards": analysis.guards,
        "relations": analysis.relations,
        "checks": analysis.checks,
        "examples": analysis.examples,
        "opaque": analysis.silence.opaque,
        "ungrounded": analysis.silence.ungrounded,
        "inexpressible": analysis.silence.inexpressible,
        "priorities": analysis.model.priorities,
        "preference": analysis.preference,
        "environment": analysis.environment,
        "weight": verification.weight,
        "sources": verification.sources,
        "prover": verification.prover,
        "properties": verification.properties,
        "stability": verification.stability,
        "gates": verification.gates,
    })
}

/// Prints the report of a verification as text.
fn print_report(project: &Project, verification: &Verification) {
    let analysis = &verification.analysis;
    print_diagnostics(&verification.diagnostics);
    print_verification(analysis);
    // How much the word `consistent` covers.
    println!("  weight: {}", verification.weight.line());
    let silence = &analysis.silence;
    print_diagnostics(&silence.opaque);
    print_diagnostics(&silence.ungrounded);
    // A property that no check of one model can read is always shown.
    print_diagnostics(&silence.inexpressible);
    // The sources: each error, the first statements without a source, and the coverage of each source.
    let sources = &verification.sources;
    let (unsourced, other): (Vec<&Diagnostic>, Vec<&Diagnostic>) = sources.diagnostics.iter().partition(|d| d.code == "unsourced");
    for diagnostic in other.iter().chain(unsourced.iter().take(LISTED)) {
        print!("{}", written(diagnostic));
    }
    if unsourced.len() > LISTED {
        println!("unsourced: {} statements name no source (`--json` lists them)", unsourced.len());
    }
    for source in &sources.sources {
        println!("source coverage of {}: {:.2}%", source.id, source.percent);
    }
    print_diagnostics(&verification.prover);
    print_diagnostics(&verification.properties);
    print_diagnostics(&verification.stability);
    let all: Vec<Diagnostic> = verification.diagnostics.iter().chain(&sources.diagnostics).chain(&verification.prover).chain(&verification.properties).chain(&verification.stability).cloned().collect();
    let specs: usize = project.set.packages.iter().flat_map(|p| &p.documents).map(|d| d.specs.len()).sum();
    let proved = analysis.checks.iter().filter(|c| c.result == "proved").count();
    println!("checked {specs} specifications: {} errors, {} warnings; {proved}/{} checks proved, {} examples run", count(&all, Severity::Error) + verification.unread().len(), count(&all, Severity::Warning), analysis.checks.len(), analysis.examples.len());
    for gate in &verification.gates {
        println!("gate {}: {}", gate.name, gate.state);
    }
    println!("{}", if verification.failed() { "not verified" } else { "verified" });
}

fn dispatch(cli: Cli) -> Result<bool, String> {
    match cli.command {
        Command::Verify { path, json, verify } => {
            let project = project::load(&path)?;
            let verification = verify::verify(&project, &verify.settings(&project))?;
            if json {
                println!("{}", to_json(&report(&verification)));
            } else {
                print_report(&project, &verification);
            }
            Ok(verification.failed())
        }
        Command::Doc { path, file, out, verify } => {
            let project = project::load(&path)?;
            let verification = verify::verify(&project, &verify.settings(&project))?;
            // A document states a verified specification: what is not verified has none.
            if verification.failed() {
                let failed: Vec<&str> = verification.gates.iter().filter(|gate| gate.state == "failed").map(|gate| gate.name).collect();
                return Err(format!("the package is not verified (gate {}): `trion verify` reports what fails, and a package that is not verified has no document", failed.join(", ")));
            }
            let html = crate::doc::render(&project, &verification, file.as_deref())?;
            match out {
                Some(target) => {
                    if let Some(parent) = target.parent().filter(|p| !p.as_os_str().is_empty()) {
                        std::fs::create_dir_all(parent).map_err(|e| format!("cannot create {}: {e}", parent.display()))?;
                    }
                    std::fs::write(&target, html).map_err(|e| format!("cannot write {}: {e}", target.display()))?
                }
                None => print!("{html}"),
            }
            Ok(false)
        }
        Command::Lsp => crate::lsp::run().map(|()| false),
    }
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
