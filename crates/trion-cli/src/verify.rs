//! `trion verify`: the formal verification of a package.
//!
//! One analysis decides whether the contracts of the package can all hold,
//! and an external prover is asked each question that the analysis decided:
//! no result rests on the built-in solver alone. Around them stand the
//! sources of the statements and the checks that the settings ask for: the
//! properties of the reading, and the stability of the outcomes when a bound
//! is raised. Each is a gate; a package is verified when no gate fails.

use crate::project::Project;
use crate::sources::{self, SourceReport};
use serde::Serialize;
use std::collections::BTreeSet;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use trion_language::{Diagnostic, Severity};
use trion_solver::Status;
use trion_verification::{analyze, check_properties, check_stability, Analysis, Bounds, Options, Proof};

/// How a package is verified: the manifest says it, and an argument of the
/// command takes the place of what it names.
#[derive(Debug, Clone)]
pub(crate) struct Settings {
    pub bounds: Bounds,
    pub properties: bool,
    pub stability: bool,
    /// The directory that the queries are written into as SMT-LIB.
    pub smt: Option<PathBuf>,
    /// The command of the external prover: it reads an SMT-LIB script on its
    /// standard input and prints one answer for each query.
    pub prover: Vec<String>,
}

/// The external prover of a package that names none.
const DEFAULT_PROVER: [&str; 2] = ["z3", "-in"];

impl Settings {
    /// The settings that the manifest of a project states.
    pub(crate) fn of(project: &Project) -> Settings {
        let stated = &project.manifest.verify;
        let default = Bounds::default();
        Settings {
            bounds: Bounds { decisions: stated.decision_limit, trace_length: stated.trace_length.unwrap_or(default.trace_length).max(2), scope: stated.scope.unwrap_or(default.scope).min(6) },
            properties: stated.properties,
            stability: stated.stability,
            smt: stated.smt.as_ref().map(|dir| project.root.join(dir)),
            prover: if stated.prover.is_empty() { DEFAULT_PROVER.map(str::to_string).to_vec() } else { stated.prover.clone() },
        }
    }
}

/// One gate of a verification with its state: `passed`, `failed`, or
/// `skipped` when the settings do not ask for it or nothing reached it.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct Gate {
    pub name: &'static str,
    pub state: &'static str,
}

/// How much a consistency result covers: the statements, the entries and
/// the atoms; the atoms that an axiom, a definition or the arithmetic
/// constrains; the terms by status; the parts without a reading and the
/// statements that constrain nothing.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct Weight {
    pub statements: usize,
    pub entries: usize,
    pub atoms: usize,
    pub constrained_atoms: usize,
    pub terms_defined: usize,
    pub terms_primitive: usize,
    pub terms_neither: usize,
    pub unread_parts: usize,
    pub ungrounded_statements: usize,
    /// The statements that only a `detailed by` line of an abstract
    /// statement grounds: they pass, and they relate to nothing else.
    pub grounded_only_through_detailed_by: usize,
}

impl Weight {
    fn of(analysis: &Analysis, project: &Project) -> Weight {
        let statements = project.all_specs().count();
        let primitives: BTreeSet<String> = project.set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.primitives).map(|p| p.name.to_lowercase()).collect();
        let extent = analysis.model.extent();
        // A term is defined by a definition, primitive by a declaration, or neither.
        let glossary = trion_language::glossary(&analysis.vocabulary);
        let bare = |term: &str| term.rsplit("::").next().unwrap_or(term).to_lowercase();
        let defined = glossary.iter().filter(|entry| entry.defined_at.is_some()).count();
        let primitive = glossary.iter().filter(|entry| entry.defined_at.is_none() && (entry.declared_at.is_some() || primitives.contains(&bare(&entry.term)))).count();
        Weight { statements, entries: extent.entries, atoms: extent.atoms, constrained_atoms: extent.constrained_atoms, terms_defined: defined, terms_primitive: primitive, terms_neither: glossary.len() - defined - primitive, unread_parts: analysis.silence.opaque.len(), ungrounded_statements: analysis.silence.ungrounded.len(), grounded_only_through_detailed_by: analysis.silence.refinement_only.len() }
    }

    pub(crate) fn line(&self) -> String {
        format!("{} statements, {} entries, {} atoms, of which an axiom, a definition or the arithmetic constrains {}; terms: {} defined, {} primitive, {} neither; {} parts without a reading, {} statements that constrain nothing, {} statements that only a `detailed by` line grounds", self.statements, self.entries, self.atoms, self.constrained_atoms, self.terms_defined, self.terms_primitive, self.terms_neither, self.unread_parts, self.ungrounded_statements, self.grounded_only_through_detailed_by)
    }
}

/// What verifying a package found.
pub(crate) struct Verification {
    pub analysis: Analysis,
    /// What loading and analysing the package reported.
    pub diagnostics: Vec<Diagnostic>,
    pub sources: SourceReport,
    /// Where the external prover did not answer as the built-in solver did.
    pub prover: Vec<Diagnostic>,
    pub properties: Vec<Diagnostic>,
    pub stability: Vec<Diagnostic>,
    pub weight: Weight,
    pub gates: Vec<Gate>,
}

fn has_errors(diagnostics: &[Diagnostic]) -> bool {
    diagnostics.iter().any(|d| d.severity == Severity::Error)
}

impl Verification {
    /// The parts of sentences without a formal reading and the statements
    /// that constrain nothing. Each is an error: nothing passes unread.
    pub(crate) fn unread(&self) -> Vec<Diagnostic> {
        self.analysis.silence.opaque.iter().chain(&self.analysis.silence.ungrounded).cloned().collect()
    }

    /// `true` when a gate failed: the package is not verified.
    pub(crate) fn failed(&self) -> bool {
        self.gates.iter().any(|gate| gate.state == "failed")
    }
}

fn answer_word(status: Status) -> &'static str {
    match status {
        Status::Satisfiable => "sat",
        Status::Unsatisfiable => "unsat",
        Status::Unknown => "unknown",
    }
}

/// Writes the queries of a result as SMT-LIB: `queries-N.smt2` for each pool
/// of formulas, and `queries.answers` with the answer of the built-in solver
/// and the name of each query, in the order of the scripts.
fn write_queries(dir: &Path, proof: &Proof) -> Result<(), String> {
    std::fs::create_dir_all(dir).map_err(|e| format!("cannot create {}: {e}", dir.display()))?;
    let mut answers = String::new();
    for (number, group) in proof.query_groups().iter().enumerate() {
        let path = dir.join(format!("queries-{number}.smt2"));
        std::fs::write(&path, group.script()).map_err(|e| format!("cannot write {}: {e}", path.display()))?;
        for query in &group.queries {
            answers.push_str(&format!("{} {}\n", answer_word(query.status), query.name));
        }
    }
    let path = dir.join("queries.answers");
    std::fs::write(&path, answers).map_err(|e| format!("cannot write {}: {e}", path.display()))
}

/// Runs the prover on one script and returns what it printed.
fn run_prover(command: &[String], script: &str) -> Result<String, String> {
    let (program, arguments) = command.split_first().ok_or("the prover has no command")?;
    let mut child = Command::new(program).args(arguments).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::null()).spawn().map_err(|e| format!("cannot run `{program}`: {e}"))?;
    let mut stdin = child.stdin.take();
    let text = script.to_string();
    // The prover answers while it reads: the script is written from a thread of its own.
    let writer = std::thread::spawn(move || {
        if let Some(stdin) = stdin.as_mut() {
            let _ = stdin.write_all(text.as_bytes());
        }
        drop(stdin);
    });
    let output = child.wait_with_output().map_err(|e| e.to_string())?;
    let _ = writer.join();
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

/// Asks the external prover each query of a result. An answer that differs
/// from that of the built-in solver is an error, and so are a prover that
/// does not answer and a query that the prover leaves open: no answer rests
/// on the built-in solver alone.
fn ask_prover(command: &[String], proof: &Proof) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let name = command.join(" ");
    let mut open = Vec::new();
    for group in proof.query_groups() {
        let printed = match run_prover(command, &group.script()) {
            Ok(printed) => printed,
            Err(message) => {
                out.push(Diagnostic::error("prover-failed", format!("the external prover did not run: {message}"), Vec::new()));
                return out;
            }
        };
        let answers: Vec<&str> = printed.lines().map(str::trim).filter(|line| matches!(*line, "sat" | "unsat" | "unknown")).collect();
        if answers.len() != group.queries.len() {
            out.push(Diagnostic::error("prover-failed", format!("`{name}` printed {} answers for {} queries: {}", answers.len(), group.queries.len(), printed.lines().find(|line| line.contains("error")).unwrap_or_default()), Vec::new()));
            return out;
        }
        for (query, answer) in group.queries.iter().zip(answers) {
            match (answer, query.status) {
                ("unknown", _) => open.push(query.name.clone()),
                (_, Status::Unknown) => {}
                (theirs, ours) if theirs != answer_word(ours) => out.push(Diagnostic::error("prover-differs", format!("the query `{}` is {} for the built-in solver and {theirs} for `{name}`", query.name, answer_word(ours)), Vec::new())),
                _ => {}
            }
        }
    }
    if !open.is_empty() {
        let shown: Vec<&str> = open.iter().take(5).map(String::as_str).collect();
        out.push(Diagnostic::error("prover-unknown", format!("`{name}` answered `unknown` for {} queries ({}{}): no prover outside trion decided them", open.len(), shown.join(", "), if open.len() > shown.len() { ", ..." } else { "" }), Vec::new()));
    }
    out
}

/// Verifies a project as its settings say.
pub(crate) fn verify(project: &Project, settings: &Settings) -> Result<Verification, String> {
    // The questions of the result are kept: the external prover is asked each.
    let options = Options { bounds: settings.bounds, subject_revision: Some(project.revision()), certificates: true, ..Options::default() };
    let analysis = analyze(&project.set, &options);
    let diagnostics: Vec<Diagnostic> = project.diagnostics.iter().chain(&analysis.diagnostics).cloned().collect();
    let sources = sources::check(project);
    if let (Some(dir), Some(proof)) = (&settings.smt, &analysis.proof) {
        write_queries(dir, proof)?;
    }
    // A package that is not read as contracts has no question to ask.
    let prover = analysis.proof.as_ref().map_or_else(Vec::new, |proof| ask_prover(&settings.prover, proof));
    let properties = if settings.properties { check_properties(&project.set, &analysis, &options) } else { Vec::new() };
    let stability = if settings.stability { check_stability(&project.set, &analysis, &options) } else { Vec::new() };
    let weight = Weight::of(&analysis, project);
    let state = |asked: bool, failed: bool| match (asked, failed) {
        (false, _) => "skipped",
        (true, true) => "failed",
        (true, false) => "passed",
    };
    let unread = !analysis.silence.opaque.is_empty() || !analysis.silence.ungrounded.is_empty();
    let gates = vec![
        // An unknown result is no success, and nothing passes unread.
        Gate { name: "check", state: state(true, has_errors(&diagnostics) || unread || analysis.has_unknown()) },
        Gate { name: "sources", state: state(true, has_errors(&sources.diagnostics)) },
        Gate { name: "prover", state: state(analysis.proof.is_some(), has_errors(&prover)) },
        Gate { name: "properties", state: state(settings.properties, !properties.is_empty()) },
        Gate { name: "stability", state: state(settings.stability, !stability.is_empty()) },
    ];
    Ok(Verification { analysis, diagnostics, sources, prover, properties, stability, weight, gates })
}
