//! `trion verify`: the formal verification of a package.
//!
//! One analysis decides whether the contracts of the package can all hold,
//! and an external prover is asked each question that the analysis decided:
//! no result rests on the built-in solver alone. Around them stand the
//! sources of the statements and the checks that the settings ask for: the
//! properties of the reading, and the stability of the outcomes when a bound
//! is raised. Each is a gate; a package is verified when no gate fails.
//!
//! Two gates stand for what a result means and not for how it was found.
//! `meaning` fails while a part of a normative statement is accepted and
//! has no meaning rule: a result about the rest is no result about the
//! statement. `claims` fails unless each required claim is proved, and
//! proved of something: a claim that holds because nothing is in its range
//! counts for nothing. What `verified` covers is written out with it: the
//! claims, the bounds of the analysis, and what was not examined.

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
    /// A saved report of an earlier verification: the result of this one
    /// must be about the same subject.
    pub against: Option<PathBuf>,
}

/// What a result is a result about: the texts, the rules that read them,
/// the programs that decided and checked, and the settings. A result about
/// one subject says nothing about another: a saved result, a saved proof or
/// a cache entry is used only where the keys are the same.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct Subject {
    /// The digest of each file of the package and of its dependencies.
    pub revision: String,
    /// The version of the meaning rules that read the statements.
    pub semantics: &'static str,
    /// The version of the command, of the analysis and of the search.
    pub tool: &'static str,
    /// The version of the rules that the independent checker implements.
    pub checker: &'static str,
    pub trace_length: usize,
    pub scope: usize,
    pub decisions: Option<u64>,
    pub properties: bool,
    pub stability: bool,
    pub prover: Vec<String>,
    /// The digest of the fields above.
    pub key: String,
}

impl Subject {
    fn of(project: &Project, settings: &Settings) -> Subject {
        let mut subject = Subject {
            revision: project.revision(),
            semantics: trion_language::reading::typed::VERSION,
            tool: env!("CARGO_PKG_VERSION"),
            checker: trion_checker::derive::VERSION,
            trace_length: settings.bounds.trace_length,
            scope: settings.bounds.scope,
            decisions: settings.bounds.decisions,
            properties: settings.properties,
            stability: settings.stability,
            prover: settings.prover.clone(),
            key: String::new(),
        };
        subject.key = crate::digest::hex(format!("{}|{}|{}|{}|{}|{}|{:?}|{}|{}|{}", subject.revision, subject.semantics, subject.tool, subject.checker, subject.trace_length, subject.scope, subject.decisions, subject.properties, subject.stability, subject.prover.join(" ")));
        subject
    }

    /// The fields in which a saved report names another subject, or that
    /// the report names none.
    fn differs_from(&self, saved: &serde_json::Value) -> Vec<String> {
        // Each field is compared, and the key as well: a report whose key
        // is kept while a field is changed names another subject.
        let saved = &saved["outcome"]["subject"];
        let own = serde_json::to_value(self).unwrap_or_default();
        let mut fields: Vec<String> = ["revision", "semantics", "tool", "checker", "trace_length", "scope", "decisions", "properties", "stability", "prover"].iter().filter(|field| saved[**field] != own[**field]).map(|field| format!("{field} ({} there, {} here)", saved[*field], own[*field])).collect();
        if fields.is_empty() && saved["key"] != own["key"] {
            fields.push("the key, which is not the digest of the fields that the report states".to_string());
        }
        fields
    }
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
            against: None,
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

/// What keeps a package from being verified: the gate that failed, the
/// code of the finding, the statement that it is about, and the finding.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct Blocker {
    pub gate: &'static str,
    pub code: String,
    pub statement: Option<String>,
    pub message: String,
}

/// The outcome of a verification as a whole.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct Outcome {
    /// `true` only when no gate failed.
    pub verified: bool,
    /// What `verified` says and within which bounds, or that it says nothing.
    pub covers: String,
    /// What was not examined: a claim that nothing asked for is no claim that holds.
    pub not_examined: Vec<String>,
    /// What the package declares and no part of the verification checks: a
    /// result says nothing of it.
    pub declared: Vec<String>,
    pub blockers: Vec<Blocker>,
    /// What the result is about.
    pub subject: Subject,
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
    /// What the checks that stand apart from the analysis found.
    pub checked: crate::checks::Checked,
    pub weight: Weight,
    pub gates: Vec<Gate>,
    pub outcome: Outcome,
}

fn has_errors(diagnostics: &[Diagnostic]) -> bool {
    diagnostics.iter().any(|d| d.severity == Severity::Error)
}

impl Verification {
    /// The parts of sentences without a formal reading, the statements
    /// that constrain nothing and the qualities that nothing defines. Each
    /// is an error: nothing passes unread.
    pub(crate) fn unread(&self) -> Vec<Diagnostic> {
        unread_of(&self.analysis)
    }

    /// `true` when a gate failed: the package is not verified.
    pub(crate) fn failed(&self) -> bool {
        self.gates.iter().any(|gate| gate.state == "failed")
    }
}

/// The meaning obligations of an analysis as diagnostics: what a normative
/// statement says and no rule reads. Every view reports them as errors.
pub(crate) fn unread_of(analysis: &Analysis) -> Vec<Diagnostic> {
    let silence = &analysis.silence;
    silence.opaque.iter().chain(&silence.ungrounded).chain(&silence.inexpressible).cloned().collect()
}

/// What a verified package is verified of, or what keeps it from being verified.
/// What a package declares about itself that the verification takes as
/// stated: the reason why a diagram kind keeps the meaning of its elements,
/// and the agreement of sentence forms with another grammar.
fn declared_of(project: &Project) -> Vec<String> {
    let documents = || project.set.packages.iter().filter(|p| p.is_root).flat_map(|p| &p.documents);
    let kinds = documents().flat_map(|d| &d.diagram_kinds).map(|kind| format!("diagram kind {}: that the expansion of an element keeps its meaning (`preserves \"{}\"`) is stated by the package; each element is read as its expansion, and the statement is not checked", kind.name, kind.preserves));
    let claims = documents().flat_map(|d| &d.compatibility).map(|claim| format!("compatibility {}: that the sentence forms {} agree with source {} at revision `{}` is stated by the package; the source and its revision are compared, and the agreement of the forms is not checked", claim.name, claim.forms.join(", "), claim.source, claim.revision));
    kinds.chain(claims).collect()
}

fn outcome_of(analysis: &Analysis, gates: &[Gate], findings: &[(&'static str, &[Diagnostic])], subject: Subject, declared: Vec<String>) -> Outcome {
    use trion_verification::Verdict;
    let claims = &analysis.claims;
    let mut blockers: Vec<Blocker> = Vec::new();
    let failed = |name: &str| gates.iter().any(|gate| gate.name == name && gate.state == "failed");
    for (gate, diagnostics) in findings {
        // A warning fails the gates of the properties and of the stability, and no other.
        let counts = |d: &&Diagnostic| d.severity == Severity::Error || matches!(*gate, "properties" | "stability") || d.code == "consistency-unknown";
        if failed(gate) {
            blockers.extend(diagnostics.iter().filter(counts).map(|d| Blocker { gate, code: d.code.clone(), statement: d.refs.first().map(|r| r.id.clone()), message: d.message.clone() }));
        }
    }
    blockers.extend(claims.obligations.iter().map(|o| Blocker { gate: "meaning", code: o.code.clone(), statement: o.statement.as_ref().map(|r| r.id.clone()), message: o.message.clone() }));
    for claim in claims.unproved() {
        let subject = claim.subject.as_ref().map_or(String::new(), |subject| format!(" of {subject}"));
        let why = if claim.vacuous { "holds of nothing".to_string() } else { format!("is {}{}", claim.verdict.as_str(), claim.reason.as_ref().map_or(String::new(), |reason| format!(" ({reason})"))) };
        blockers.push(Blocker { gate: "claims", code: claim.claim.clone(), statement: None, message: format!("the claim `{}`{subject} {why}: {}", claim.claim, claim.statement) });
    }
    let verified = !gates.iter().any(|gate| gate.state == "failed");
    let not_examined: Vec<String> = claims.claims.iter().filter(|c| c.verdict == Verdict::NotRequested).map(|c| format!("{}: {}", c.claim, c.statement)).chain(gates.iter().filter(|gate| gate.state == "skipped").map(|gate| format!("gate {}", gate.name))).collect();
    let covers = if verified {
        let range = claims.claims.first().map_or(String::new(), |c| c.range.phrase());
        let proved: Vec<String> = claims.claims.iter().filter(|c| c.verdict == Verdict::Proved && c.subject.is_none()).map(|c| c.statement.clone()).collect();
        let checks = claims.claims.iter().filter(|c| c.claim == "property_entails" && c.subject.is_some() && c.verdict == Verdict::Proved).count();
        let checked = if checks == 0 { String::new() } else { format!("; {checks} stated properties follow") };
        // A scenario is one concrete behaviour: its judgement is about that behaviour and no bound.
        let scenarios = claims.claims.iter().filter(|c| c.claim == "scenario_satisfiable" && matches!(c.verdict, Verdict::Proved | Verdict::Refuted)).count();
        let judged = if scenarios == 0 { String::new() } else { format!("; {scenarios} scenarios are judged as expected, each alike by the reference evaluator and by the formulas of the reading") };
        format!("within {range}: {}{checked}; no result is lifted beyond these bounds{judged}", proved.join("; "))
    } else {
        "nothing: a gate failed, and no claim of the package is shown as verified".to_string()
    };
    Outcome { verified, covers, not_examined, declared, blockers, subject }
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
    let mut analysis = analyze(&project.set, &options);
    let mut checked = crate::checks::run(project, &mut analysis);
    let mut diagnostics: Vec<Diagnostic> = project.diagnostics.iter().chain(&analysis.diagnostics).cloned().collect();
    // A saved result is a result about its own subject: where it names
    // another text, another version of the rules or of the programs, or
    // other settings, it says nothing about this verification.
    let subject = Subject::of(project, settings);
    if let Some(path) = &settings.against {
        let saved = std::fs::read_to_string(path).map_err(|e| format!("cannot read {}: {e}", path.display())).and_then(|text| serde_json::from_str::<serde_json::Value>(&text).map_err(|e| format!("{} is no report: {e}", path.display())));
        match saved {
            Err(message) => diagnostics.push(Diagnostic::error("result-stale", format!("the saved result cannot be compared: {message}"), Vec::new())),
            Ok(saved) => {
                let fields = subject.differs_from(&saved);
                if !fields.is_empty() {
                    diagnostics.push(Diagnostic::error("result-stale", format!("the saved result at {} is about another subject, and nothing of it holds here: it differs in {}", path.display(), fields.join(", ")), Vec::new()));
                }
            }
        }
    }
    let sources = sources::check(project);
    if let (Some(dir), Some(proof)) = (&settings.smt, &analysis.proof) {
        write_queries(dir, proof)?;
    }
    // A package that is not read as contracts has no question to ask.
    let prover = analysis.proof.as_ref().map_or_else(Vec::new, |proof| ask_prover(&settings.prover, proof));
    let mut properties = if settings.properties { check_properties(&project.set, &analysis, &options) } else { Vec::new() };
    // The reading and the meaning agree next to the scenarios as on them.
    if settings.properties && analysis.model.individuals.is_some() {
        let (variations, differing) = crate::checks::vary(project, &analysis);
        properties.extend(differing);
        checked.variations = Some(variations);
    }
    let stability = if settings.stability { check_stability(&project.set, &analysis, &options) } else { Vec::new() };
    let weight = Weight::of(&analysis, project);
    let state = |asked: bool, failed: bool| match (asked, failed) {
        (false, _) => "skipped",
        (true, true) => "failed",
        (true, false) => "passed",
    };
    let unread = !unread_of(&analysis).is_empty();
    // The external prover is asked whenever a question was decided: a
    // verification without its answers rests on the built-in solver alone,
    // and that is a failure and no skip.
    let prover_failed = analysis.proof.is_none() || has_errors(&prover);
    let gates = vec![
        // An unknown result is no success, and nothing passes unread.
        Gate { name: "check", state: state(true, has_errors(&diagnostics) || unread || analysis.has_unknown()) },
        // What a normative statement says and no rule reads.
        Gate { name: "meaning", state: state(true, !analysis.claims.obligations.is_empty()) },
        // Each required claim is proved, and proved of something.
        Gate { name: "claims", state: state(true, !analysis.claims.unproved().is_empty()) },
        // The reference evaluator and the formulas agree on each scenario,
        // and each scenario is judged as its author expects.
        Gate { name: "checker", state: state(checked.asked, has_errors(&checked.diagnostics)) },
        Gate { name: "sources", state: state(true, has_errors(&sources.diagnostics)) },
        Gate { name: "prover", state: state(true, prover_failed) },
        Gate { name: "properties", state: state(settings.properties, !properties.is_empty()) },
        Gate { name: "stability", state: state(settings.stability, !stability.is_empty()) },
    ];
    let outcome = outcome_of(&analysis, &gates, &[("check", &diagnostics), ("checker", &checked.diagnostics), ("sources", &sources.diagnostics), ("prover", &prover), ("properties", &properties), ("stability", &stability)], subject, declared_of(project));
    Ok(Verification { analysis, diagnostics, sources, prover, properties, stability, checked, weight, gates, outcome })
}
