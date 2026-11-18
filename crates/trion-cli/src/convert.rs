//! The conversion of a package: what `trion` reads from it and writes.
//!
//! A package is read without being decided: its statements are read as
//! contracts by responsibility, and its proof obligations are written down.
//! What does not conform to the language is an error; nothing here is a
//! proof, and a document does not wait for one.

use crate::project::Project;
use crate::sources::{self, SourceReport};
use trioc_cli::mmt::{Contract, Form};
use trion_language::{Diagnostic, Severity, SpecRef};
use trion_verification::{analyze, demonstrations, proof_obligations, stated_contracts, Analysis, Bounds, Control, ExampleOutcome, ObligationQuestion, Options, ProofObligation, ProofObligations, StatedContract};

/// What the conversion of a package read.
pub(crate) struct Converted {
    pub analysis: Analysis,
    /// The findings of loading and of reading the package, and of the
    /// examples that demonstrate the conversion: what does not conform to
    /// the language is an error.
    pub diagnostics: Vec<Diagnostic>,
    /// What the checker found of the reading: each finding is an error of
    /// the conversion.
    pub checker: Vec<Diagnostic>,
    pub sources: SourceReport,
    pub contracts: Vec<StatedContract>,
    pub control: Control,
    pub obligations: ProofObligations,
    /// What the package declares and nothing checks.
    pub declared: Vec<String>,
    /// The examples of syntax and of readings, which demonstrate the conversion.
    pub demonstrated: Vec<ExampleOutcome>,
    /// What the checker showed of the reading.
    pub checked: crate::checks::Demonstrated,
}

impl Converted {
    /// Every finding of the conversion: of reading, of the checker, of
    /// what no rule reads, and of the sources.
    pub(crate) fn all(&self) -> impl Iterator<Item = &Diagnostic> {
        let silence = &self.analysis.silence;
        self.diagnostics.iter().chain(&self.checker).chain(&silence.opaque).chain(&silence.ungrounded).chain(&silence.inexpressible).chain(&self.sources.diagnostics)
    }

    /// `true` when the package does not conform to the language.
    pub(crate) fn failed(&self) -> bool {
        self.all().any(|d| d.severity == Severity::Error)
    }

    /// The MMT form of the package.
    pub(crate) fn form(&self, project: &Project) -> Form {
        Form {
            package: project.manifest.package.name.clone(),
            revision: project.revision(),
            semantics: trion_language::reading::typed::VERSION.to_string(),
            tool: env!("CARGO_PKG_VERSION").to_string(),
            system: self.control.system.iter().cloned().collect(),
            environment: self.control.environment.iter().cloned().collect(),
            contracts: self
                .contracts
                .iter()
                .map(|c| Contract {
                    id: c.statement.id.clone(),
                    file: c.statement.file.clone(),
                    line: c.statement.line,
                    text: c.statement.text.clone(),
                    role: c.role.clone(),
                    parameters: c.parameters.clone(),
                    chosen: c.chosen.clone(),
                    assume: c.assume.clone(),
                    guarantee: c.guarantee.clone(),
                    timing: c.timing.clone(),
                    scope: match &c.scope {
                        None => trioc_cli::mmt::Scope::Unscoped,
                        Some(trion_verification::Scope::Document) => trioc_cli::mmt::Scope::Document,
                        Some(trion_verification::Scope::Block { head, file, line }) => trioc_cli::mmt::Scope::Block { head: head.clone(), file: file.clone(), line: *line },
                    },
                })
                .collect(),
            obligations: self.obligations.clone(),
        }
    }
}

/// What a package declares about itself that nothing checks: the reason
/// why a diagram kind keeps the meaning of its elements, and the agreement
/// of sentence forms with another grammar.
fn declared_of(project: &Project) -> Vec<String> {
    let documents = || project.set.packages.iter().filter(|p| p.is_root).flat_map(|p| &p.documents);
    let kinds = documents().flat_map(|d| &d.diagram_kinds).map(|kind| format!("diagram kind {}: that the expansion of an element keeps its meaning (`preserves \"{}\"`) is stated by the package; each element is read as its expansion, and the statement is not checked", kind.name, kind.preserves));
    let claims = documents().flat_map(|d| &d.compatibility).map(|claim| format!("compatibility {}: that the sentence forms {} agree with source {} at revision `{}` is stated by the package; the source and its revision are compared, and the agreement of the forms is not checked", claim.name, claim.forms.join(", "), claim.source, claim.revision));
    kinds.chain(claims).collect()
}

/// What `trion` and `trioc prove` report of a project together, as an
/// editor shows it: the analysis of the conversion, and its findings (of
/// loading, reading, the checker and the sources) with, where the package
/// conforms, the findings of the proof of its MMT form. What no rule reads
/// is in the analysis, and is not repeated here.
pub struct Findings {
    pub analysis: Analysis,
    pub diagnostics: Vec<Diagnostic>,
}

/// The findings of a project within the bounds of its manifest. A package
/// that does not conform is not proved, as `trion` writes no form for it.
pub fn findings(project: &Project) -> Findings {
    let stated = &project.manifest.verify;
    let default = Bounds::default();
    let bounds = Bounds { decisions: stated.decision_limit, trace_length: stated.trace_length.unwrap_or(default.trace_length).max(2), scope: stated.scope.unwrap_or(default.scope).min(6) };
    let converted = convert(project, bounds, false);
    let mut diagnostics: Vec<Diagnostic> = converted.diagnostics.iter().chain(&converted.checker).chain(&converted.sources.diagnostics).cloned().collect();
    if !converted.failed() {
        match trioc_cli::prove::prove(&converted.form(project), bounds.decisions, None, &[]) {
            Ok(proved) => diagnostics.extend(proved.diagnostics),
            Err(message) => diagnostics.push(Diagnostic::error("prover-failed", format!("the obligations of the MMT form were not proved: {message}"), Vec::new())),
        }
    }
    Findings { analysis: converted.analysis, diagnostics }
}

/// Converts a package within the bounds of its obligations. With
/// `properties`, the properties of the reader are examined as well:
/// context independence, relation locality, order independence, the round
/// trip, and the behaviours next to each scenario.
pub(crate) fn convert(project: &Project, bounds: Bounds, properties: bool) -> Converted {
    let options = Options { bounds, subject_revision: Some(project.revision()) };
    let analysis = analyze(&project.set, &options);
    let sources = sources::check(project);
    let mut diagnostics: Vec<Diagnostic> = project.diagnostics.iter().chain(&analysis.diagnostics).cloned().collect();
    // The conversion is demonstrated by the examples of syntax and of
    // readings: each observes what it expects, or the conversion is wrong.
    let (demonstrated, failed) = demonstrations(&project.set, bounds);
    diagnostics.extend(failed);
    let mut checker = Vec::new();
    let checked = crate::checks::demonstrate(project, &analysis, bounds.trace_length, properties, &mut checker);
    if properties {
        checker.extend(trion_verification::check_properties(&project.set, &analysis, &options));
    }
    let (contracts, control) = stated_contracts(&project.set, &analysis);
    // Responsibility follows the declaration of the system. A document that
    // declares none is read with the actors that its requirements speak
    // about, and a reader is told which they are: a wrong boundary changes
    // the conclusion for the same statements and is not detected.
    if let Some(actors) = trion_verification::inferred_system(&project.set, &analysis).filter(|actors| !actors.is_empty()) {
        let named: Vec<String> = actors.iter().map(|a| a.rsplit("::").next().unwrap_or(a).to_string()).collect();
        diagnostics.push(Diagnostic::warning(
            "system-undeclared",
            format!("no actor is declared the system, so the system is taken to be {}: the actors whose actions the requirements speak about; declare it with `system {}`, and the others with `environment`", named.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", "), named.join(", ")),
            Vec::new(),
        ));
    }
    let mut obligations = proof_obligations(&project.set, &analysis, bounds.trace_length);
    // A block that names what is not there, or expects what no proof decides.
    diagnostics.append(&mut obligations.findings);
    scenarios(project, &analysis, &mut obligations, &mut diagnostics);
    Converted { declared: declared_of(project), analysis, diagnostics, checker, sources, contracts, control, obligations, demonstrated, checked }
}

/// The obligation of each scenario: the behaviour that it states keeps
/// every statement, or breaks one, as the author expects.
fn scenarios(project: &Project, analysis: &Analysis, obligations: &mut ProofObligations, diagnostics: &mut Vec<Diagnostic>) {
    let stated = trion_checker::Stated::of(&analysis.model);
    for doc in project.set.packages.iter().filter(|p| p.is_root).flat_map(|p| &p.documents) {
        let lex = analysis.lexicon.in_document(doc);
        for block in doc.scenarios.iter().filter(|b| !b.malformed) {
            let at = SpecRef { id: format!("scenario {}", block.name), file: block.file.clone(), line: block.line, text: format!("scenario {}", block.name) };
            let (Some(stated), Some(individuals)) = (&stated, &analysis.model.individuals) else {
                diagnostics.push(Diagnostic::error("scenario-unsupported", "a scenario is judged over individuals of declared types, and the package declares none: declare them, as in `individuals user, room`", vec![at]));
                continue;
            };
            let world = match trion_checker::scenario::world(block, individuals, &lex) {
                Ok(world) => world,
                Err(problems) => {
                    for problem in problems {
                        diagnostics.push(Diagnostic::error("scenario-invalid", problem.what, vec![SpecRef { line: problem.line, ..at.clone() }]));
                    }
                    continue;
                }
            };
            let moments = world.closed().moments.len();
            // The agreement of the meaning and the formulas on the behaviour
            // is shown by the checker; here the behaviour is a question.
            let comparison = stated.compare(&world);
            let question = match stated.question(&world) {
                Ok(question) => question,
                Err(trion_checker::Generated::NotComparable { atoms }) => {
                    diagnostics.push(Diagnostic::error("scenario-unsupported", format!("the formulas hold atoms that the behaviour does not fix ({}): a statement of the package is not read over individuals", atoms.iter().take(3).cloned().collect::<Vec<_>>().join(", ")), vec![at]));
                    continue;
                }
                Err(_) => continue,
            };
            let query: Vec<usize> = question.into_iter().map(|formula| {
                obligations.pool.push(formula);
                obligations.pool.len() - 1
            }).collect();
            let (question, expected) = match block.expect.as_str() {
                "forbidden" => (ObligationQuestion::Unsatisfiable { query }, "breaks a statement"),
                // `undefined`: the behaviour keeps every statement, and a
                // share has no value in it, as the reference evaluator finds.
                "undefined" if comparison.reference.undefined.is_empty() => {
                    diagnostics.push(Diagnostic::error("scenario-failed", "the scenario is expected to leave a share without a value, and each share has one in it".to_string(), vec![at]));
                    continue;
                }
                _ => (ObligationQuestion::Satisfiable { query }, "keeps every statement"),
            };
            obligations.obligations.push(ProofObligation {
                name: format!("scenario/{}", block.name),
                property: "scenario".to_string(),
                proposition: format!("exactly, of the behaviour of {moments} moments that the scenario states: it {expected}"),
                statements: Vec::new(),
                question,
            });
        }
    }
}
