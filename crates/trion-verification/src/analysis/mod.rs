//! Checking: finds contradictions, form violations and missing cases in the
//! composed model, and exposes how specifications relate.
//!
//! A missing specification can be asserted only when the whole domain is known.
//! Otherwise trion lists what is unrelated and leaves the finding to a person.

use trion_solver::{Instance, Lit, Status};
use trion_language::{Diagnostic, Severity, SpecRef};
use trion_language::document::{parse_document, parse_statement, Document, Meta, Package, Spec, SpecSet, VocabularyMode};
use trion_solver::Formula;
use crate::proof::{self, CheckClaim, CheckResult, ChoiceClaim, ComparisonClaim, ComparisonResult, Coverage, EnvironmentRecord, ExampleClaim, Exclusivity, Proof, Question, UsedBounds};
use trion_language::reading::{build_table, occurrences, Constraint, ConstraintKind, Lexicon, Model, VocabEntry};
use trion_language::syntax::ast::{CompNode, Core, Modal, VpGroup};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

mod blocks;
mod conflicts;
mod environment;
mod flows;
mod isolation;
mod properties;
mod situations;
mod stability;
mod structure;

pub use environment::{Control, Findings as EnvironmentFindings, Unrealizable};
pub use flows::GuardObligation;
pub use isolation::{temporal_forms, Isolation};
pub use properties::check as check_properties;
pub use stability::check as check_stability;

use blocks::{run_checks, run_examples, used_bounds, Environment, ExampleClaims, Operand};
use conflicts::{Authored, Conflicts};
use flows::check_flow_guards;
use isolation::{local_reading, relation_keys, unrolled_lines};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Default)]
pub struct RelationReport {
    /// Connected groups of specifications that share a term.
    pub components: Vec<Vec<String>>,
    /// Specifications that share no term with any other. A person reviews these.
    pub isolated: Vec<SpecRef>,
    /// Terms that appear in exactly one specification.
    pub single_use_terms: Vec<String>,
}

/// A requested proof and what the checker established.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CheckOutcome {
    pub name: String,
    pub relation: String,
    /// `proved`, `refuted` or `unknown`.
    pub result: String,
    pub file: String,
    pub line: usize,
}

/// A conformance example with its expected and observed results kept apart.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ExampleOutcome {
    pub name: String,
    pub kind: String,
    pub expected: String,
    pub observed: String,
    pub file: String,
    pub line: usize,
}

/// The moments of a trace when no other length is asked for.
pub(crate) const DEFAULT_TRACE_LENGTH: usize = 3;

/// The finite limits of an analysis. No decision limit means the search runs
/// to the end. The trace length is always finite: a result holds for the
/// traces of that many moments.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct Bounds {
    /// The number of branching decisions one solver query may make.
    pub decisions: Option<u64>,
    /// The number of moments of each trace that is examined.
    pub trace_length: usize,
    /// The number of individuals of each carrier that statements about
    /// individuals are read over.
    pub scope: usize,
}

impl Options {
    /// The options of a reading: the vocabulary, the model and the relations
    /// of a set, for views that show no verdict. No solver query is made.
    pub fn read_only() -> Self {
        Self { without_search: true, ..Self::default() }
    }
}

impl Default for Bounds {
    fn default() -> Self {
        Self { decisions: None, trace_length: DEFAULT_TRACE_LENGTH, scope: trion_language::reading::DEFAULT_SCOPE }
    }
}

/// What an analysis is run with, apart from the specifications.
///
/// The default decides everything within the default bounds;
/// [`Options::read_only`] reads the statements and asks the solver nothing.
#[derive(Debug, Clone, Default)]
pub struct Options {
    /// The finite limits of every solver query. The default has none.
    pub bounds: Bounds,
    /// The revision of the analysed specification, when the caller knows it.
    pub subject_revision: Option<String>,
    /// Reads the statements and builds the vocabulary and the model, and asks
    /// the solver nothing. The consistency result is then `unknown`.
    pub without_search: bool,
    /// Decides every question of the inventory and keeps its outcome with
    /// the certificates of its row.
    pub certificates: bool,
    /// With `certificates`: keeps the entries, the background and the
    /// relations of the proof, and decides no question of the inventory.
    pub outline: bool,
}

/// The semantic profile every result of this edition is established under.
pub(crate) const SEMANTIC_PROFILE: &str = "trion contracts over bounded traces with integer intervals";
/// How every result of this edition is established.
pub(crate) const METHOD: &str = "Tseitin encoding, DPLL search over atoms with learned clauses and linear integer arithmetic; each answer with a witness or a refutation; conflict sets by deletion";

/// The consistency of a specification, with what the claim rests on.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ConsistencyResult {
    /// Whether a behaviour keeps every hard constraint: exactly one of
    /// `satisfiable`, `unsatisfiable` and `unknown`.
    pub status: Status,
    /// `consistent`, `inconsistent` or `unknown`. A specification is
    /// consistent when, in each situation that its statements without
    /// normative force allow, the statements whose conditions hold can all
    /// be kept: a satisfiable specification can be inconsistent.
    pub verdict: String,
    /// How far the situations in which several conditions hold together
    /// were examined; absent when a conflict was found before them.
    pub situations: Option<String>,
    pub subject_revision: Option<String>,
    /// What every interpretation is assumed to satisfy besides the statements.
    pub assumptions: Vec<String>,
    pub profile: String,
    pub method: String,
    /// The finite bounds of the analysis; no bound when the field is null.
    pub bounds: Bounds,
    /// `true` when every search behind the status ran to its end, so that the
    /// status holds without the bounds. A search that the bounds ended never
    /// yields `satisfiable` or `unsatisfiable`.
    pub exhaustive: bool,
    /// The most decisions that one query needed.
    pub peak_decisions: u64,
}

impl ConsistencyResult {
    pub fn is_satisfiable(&self) -> bool {
        self.status == Status::Satisfiable
    }

    pub fn is_unsatisfiable(&self) -> bool {
        self.status == Status::Unsatisfiable
    }

    /// `true` when the consistency is neither proved nor refuted.
    pub fn is_unknown(&self) -> bool {
        self.verdict == "unknown"
    }
}

/// One source element of a conflict, as its author wrote and scoped it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ConflictElement {
    pub reference: SpecRef,
    /// The enclosing sections and the conditions the element inherits from
    /// its enclosing blocks, outermost first.
    pub scopes: Vec<String>,
    /// The element with its inherited conditions written out.
    pub expansion: String,
    /// The identity each term of the element resolves to, with its kind.
    pub terms: Vec<String>,
}

/// One contract of the derivation of a conflict.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DerivationStep {
    /// The statement the contract comes from, or `background`.
    pub origin: String,
    pub assume: String,
    pub guarantee: String,
}

/// A reported conflict set with what supports it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ConflictExplanation {
    /// The code of the diagnostic this explains.
    pub code: String,
    /// The conditions under which the elements conflict, when there are any.
    pub condition: Option<String>,
    /// `true` only when no smaller subset of the elements conflicts.
    pub minimal: bool,
    pub elements: Vec<ConflictElement>,
    /// The contracts and background axioms the inconsistency follows from.
    pub derivation: Vec<DerivationStep>,
    /// The definitions that the elements refer to.
    pub definitions: Vec<SpecRef>,
}

/// A conditional statement that holds only because its condition cannot occur.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct VacuousCondition {
    pub reference: SpecRef,
    /// The condition that is unreachable.
    pub condition: String,
    /// `unreachable in every environment` or `unreachable under the other statements`.
    pub reason: String,
}

/// What the statements are known to cover, with the conditions that make a
/// statement hold emptily kept in view.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Default)]
pub struct CoverageExplanation {
    pub vacuous: Vec<VacuousCondition>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Analysis {
    pub diagnostics: Vec<Diagnostic>,
    /// The consistency of the hard constraints.
    pub consistency: ConsistencyResult,
    /// An explanation of every reported conflict set.
    pub conflicts: Vec<ConflictExplanation>,
    pub coverage: CoverageExplanation,
    /// The proof obligation of every flow choice. A status of unsatisfiable
    /// means that the overlap or the gap was refuted.
    pub guards: Vec<GuardObligation>,
    pub vocabulary: BTreeMap<String, VocabEntry>,
    pub relations: RelationReport,
    pub model: Model,
    /// The outcome of every `check` block.
    pub checks: Vec<CheckOutcome>,
    /// The outcome of every `example` block.
    pub examples: Vec<ExampleOutcome>,
    /// The opaque readings and the ungrounded statements: what the
    /// specification says without constraining anything.
    pub silence: trion_language::reading::Silence,
    /// The recommendations to keep when recommendations cannot all be followed.
    pub preference: Option<trion_language::reading::Preference>,
    /// Who controls each actor, and the guarantees that no system can keep.
    pub environment: crate::analysis::environment::Findings,
    /// How names resolve, for tools that ask what a word refers to.
    #[serde(skip)]
    pub lexicon: Lexicon,
    /// What the result rests on: the unrolled entries, the relations, the
    /// environments and the outcome of every question with its certificates.
    #[serde(skip)]
    pub proof: Option<Proof>,
}

impl Analysis {
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.severity == Severity::Error)
    }

    /// Whether a result of this analysis is neither proved nor refuted: the
    /// consistency, a check or an example. Such a result is no success.
    pub fn has_unknown(&self) -> bool {
        self.consistency.is_unknown() || self.checks.iter().any(|c| c.result == "unknown") || self.examples.iter().any(|e| e.observed == "unknown")
    }
}

/// What every interpretation is assumed to satisfy besides the statements.
fn assumptions(model: &Model) -> Vec<String> {
    let mut out = vec![
        "an attribute holds at most one of its values at a time".to_string(),
        "time is a trace of moments: a state holds at a moment, an event occurs at a moment and an action completes at a moment".to_string(),
        "a response to a trigger completes at a later moment, and a state that it requires holds at the next moment".to_string(),
        "after the last moment stands the rest of the trace: a state holds there when it holds throughout the rest, an action completes there when it completes at some moment of the rest, and no state excludes another there".to_string(),
        "a trigger and its response are never read at one moment: a response to an event of the rest completes later in the rest, and a state that a trigger requires at a moment of the rest is not stated".to_string(),
        "the abstraction claim: every trace of at least as many moments, over domains of the same size, that satisfies the statements gives a model of the unrolled formulas; it is assumed and not proved, and no result holds beyond its bounds".to_string(),
        "each moment has a time, and a later moment is never earlier: a deadline and a delay of a triggered action relate the moment of the trigger, or of the event that the sentence names, to the moment of the completion".to_string(),
        "the rest of the trace has one time for each action, the time of its first completion there; a completion and an occurrence that both lie in the rest are not ordered, and an order without an activation is read from the second moment on".to_string(),
        "an obligation without a deadline may be met in the rest of the trace: a bounded trace refutes it only through a prohibition or a deadline, and never proves that the action is done".to_string(),
        "the condition of each conditional statement is forced when its conflicts are sought".to_string(),
    ];
    if !model.closed_domains.is_empty() {
        out.push(format!("{} closed domains hold no value outside their enumerations", model.closed_domains.len()));
    }
    out.push(format!("{} background axioms", model.background.len()));
    out
}

/// The contracts of a model over a trace, with what the environment controls.
fn trace_of(set: &SpecSet, model: &Model, lex: &Lexicon, length: usize) -> (trion_language::reading::Trace, crate::analysis::environment::Control) {
    let mut trace = trion_language::reading::unroll(model, length);
    // What the environment does is not the system's to decide: a statement
    // about it is an assumption, and its event occurs only when it acts.
    let control = crate::analysis::environment::control(set, model, lex);
    for axiom in crate::analysis::environment::environment_events(model, &control) {
        trace.background.extend(trion_language::reading::at_every_moment(&axiom, length));
    }
    (trace, control)
}

/// The formulas that the consistency of a package is decided over.
pub(crate) struct Decided {
    /// The background at every moment.
    pub background: Vec<Formula>,
    /// Each contract over the trace: the identity of its statement, its
    /// formula, and whether it is a recommendation. The status is decided
    /// over the background and the contracts that are no recommendations.
    pub contracts: Vec<(String, Formula, bool)>,
}

/// The formulas that the consistency of an analysed package is decided
/// over, at a trace of `length` moments.
pub(crate) fn decided(set: &SpecSet, analysis: &Analysis, length: usize) -> Decided {
    let (trace, _) = trace_of(set, &analysis.model, &analysis.lexicon, length);
    let authored = Authored::new(set, &analysis.lexicon);
    let contracts = analysis.model.constraints.iter().zip(trace.groups).map(|(c, (formula, _))| (c.refs.first().map_or(String::new(), |r| r.id.clone()), formula, authored.is_recommendation(c))).collect();
    Decided { background: trace.background, contracts }
}

/// The formulas that the consistency of an analysed set is decided over, at
/// a trace of `length` moments, as an SMT-LIB script for an external solver.
pub fn smt2(set: &SpecSet, analysis: &Analysis, length: usize) -> String {
    let decided = decided(set, analysis, length);
    crate::proof::smt::decided_to_smt2(&decided.background, &decided.contracts)
}

/// The contracts of the model that are no axioms, as entries over the trace.
fn entries_of(model: &Model, inst: &Instance, authored: &Authored) -> Vec<proof::Entry> {
    let mut entries = Vec::new();
    for (index, c) in model.constraints.iter().enumerate() {
        if c.kind.is_axiom() {
            continue;
        }
        let statement = c.refs.first().cloned();
        let recommendation = authored.is_recommendation(c);
        let kind = if recommendation {
            proof::EntryKind::Recommendation
        } else if c.kind == ConstraintKind::Permission {
            proof::EntryKind::Permission
        } else {
            proof::EntryKind::Hard
        };
        let weight = recommendation.then(|| statement.as_ref().and_then(|r| authored.owner(r)).and_then(|(spec, _)| spec.weight).map_or(1, u64::from));
        let temporal = statement.as_ref().and_then(|r| model.temporal.iter().find(|o| o.statement.id == r.id)).cloned();
        entries.push(proof::Entry { constraint: index, statement, kind, weight, local_assume: trion_language::reading::authored_condition(model, c), local_guarantee: c.guarantee.clone(), temporal, formula: inst.group(index), condition: inst.guard(index).map(|g| g as usize) });
    }
    entries
}

/// What every question of the inventory holds: the background of the
/// instance and what the terms mean.
fn background_of(model: &Model, inst: &Instance) -> Vec<usize> {
    inst.background().iter().copied().chain((0..model.constraints.len()).filter(|&i| model.constraints[i].kind.is_vocabulary()).map(|i| inst.group(i))).collect()
}

/// What the inventory needs to know of each entry.
fn members_of(entries: &[proof::Entry]) -> Vec<proof::Member> {
    entries.iter().enumerate().map(|(n, e)| proof::Member { entry: n, formula: e.formula, condition: e.condition, recommendation: e.kind == proof::EntryKind::Recommendation, weight: e.weight.unwrap_or(1) }).collect()
}

/// The contracts of a model over a bounded trace as the solver is asked
/// them, and after them the condition of each contract that has one, while
/// its response is due: the second value gives the group of that condition.
fn encode(trace: &trion_language::reading::Trace, model: &Model, bounds: Bounds) -> (Instance, BTreeMap<usize, usize>) {
    let mut parts = trace.groups.clone();
    let mut standing: BTreeMap<usize, usize> = BTreeMap::new();
    for (index, condition) in trion_language::reading::standing_conditions(model, bounds.trace_length) {
        standing.insert(index, parts.len());
        parts.push((condition, None));
    }
    (Instance::new(&trace.background, &parts, bounds.decisions), standing)
}

/// The relations between the entries of a model: each yielding, and each
/// statement that its details stand for.
fn relations_of(model: &Model) -> Vec<proof::Relation> {
    let mut relations: Vec<proof::Relation> = model.priorities.iter().map(|p| proof::Relation { kind: p.kind.clone(), subject: p.yields.clone(), rests_on: vec![p.to.clone()], queries: p.queries.clone() }).collect();
    let mut detailed: BTreeMap<String, (SpecRef, Vec<SpecRef>)> = BTreeMap::new();
    for (detail, parents) in &model.refined {
        let Some(at) = model.constraints.iter().flat_map(|c| &c.refs).find(|r| r.id == *detail) else { continue };
        for parent in parents {
            detailed.entry(parent.id.clone()).or_insert_with(|| (parent.clone(), Vec::new())).1.push(at.clone());
        }
    }
    relations.extend(detailed.into_values().map(|(subject, rests_on)| proof::Relation { kind: "refinement".to_string(), subject, rests_on, queries: Vec::new() }));
    // What a statement about terms or individuals says about other statements.
    relations.extend(model.applied.iter().map(|a| proof::Relation { kind: a.kind.clone(), subject: a.subject.clone(), rests_on: a.rests_on.clone(), queries: Vec::new() }));
    relations
}

/// Analyses a specification set: reads its statements as contracts and
/// decides, within the bounds of the options, whether they can all hold.
pub fn analyze(set: &SpecSet, options: &Options) -> Analysis {
    analyze_from(set, options, None)
}

impl Analysis {
    /// Analyses the set of this analysis again at other bounds. What does
    /// not depend on the bounds is taken from this run: the lexicon, the
    /// vocabulary, the relations and the report of unread parts, and the
    /// compiled model when the domain of individuals is the same. The
    /// diagnostics of reading are those of this run and are not repeated;
    /// the new run reports what the unrolling and the solver find.
    pub fn again(&self, set: &SpecSet, options: &Options) -> Analysis {
        analyze_from(set, options, Some((self, self.consistency.bounds)))
    }
}

fn analyze_from(set: &SpecSet, options: &Options, prior: Option<(&Analysis, Bounds)>) -> Analysis {
    let bounds = options.bounds;
    let mut diagnostics = Vec::new();
    let profile = std::env::var("TRION_PROFILE").is_ok();
    let clock = std::time::Instant::now();
    let lap = |what: &str| {
        if profile {
            eprintln!("profile: {:>8.3}s {what}", clock.elapsed().as_secs_f64());
        }
    };
    let (lex, vocabulary, model) = match prior {
        Some((base, base_bounds)) => {
            let model = if base_bounds.scope == bounds.scope { base.model.clone() } else { trion_language::reading::compile(set, &base.lexicon, bounds.scope) };
            lap("model taken from the earlier run");
            (base.lexicon.clone(), base.vocabulary.clone(), model)
        }
        None => {
            let lex = Lexicon::checked(set, &mut diagnostics);
            lap("scopes read");
            let (vocabulary, vocabulary_diagnostics) = build_table(set, &lex);
            lap("vocabulary built");
            diagnostics.extend(vocabulary_diagnostics);
            structure::check_identifiers(set, &mut diagnostics);
            diagnostics.extend(trion_language::reading::check_refinements(set));
            lap("meaning checked");
            let model = trion_language::reading::compile(set, &lex, bounds.scope);
            lap("model compiled");
            (lex, vocabulary, model)
        }
    };
    diagnostics.extend(trion_language::reading::check_priorities(set, &model));
    structure::find_unsupported(set, &model, &mut diagnostics);
    if options.without_search {
        let consistency = ConsistencyResult {
            status: Status::Unknown,
            verdict: "unknown".to_string(),
            situations: None,
            subject_revision: options.subject_revision.clone(),
            assumptions: assumptions(&model),
            profile: SEMANTIC_PROFILE.to_string(),
            method: "no search was run".to_string(),
            bounds,
            exhaustive: false,
            peak_decisions: 0,
        };
        let relations = structure::relate(set, &lex);
        let silence = trion_language::reading::silence(set, &model, &vocabulary, &lex);
        return Analysis { environment: crate::analysis::environment::Findings::default(), preference: None, silence, guards: Vec::new(), diagnostics, consistency, conflicts: Vec::new(), coverage: CoverageExplanation::default(), vocabulary, relations, model, checks: Vec::new(), examples: Vec::new(), lexicon: lex, proof: None };
    }
    // The contracts are read over a bounded trace: a statement set is
    // inconsistent when no trace of that length satisfies all of it.
    lap("compiled");
    let (trace, control) = trace_of(set, &model, &lex, bounds.trace_length);
    lap("unrolled");
    let (inst, standing) = encode(&trace, &model, bounds);
    lap("encoded");
    let authored = Authored::new(set, &lex);
    let before_conflicts = diagnostics.len();
    let found = conflicts::search(&model, &inst, &standing, &authored, &mut diagnostics);
    let verdict = found.verdict();
    let Conflicts { conflicts, coverage, unsatisfiable, unknown, refuted, situations, .. } = found;
    // The checker reports each contradiction, then each form violation
    // ([REASON-CHECKER-FLOW]); the missing cases follow below.
    diagnostics[before_conflicts..].sort_by_key(|d| d.code == "shape-violation");
    lap("conflicts searched");
    // A proved conflict settles the question; a search the bounds ended
    // settles nothing.
    let status = if unsatisfiable {
        Status::Unsatisfiable
    } else if unknown {
        Status::Unknown
    } else {
        Status::Satisfiable
    };
    if verdict == "unknown" {
        let limit = bounds.decisions.map_or(String::new(), |n| format!(" of {n} decisions for each query"));
        diagnostics.push(Diagnostic::warning("consistency-unknown", format!("the specification is neither proved consistent nor proved inconsistent within the analysis bounds{limit}"), vec![]));
    }
    let consistency = ConsistencyResult {
        status,
        verdict: verdict.to_string(),
        situations: situations.as_ref().map(|s| s.examined.clone()),
        subject_revision: options.subject_revision.clone(),
        assumptions: assumptions(&model),
        profile: SEMANTIC_PROFILE.to_string(),
        method: METHOD.to_string(),
        bounds,
        exhaustive: verdict != "unknown",
        peak_decisions: inst.peak_decisions(),
    };
    structure::check_model(set, &model, &lex, &mut diagnostics);
    diagnostics.extend(trion_language::reading::temporal_diagnostics(&model.temporal));
    lap("extensions and required forms checked");
    let mut choice_claims = Vec::new();
    let guards = check_flow_guards(set, &model, &lex, &inst, bounds, &mut diagnostics, &mut choice_claims);
    lap("flow guards checked");
    let mut check_claims = Vec::new();
    let checks = run_checks(set, &model, &inst, bounds, &mut diagnostics, &mut check_claims);
    lap("checks run");
    let mut example_claims = ExampleClaims::default();
    let examples = run_examples(set, &model, &inst, bounds, &mut diagnostics, &mut example_claims);
    lap("examples run");
    // The relations and the unread parts do not depend on the bounds.
    let (relations, silence) = match prior {
        Some((base, _)) => (base.relations.clone(), base.silence.clone()),
        None => {
            let relations = structure::relate(set, &lex);
            lap("relations read");
            let silence = trion_language::reading::silence(set, &model, &vocabulary, &lex);
            lap("silence read");
            (relations, silence)
        }
    };
    // The entries of the model over the trace, and what the inventory asks of them.
    let entries = entries_of(&model, &inst, &authored);
    let background = background_of(&model, &inst);
    let members = members_of(&entries);
    let advised = status == Status::Satisfiable && ((options.certificates && !options.outline) || diagnostics.iter().any(|d| d.code == "recommendation-violation"));
    let recommendations = if advised { proof::recommendations(&inst, &background, &members) } else { None };
    let reference = |entry: usize| entries[entry].statement.clone();
    let preference = recommendations.as_ref().filter(|r| !r.dropped.is_empty()).map(|r| {
        let weight = |chosen: &[usize]| chosen.iter().map(|&e| entries[e].weight.unwrap_or(1)).sum::<u64>();
        let dropped: Vec<usize> = r.dropped.iter().map(|d| d.entry).collect();
        trion_language::reading::Preference { kept: r.kept.iter().filter_map(|&e| reference(e)).collect(), dropped: dropped.iter().filter_map(|&e| reference(e)).collect(), kept_weight: weight(&r.kept), dropped_weight: weight(&dropped), optimal: r.greatest.is_some() }
    });
    lap("checks, examples and reports done");
    let unrealizable = crate::analysis::environment::unrealizable(&model, &control);
    diagnostics.extend(unrealizable.iter().map(|u| Diagnostic::warning("unrealizable", u.message.clone(), vec![u.statement.clone()])));
    let environment = crate::analysis::environment::Findings { control, unrealizable };
    let proof = options.certificates.then(|| {
        let hard: Vec<(usize, usize)> = members.iter().filter(|m| !m.recommendation).map(|m| (m.entry, m.formula)).collect();
        let outcome = if options.outline { proof::StatusOutcome::Unknown } else { proof::status_outcome(&inst, &background, &hard) };
        let satisfiable = outcome.status() == Status::Satisfiable;
        let kept: Vec<usize> = recommendations.as_ref().map(|r| r.kept.clone()).unwrap_or_default();
        let conditions = if satisfiable { proof::conditions(&inst, &background, &members, &kept) } else { Vec::new() };
        // What the report says from solver answers without a row of the inventory.
        let mut uncertified: Vec<proof::Uncertified> = Vec::new();
        let mut note = |kind: &str, subject: String| uncertified.push(proof::Uncertified { kind: kind.to_string(), subject });
        // Each finding that has no question of its own in the inventory is a
        // comparison of the model file: its premises have a witness, and with
        // what the finding names they are refuted.
        let used = used_bounds(&model, bounds);
        let mut findings: Vec<ComparisonClaim> = Vec::new();
        let mut answered: Vec<(String, Question)> = Vec::new();
        let mut certify = |name: String, premises: Vec<usize>, base: Vec<usize>, candidate: Vec<usize>, expected: Option<&str>| match proof::finding(&inst, name, used, premises, base, candidate, expected) {
            Some(claim) => {
                findings.push(claim);
                true
            }
            None => false,
        };
        let names = |groups: &[usize]| groups.iter().filter_map(|&g| model.constraints[g].refs.first()).map(|r| r.id.as_str()).collect::<Vec<_>>().join(" / ");
        // A refutation under forced conditions: the conditions hold together, and the named statements cannot.
        for (kind, forced, core) in refuted.iter().filter(|_| !options.outline) {
            if !certify(format!("{kind}: {}", names(core)), inst.query(&[], forced), Vec::new(), core.iter().map(|&g| inst.group(g)).collect(), Some("consistent extension")) {
                note(kind, names(core));
            }
        }
        // The situations: each conflict of conditions that hold together,
        // or that the statements can be kept in every situation.
        if let Some(situations) = situations.as_ref().filter(|_| !options.outline) {
            match situations.questions(&inst) {
                Some(questions) => answered = questions,
                None => note("situations", "the conditions that hold together".to_string()),
            }
        }
        if recommendations.as_ref().is_some_and(|r| !r.dropped.is_empty() && r.greatest.is_none()) {
            note("recommendations-greatest-weight", "the kept recommendations".to_string());
        }
        Proof {
            pool: std::sync::Arc::new(inst.formulas()),
            bounds: used_bounds(&model, bounds),
            background: background.clone(),
            relations: relations_of(&model),
            status: outcome,
            recommendations: recommendations.clone().filter(|_| satisfiable),
            conditions,
            checks: check_claims,
            comparisons: example_claims.comparisons.into_iter().chain(findings).collect(),
            choices: choice_claims,
            examples: example_claims.consistency,
            answered,
            uncertified,
            entries: entries.clone(),
        }
    });
    lap("proof built");
    Analysis { environment, preference, silence, guards, diagnostics, consistency, conflicts, coverage, vocabulary, relations, model, checks, examples, lexicon: lex, proof }
}
