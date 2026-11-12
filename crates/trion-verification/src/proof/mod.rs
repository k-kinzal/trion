//! What a result rests on, as data: the unrolled entries, the relations
//! between them, the environments of the questions, and for every question
//! of the inventory its outcome with the certificates of its row.
//!
//! The questions of a proof can be put to another solver
//! ([`Proof::query_groups`]).

pub(crate) mod smt;

pub use trion_solver::{Answer, Certificate, Justification, LinearDerivation, LinearSource, Literal, Quantity, Refutation, Side, Step, Witness, WitnessPart};
pub use trion_language::reading::ReaderQuery;
pub use smt::{Query, QueryGroup};

use trion_language::SpecRef;
use trion_solver::{Atom, Cmp, Formula};
use trion_solver::{Instance, Status};
use trion_language::reading::Obligation;
use std::sync::Arc;

/// A question that was asked, with its answer. The numbers name formulas of
/// the pool of the proof that holds the question.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Question {
    pub query: Vec<usize>,
    pub answer: Answer,
}

impl Question {
    pub(crate) fn ask(instance: &Instance, query: Vec<usize>) -> Self {
        let answer = instance.decide(&query);
        Self { query, answer }
    }

    pub fn status(&self) -> Status {
        self.answer.status
    }

    /// The formulas of the question.
    pub fn formulas(&self, pool: &[Formula]) -> Vec<Formula> {
        self.query.iter().map(|&id| pool[id].clone()).collect()
    }
}

/// Every finite limit under which the formulas of a result were built, as
/// the reader used them and not as they were asked for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UsedBounds {
    /// The moments of the unrolling; one more position, the rest, follows them.
    pub moments: usize,
    /// The individuals of each type, when a statement is read over individuals.
    pub individuals: Option<usize>,
    /// The decisions that the search for one part of a query may make.
    pub decisions: Option<u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntryKind {
    /// A hard constraint.
    Hard,
    /// A permission: it stands for the admissibility of its response.
    Permission,
    /// A recommendation: breaking it leaves the specification consistent.
    Recommendation,
}

impl EntryKind {
    pub fn as_str(self) -> &'static str {
        match self {
            EntryKind::Hard => "hard",
            EntryKind::Permission => "permission",
            EntryKind::Recommendation => "recommendation",
        }
    }
}

/// One contract of the model, after unrolling.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// The index of the contract in the model.
    pub constraint: usize,
    /// The identity of its statement.
    pub statement: Option<SpecRef>,
    pub kind: EntryKind,
    /// The weight of a recommendation.
    pub weight: Option<u64>,
    /// The local reading: the contract before any relation to another
    /// statement is applied, and the temporal shape of the statement.
    pub local_assume: Formula,
    pub local_guarantee: Formula,
    pub temporal: Option<Obligation>,
    /// The formula over the trace, with every relation applied.
    pub formula: usize,
    /// The condition that the statement states, at the first moment.
    pub condition: Option<usize>,
}

/// A relation between entries. It is already applied in the formulas, and it
/// removes no entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Relation {
    /// `overrides`, `default`, `narrows` or `refinement`.
    pub kind: String,
    /// The statement whose formula the relation changes: the one that
    /// yields, or the one that its details stand for.
    pub subject: SpecRef,
    /// The statements that the relation rests on.
    pub rests_on: Vec<SpecRef>,
    /// The questions that the reader asked to establish the relation, each
    /// with the certificate of its answer.
    pub queries: Vec<ReaderQuery>,
}

/// The outcome of the status question, or of the status of an example.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatusOutcome {
    /// A witness of B ∧ H.
    Satisfiable { witness: Question },
    /// Every member is in H; a refutation of B ∧ M with no condition forced.
    /// A set that is called minimal has, for each member, a witness of
    /// B ∧ M without that member.
    Unsatisfiable { members: Vec<usize>, refutation: Question, minimal: Option<Vec<Question>> },
    Unknown,
}

impl StatusOutcome {
    pub fn status(&self) -> Status {
        match self {
            StatusOutcome::Satisfiable { .. } => Status::Satisfiable,
            StatusOutcome::Unsatisfiable { .. } => Status::Unsatisfiable,
            StatusOutcome::Unknown => Status::Unknown,
        }
    }
}

/// A recommendation that is not followed, with the set that holds it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dropped {
    pub entry: usize,
    /// The reported set: entries of H and of R, the dropped one among them.
    pub members: Vec<usize>,
    /// A refutation of B ∧ M.
    pub refutation: Question,
}

/// That no set of recommendations weighs more than the kept one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Greatest {
    /// The weights of the kept recommendations add up to this.
    pub weight: u64,
    /// The formulas of S(weight + 1), in the pool.
    pub heavier: Vec<usize>,
    /// A refutation of B ∧ H ∧ S(weight + 1).
    pub refutation: Question,
}

/// The outcome of the recommendations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Recommendations {
    /// R′: the recommendations that are followed.
    pub kept: Vec<usize>,
    /// A witness of B ∧ H ∧ R′.
    pub witness: Question,
    pub dropped: Vec<Dropped>,
    /// Present when R′ is reported as the set of greatest weight and the
    /// claim is certified.
    pub greatest: Option<Greatest>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConditionOutcome {
    /// A witness of B ∧ H ∧ R_e ∧ c.
    NoConflict { witness: Question },
    /// A refutation of B ∧ c: the condition cannot occur in any environment.
    Unreachable { refutation: Question },
    /// A witness of B ∧ c; every member is in H; a refutation of B ∧ M ∧ c.
    Conflict { reachable: Question, members: Vec<usize>, refutation: Question, minimal: Option<Vec<Question>> },
    /// A witness of B ∧ H ∧ c; every member is in H or in R_e; a refutation of B ∧ M ∧ c.
    RecommendationConflict { possible: Question, members: Vec<usize>, refutation: Question, minimal: Option<Vec<Question>> },
    Unknown,
}

impl ConditionOutcome {
    pub fn name(&self) -> &'static str {
        match self {
            ConditionOutcome::NoConflict { .. } => "no-conflict",
            ConditionOutcome::Unreachable { .. } => "unreachable",
            ConditionOutcome::Conflict { .. } => "conflict",
            ConditionOutcome::RecommendationConflict { .. } => "recommendation-conflict",
            ConditionOutcome::Unknown => "unknown",
        }
    }
}

/// The outcome of the condition of one entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConditionClaim {
    pub entry: usize,
    pub outcome: ConditionOutcome,
}

/// The environment of a check, a comparison, a choice or an example: its
/// bounds and the selected premises beside the background.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnvironmentRecord {
    pub name: String,
    /// `check`, `comparison`, `choice` or `example`.
    pub kind: String,
    pub bounds: UsedBounds,
    /// The background of the environment: what every question in it holds
    /// before the selected premises.
    pub background: Vec<usize>,
    pub premises: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckResult {
    /// A witness of E; a refutation of E ∧ L ∧ ¬R; a refutation of E ∧ R ∧ ¬L.
    /// A side is a list of formulas, and the negation of a side is refuted
    /// formula by formula: `forward` holds a refutation of E ∧ L ∧ ¬r for
    /// each formula r of R, and `backward` one of E ∧ R ∧ ¬l for each l of L.
    Proved { environment: Question, forward: Vec<Question>, backward: Vec<Question> },
    /// A witness of E ∧ L ∧ ¬R or of E ∧ R ∧ ¬L.
    Refuted { witness: Question },
    /// A refutation of E.
    EnvironmentInconsistent { refutation: Question },
    Unknown,
}

impl CheckResult {
    pub fn name(&self) -> &'static str {
        match self {
            CheckResult::Proved { .. } => "proved",
            CheckResult::Refuted { .. } => "refuted",
            CheckResult::EnvironmentInconsistent { .. } => "environment-inconsistent",
            CheckResult::Unknown => "unknown",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckClaim {
    pub environment: EnvironmentRecord,
    /// The formulas of each side.
    pub left: Vec<usize>,
    pub right: Vec<usize>,
    /// The negation of each formula of the right side and of the left side.
    pub not_right: Vec<usize>,
    pub not_left: Vec<usize>,
    pub result: CheckResult,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComparisonResult {
    /// A refutation of E ∧ Base.
    BaseInconsistent { refutation: Question },
    /// A witness of E ∧ Base; a refutation of E ∧ Base ∧ ¬c for each formula c of the candidate.
    Redundant { base: Question, refutations: Vec<Question> },
    /// A witness of E ∧ Base ∧ Candidate; a witness of E ∧ Base ∧ ¬c for a formula c of the candidate.
    Extension { with: Question, without: Question },
    /// A witness of E ∧ Base; a refutation of E ∧ Base ∧ Candidate.
    Conflict { base: Question, refutation: Question },
    Unknown,
}

impl ComparisonResult {
    pub fn name(&self) -> &'static str {
        match self {
            ComparisonResult::BaseInconsistent { .. } => "base-inconsistent",
            ComparisonResult::Redundant { .. } => "redundant",
            ComparisonResult::Extension { .. } => "extension",
            ComparisonResult::Conflict { .. } => "conflict",
            ComparisonResult::Unknown => "unknown",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComparisonClaim {
    /// The premises hold the conditions of the base that the comparison forces.
    pub environment: EnvironmentRecord,
    pub base: Vec<usize>,
    pub candidate: Vec<usize>,
    /// The conditions of the candidate that are forced with it.
    pub candidate_conditions: Vec<usize>,
    /// The negation of each formula of the candidate.
    pub not_candidate: Vec<usize>,
    /// The classification that an example expects.
    pub expected: Option<String>,
    pub result: ComparisonResult,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Exclusivity {
    /// For each two guards, a refutation of E ∧ gi ∧ gj.
    Exclusive { refutations: Vec<Question> },
    /// A witness of E ∧ gi ∧ gj.
    Overlap { first: usize, second: usize, witness: Question },
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Coverage {
    /// A refutation of E ∧ ¬g1 ∧ … ∧ ¬gm.
    Covered { refutation: Question },
    /// A witness of E ∧ ¬g1 ∧ … ∧ ¬gm.
    Missing { witness: Question },
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChoiceClaim {
    pub environment: EnvironmentRecord,
    pub statement: String,
    pub after: String,
    pub guards: Vec<usize>,
    /// ¬g1 ∧ … ∧ ¬gm, as a formula of the pool.
    pub none: usize,
    pub otherwise: bool,
    pub exclusive: Exclusivity,
    /// A choice with `otherwise` is covered by its reading.
    pub covered: Option<Coverage>,
}

/// A consistency example: the rows of the status, in the environment of the example.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExampleClaim {
    pub name: String,
    pub expected: String,
    pub bounds: UsedBounds,
    /// The formulas of the example's own environment.
    pub pool: Arc<Vec<Formula>>,
    pub background: Vec<usize>,
    /// The formulas of its hard constraints.
    pub hard: Vec<usize>,
    pub status: StatusOutcome,
    /// When the status is satisfiable: one outcome for the condition of
    /// each entry that has one.
    pub conditions: Vec<ConditionClaim>,
    /// When the status is satisfiable and no condition alone is a conflict:
    /// the questions about the situations in which conditions hold together.
    pub situations: Vec<(String, Question)>,
}

impl ExampleClaim {
    /// Every question that the verdict of the example rests on.
    pub fn questions(&self) -> Vec<&Question> {
        let mut out = Vec::new();
        of_status(&self.status, &mut out);
        self.conditions.iter().for_each(|claim| of_condition(claim, &mut out));
        out.extend(self.situations.iter().map(|(_, question)| question));
        out
    }
}

/// The questions of a status.
fn of_status<'a>(status: &'a StatusOutcome, out: &mut Vec<&'a Question>) {
    match status {
        StatusOutcome::Satisfiable { witness } => out.push(witness),
        StatusOutcome::Unsatisfiable { refutation, minimal, .. } => {
            out.push(refutation);
            out.extend(minimal.iter().flatten());
        }
        StatusOutcome::Unknown => {}
    }
}

/// The questions of the outcome of a condition.
fn of_condition<'a>(claim: &'a ConditionClaim, out: &mut Vec<&'a Question>) {
    match &claim.outcome {
        ConditionOutcome::NoConflict { witness } => out.push(witness),
        ConditionOutcome::Unreachable { refutation } => out.push(refutation),
        ConditionOutcome::Conflict { reachable: first, refutation, minimal, .. } | ConditionOutcome::RecommendationConflict { possible: first, refutation, minimal, .. } => {
            out.push(first);
            out.push(refutation);
            out.extend(minimal.iter().flatten());
        }
        ConditionOutcome::Unknown => {}
    }
}

/// A finding of the report as a comparison of the model file: the premises
/// with the base have a witness, and with the candidate they are refuted.
/// `None` when the solver does not give both answers.
pub(crate) fn finding(instance: &Instance, name: String, bounds: UsedBounds, premises: Vec<usize>, base: Vec<usize>, candidate: Vec<usize>, expected: Option<&str>) -> Option<ComparisonClaim> {
    let with: Vec<usize> = premises.iter().chain(&base).copied().collect();
    let possible = Question::ask(instance, with.clone());
    if possible.status() != Status::Satisfiable {
        return None;
    }
    let refutation = Question::ask(instance, with.iter().chain(&candidate).copied().collect());
    if refutation.status() != Status::Unsatisfiable {
        return None;
    }
    let formulas = instance.formulas();
    let not_candidate = candidate.iter().map(|&id| instance.add(&Formula::Not(Box::new(formulas[id].clone())))).collect();
    let environment = EnvironmentRecord { name, kind: "comparison".to_string(), bounds, background: Vec::new(), premises };
    Some(ComparisonClaim { environment, base, candidate, candidate_conditions: Vec::new(), not_candidate, expected: expected.map(str::to_string), result: ComparisonResult::Conflict { base: possible, refutation } })
}

/// A claim that the report makes from solver answers and whose certificate
/// is missing: it is printed as `not certified` and counts for nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Uncertified {
    pub kind: String,
    pub subject: String,
}

/// Every kind of claim that a report can make from solver answers, and
/// whether the inventory has a row for it.
pub const CLAIM_KINDS: [(&str, bool); 14] = [
    ("status", true),
    ("conflict-set-minimal", true),
    ("recommendations-followed", true),
    ("recommendations-greatest-weight", true),
    ("condition", true),
    ("check", true),
    ("comparison", true),
    ("consistency-example", true),
    ("choice-exclusive", true),
    ("choice-covered", true),
    ("reader-query", true),
    ("situations", true),
    ("condition-unreachable", true),
    ("shape-violation", true),
];

/// What a result of an analysis rests on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof {
    /// Every formula that a question of this proof names, by its number.
    pub pool: Arc<Vec<Formula>>,
    pub bounds: UsedBounds,
    /// The background: the axioms of the model at every moment, what the
    /// terms mean, and the order of the times of the moments.
    pub background: Vec<usize>,
    pub entries: Vec<Entry>,
    pub relations: Vec<Relation>,
    pub status: StatusOutcome,
    /// Present when the status is satisfiable and the package has recommendations.
    pub recommendations: Option<Recommendations>,
    /// Present when the status is satisfiable: one outcome for the
    /// condition of each entry of H or of R that has one.
    pub conditions: Vec<ConditionClaim>,
    pub checks: Vec<CheckClaim>,
    pub comparisons: Vec<ComparisonClaim>,
    pub choices: Vec<ChoiceClaim>,
    pub examples: Vec<ExampleClaim>,
    /// The questions about the situations in which conditions hold
    /// together, each with its name: for a conflict, that its conditions
    /// hold together and that the statements cannot all be kept under them;
    /// without one, that the statements are kept in each largest situation
    /// and that every situation lies within a largest one.
    pub answered: Vec<(String, Question)>,
    pub uncertified: Vec<Uncertified>,
}

impl Proof {
    /// Every question of this proof over its own pool, for a checker.
    pub fn questions(&self) -> Vec<&Question> {
        let mut out: Vec<&Question> = Vec::new();
        of_status(&self.status, &mut out);
        out.extend(self.answered.iter().map(|(_, question)| question));
        if let Some(recommendations) = &self.recommendations {
            out.push(&recommendations.witness);
            out.extend(recommendations.dropped.iter().map(|d| &d.refutation));
            out.extend(recommendations.greatest.iter().map(|g| &g.refutation));
        }
        self.conditions.iter().for_each(|claim| of_condition(claim, &mut out));
        for claim in &self.checks {
            match &claim.result {
                CheckResult::Proved { environment, forward, backward } => {
                    out.push(environment);
                    out.extend(forward.iter().chain(backward));
                }
                CheckResult::Refuted { witness } => out.push(witness),
                CheckResult::EnvironmentInconsistent { refutation } => out.push(refutation),
                CheckResult::Unknown => {}
            }
        }
        for claim in &self.comparisons {
            match &claim.result {
                ComparisonResult::BaseInconsistent { refutation } => out.push(refutation),
                ComparisonResult::Redundant { base, refutations } => {
                    out.push(base);
                    out.extend(refutations);
                }
                ComparisonResult::Conflict { base, refutation } => out.extend([base, refutation]),
                ComparisonResult::Extension { with, without } => out.extend([with, without]),
                ComparisonResult::Unknown => {}
            }
        }
        for claim in &self.choices {
            match &claim.exclusive {
                Exclusivity::Exclusive { refutations } => out.extend(refutations),
                Exclusivity::Overlap { witness, .. } => out.push(witness),
                Exclusivity::Unknown => {}
            }
            match &claim.covered {
                Some(Coverage::Covered { refutation }) => out.push(refutation),
                Some(Coverage::Missing { witness }) => out.push(witness),
                _ => {}
            }
        }
        out
    }
}

/// The outcome of the status over the hard formulas: a witness, or a
/// refuted subset with what shows that it is minimal.
pub(crate) fn status_outcome(instance: &Instance, background: &[usize], hard: &[(usize, usize)]) -> StatusOutcome {
    let with = |members: &[(usize, usize)]| -> Vec<usize> { background.iter().copied().chain(members.iter().map(|(_, formula)| *formula)).collect() };
    let whole = Question::ask(instance, with(hard));
    match whole.status() {
        Status::Satisfiable => StatusOutcome::Satisfiable { witness: whole },
        Status::Unknown => StatusOutcome::Unknown,
        Status::Unsatisfiable => {
            let (members, minimal) = shrink(instance, hard, &|members| with(members));
            let refutation = Question::ask(instance, with(&members));
            StatusOutcome::Unsatisfiable { members: members.iter().map(|(entry, _)| *entry).collect(), refutation, minimal }
        }
    }
}

/// Removes members while the query stays refuted. With the set come, when
/// it is minimal, the witnesses of the query without each member.
fn shrink(instance: &Instance, members: &[(usize, usize)], query: &dyn Fn(&[(usize, usize)]) -> Vec<usize>) -> (Vec<(usize, usize)>, Option<Vec<Question>>) {
    let mut core = members.to_vec();
    let mut at = 0;
    while at < core.len() {
        let removed = core.remove(at);
        if instance.decide(&query(&core)).status != Status::Unsatisfiable {
            core.insert(at, removed);
            at += 1;
        }
    }
    let mut witnesses = Vec::new();
    for skip in 0..core.len() {
        let without: Vec<(usize, usize)> = core.iter().enumerate().filter(|(n, _)| *n != skip).map(|(_, m)| *m).collect();
        let question = Question::ask(instance, query(&without));
        if question.status() != Status::Satisfiable {
            return (core, None);
        }
        witnesses.push(question);
    }
    (core, Some(witnesses))
}

/// What the inventory needs to know of one entry.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Member {
    pub entry: usize,
    pub formula: usize,
    pub condition: Option<usize>,
    pub recommendation: bool,
    pub weight: u64,
}

/// The formulas of S(v): recommendations of a total weight of `v` or more
/// are followed. Each recommendation r has one quantity between 0 and 1;
/// `x_r ≥ 1` implies r; the sum of weight(r) · x_r is `v` or more.
pub(crate) fn heavier(recommendations: &[(usize, Formula, u64)], v: u64) -> Vec<Formula> {
    let unit = "";
    let name = |entry: usize| format!("followed#{entry}");
    let bound = |entry: usize, cmp: Cmp, n: i64| Formula::Atom(Atom::Num { attr: name(entry), unit: unit.to_string(), cmp, n });
    let mut out = Vec::new();
    for (entry, formula, _) in recommendations {
        out.push(bound(*entry, Cmp::Ge, 0));
        out.push(bound(*entry, Cmp::Le, 1));
        out.push(Formula::implies(bound(*entry, Cmp::Ge, 1), formula.clone()));
    }
    let terms: Vec<(String, i64)> = recommendations.iter().map(|(entry, _, weight)| (name(*entry), i64::try_from(*weight).unwrap_or(i64::MAX))).collect();
    out.push(Formula::Atom(Atom::Lin { terms, unit: unit.to_string(), cmp: Cmp::Ge, n: i64::try_from(v).unwrap_or(i64::MAX) }));
    out
}

/// The greatest number of recommendations whose subsets are all compared.
const EXHAUSTIVE: usize = 12;

/// The outcome of the recommendations: the set that is followed, the set
/// that holds each recommendation outside it, and that no set weighs more.
pub(crate) fn recommendations(instance: &Instance, background: &[usize], members: &[Member]) -> Option<Recommendations> {
    let hard: Vec<usize> = members.iter().filter(|m| !m.recommendation).map(|m| m.formula).collect();
    let soft: Vec<&Member> = members.iter().filter(|m| m.recommendation).collect();
    if soft.is_empty() {
        return None;
    }
    let with = |chosen: &[&Member]| -> Vec<usize> { background.iter().chain(&hard).copied().chain(chosen.iter().map(|m| m.formula)).collect() };
    let holds = |chosen: &[&Member]| instance.decide(&with(chosen)).status == Status::Satisfiable;
    let weight_of = |chosen: &[&Member]| chosen.iter().map(|m| m.weight).sum::<u64>();
    let mut optimal = true;
    let kept: Vec<&Member> = if holds(&soft) {
        soft.clone()
    } else {
        // A recommendation that the hard constraints alone exclude is never kept.
        let free: Vec<&Member> = soft.iter().copied().filter(|m| holds(&[*m])).collect();
        if free.len() <= EXHAUSTIVE {
            let mut best: Vec<&Member> = Vec::new();
            for mask in 0u32..(1u32 << free.len()) {
                let chosen: Vec<&Member> = free.iter().enumerate().filter(|(bit, _)| mask & (1 << bit) != 0).map(|(_, m)| *m).collect();
                if weight_of(&chosen) > weight_of(&best) && holds(&chosen) {
                    best = chosen;
                }
            }
            best
        } else {
            optimal = false;
            let mut order = free.clone();
            order.sort_by_key(|m| std::cmp::Reverse(m.weight));
            let mut chosen: Vec<&Member> = Vec::new();
            for m in order {
                chosen.push(m);
                if !holds(&chosen) {
                    chosen.pop();
                }
            }
            chosen
        }
    };
    let witness = Question::ask(instance, with(&kept));
    if witness.status() != Status::Satisfiable {
        return None;
    }
    let mut dropped = Vec::new();
    for m in soft.iter().filter(|m| !kept.iter().any(|k| k.entry == m.entry)) {
        // The set that holds it: hard constraints and kept recommendations with it.
        let candidates: Vec<(usize, usize)> = members.iter().filter(|c| !c.recommendation || kept.iter().any(|k| k.entry == c.entry)).map(|c| (c.entry, c.formula)).collect();
        let query = |rest: &[(usize, usize)]| -> Vec<usize> { background.iter().copied().chain(rest.iter().map(|(_, f)| *f)).chain([m.formula]).collect() };
        let (core, _) = shrink(instance, &candidates, &query);
        let refutation = Question::ask(instance, query(&core));
        let mut set: Vec<usize> = core.iter().map(|(entry, _)| *entry).collect();
        set.push(m.entry);
        dropped.push(Dropped { entry: m.entry, members: set, refutation });
    }
    let weight = weight_of(&kept);
    let mut greatest = None;
    if !dropped.is_empty() && optimal {
        let formulas = instance.formulas();
        let weighted: Vec<(usize, Formula, u64)> = soft.iter().map(|m| (m.entry, formulas[m.formula].clone(), m.weight)).collect();
        let heavier: Vec<usize> = heavier(&weighted, weight + 1).iter().map(|f| instance.add(f)).collect();
        let refutation = Question::ask(instance, background.iter().chain(&hard).chain(&heavier).copied().collect());
        if refutation.status() == Status::Unsatisfiable {
            greatest = Some(Greatest { weight, heavier, refutation });
        }
    }
    Some(Recommendations { kept: kept.iter().map(|m| m.entry).collect(), witness, dropped, greatest })
}

/// The outcome of the condition of each entry of H or of R that has one.
pub(crate) fn conditions(instance: &Instance, background: &[usize], members: &[Member], kept: &[usize]) -> Vec<ConditionClaim> {
    let hard: Vec<(usize, usize)> = members.iter().filter(|m| !m.recommendation).map(|m| (m.entry, m.formula)).collect();
    let mut out = Vec::new();
    for member in members {
        let Some(condition) = member.condition else { continue };
        // R_e is R′ together with the entry itself when it is a recommendation.
        let advised: Vec<(usize, usize)> = members.iter().filter(|m| m.recommendation && (kept.contains(&m.entry) || m.entry == member.entry)).map(|m| (m.entry, m.formula)).collect();
        let with = |entries: &[(usize, usize)]| -> Vec<usize> { background.iter().copied().chain(entries.iter().map(|(_, f)| *f)).chain([condition]).collect() };
        let everything: Vec<(usize, usize)> = hard.iter().chain(&advised).copied().collect();
        let whole = Question::ask(instance, with(&everything));
        let outcome = match whole.status() {
            Status::Satisfiable => ConditionOutcome::NoConflict { witness: whole },
            Status::Unknown => ConditionOutcome::Unknown,
            Status::Unsatisfiable => {
                let alone = Question::ask(instance, with(&[]));
                match alone.status() {
                    Status::Unsatisfiable => ConditionOutcome::Unreachable { refutation: alone },
                    Status::Unknown => ConditionOutcome::Unknown,
                    Status::Satisfiable => {
                        let strict = Question::ask(instance, with(&hard));
                        match strict.status() {
                            Status::Unknown => ConditionOutcome::Unknown,
                            Status::Unsatisfiable => {
                                let (core, minimal) = shrink(instance, &hard, &|rest| with(rest));
                                let refutation = Question::ask(instance, with(&core));
                                ConditionOutcome::Conflict { reachable: alone, members: core.iter().map(|(entry, _)| *entry).collect(), refutation, minimal }
                            }
                            Status::Satisfiable => {
                                let (core, minimal) = shrink(instance, &everything, &|rest| with(rest));
                                let refutation = Question::ask(instance, with(&core));
                                ConditionOutcome::RecommendationConflict { possible: strict, members: core.iter().map(|(entry, _)| *entry).collect(), refutation, minimal }
                            }
                        }
                    }
                }
            }
        };
        out.push(ConditionClaim { entry: member.entry, outcome });
    }
    out
}
