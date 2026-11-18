//! No statement wins over another.
//!
//! A conjunction is monotonic: a general rule and its exception contradict
//! each other unless the general rule names the exception. A line that lets
//! one statement change the contract of another (`overrides [ID]`,
//! `default`, `weight N`) would give the specification a meaning that no
//! set of contracts has, so each is rejected (`priority-unsupported`), and
//! a general permission is not narrowed by a prohibition either: where both
//! apply they contradict.

use crate::document::SpecSet;
use crate::diagnostic::{Diagnostic, SpecRef};
use crate::document::Spec;
use crate::reading::model::{Constraint, ConstraintKind, Model};
use trion_solver::Formula;
use trion_solver::Answer;
use serde::Serialize;

/// One statement that yields to another.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Priority {
    /// The statement that does not apply where the other one does.
    pub yields: SpecRef,
    /// The statement that wins.
    pub to: SpecRef,
    /// `overrides` when the winner names the loser, `default` when the loser is a default.
    pub kind: String,
    /// The condition under which the winner applies. `⊤` replaces the loser everywhere.
    pub condition: String,
    /// Whether the two statements conflict where both apply.
    pub conflict: bool,
    /// The condition of the statement that yields, as its author wrote it:
    /// a relation narrows the formula and leaves the condition as it is.
    #[serde(skip)]
    pub authored: Formula,
    /// The questions that the reader asked the solver to establish this
    /// relation, each with the certificate of its answer.
    #[serde(skip)]
    pub queries: Vec<ReaderQuery>,
}

/// A question that the reader asked the solver while it built the model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReaderQuery {
    /// What the answer decides.
    pub purpose: String,
    /// What the terms say: the premises of every such question.
    pub axioms: std::sync::Arc<Vec<Formula>>,
    /// The formulas that are asked together with the axioms.
    pub formulas: Vec<Formula>,
    pub answer: Answer,
}

impl ReaderQuery {
    /// Every formula of the question.
    pub fn all(&self) -> Vec<Formula> {
        self.axioms.iter().chain(&self.formulas).cloned().collect()
    }
}

/// The recommendations to keep when recommendations cannot all be followed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Preference {
    pub kept: Vec<SpecRef>,
    pub dropped: Vec<SpecRef>,
    pub kept_weight: u64,
    pub dropped_weight: u64,
    /// `true` when no other set weighs more: a refutation shows that the
    /// hard constraints allow no greater weight. Otherwise the set was built
    /// by weight, greatest first, or the refutation was not found.
    pub optimal: bool,
}

fn statements(set: &SpecSet) -> impl Iterator<Item = (&Spec, String)> {
    set.packages.iter().flat_map(|pkg| pkg.documents.iter().flat_map(move |doc| doc.specs.iter().map(move |spec| (spec, if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) }))))
}

/// Narrows the formula of each statement that yields to another one. This
/// runs before refinements are read, so that a detailed statement is the
/// conjunction of its details as they apply.
pub(super) fn apply(_set: &SpecSet, _lex: &crate::reading::lexicon::Lexicon, _model: &mut Model) {
    // No statement narrows another: a set of contracts is a conjunction,
    // and adding a statement only removes behaviours. `overrides`,
    // `default` and `weight` are rejected by [`check`], and a permission
    // that a prohibition contradicts is a contradiction like any other.
}

/// The condition of a contract as its author wrote it. A statement that
/// yields to another one keeps its condition: only its formula is narrowed.
pub fn authored_condition(model: &Model, constraint: &Constraint) -> Formula {
    if !matches!(constraint.kind, ConstraintKind::Spec | ConstraintKind::Permission) {
        return constraint.assume.clone();
    }
    let narrows = |authored: &Formula| match (authored, &constraint.assume) {
        (Formula::True, Formula::Not(_)) => true,
        (Formula::True, Formula::And(items)) => items.iter().all(|i| matches!(i, Formula::Not(_))),
        (Formula::And(parts), Formula::And(items)) => items.len() > parts.len() && items.starts_with(parts),
        (other, Formula::And(items)) => items.len() > 1 && items[0] == *other,
        _ => false,
    };
    let found = constraint.refs.first().and_then(|at| model.priorities.iter().find(|p| p.yields == *at && narrows(&p.authored)));
    found.map_or_else(|| constraint.assume.clone(), |p| p.authored.clone())
}

/// Reports each priority line: no statement changes the contract of another.
pub fn check(set: &SpecSet, _model: &Model) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for (spec, id) in statements(set) {
        let at = SpecRef { id: id.clone(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
        let lines: Vec<&str> = [(!spec.overrides.is_empty()).then_some("overrides"), spec.default.then_some("default"), spec.weight.is_some().then_some("weight")].into_iter().flatten().collect();
        for line in lines {
            out.push(Diagnostic::error("priority-unsupported", format!("`{line}` would let one statement change the contract of another, and the contracts of a specification are a conjunction: a statement only removes behaviours. State the exception in the statement that has it, with `, unless …`, or as the condition of a narrower statement"), vec![at.clone()]));
        }
    }
    out
}

