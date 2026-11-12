//! Which statement wins where two statements conflict.
//!
//! A conjunction is monotonic: a general rule and its exception contradict
//! each other unless the general rule names the exception. Two lines under a
//! statement let an author rank statements without editing the general one:
//!
//! - `overrides [ID], [ID]`: where the condition of this statement holds, the
//!   named statements do not apply;
//! - `default`: the statement yields to each more specific statement that
//!   contradicts it.
//!
//! A third line, `weight N`, ranks recommendations: when recommendations
//! cannot all be followed, the set with the greatest weight is the one to keep.
//!
//! A general permission yields without a line: a narrower prohibition of the
//! same action restricts it. Each yielding is applied in the model: the
//! formula of the statement that yields is narrowed to where the condition
//! of the other does not hold, so no query has to leave a statement out.
//! Every answer of the solver that decides a yielding is kept with its
//! certificate.

use crate::document::SpecSet;
use crate::diagnostic::{Diagnostic, SpecRef};
use crate::document::Spec;
use crate::reading::model::{Constraint, ConstraintKind, Model};
use trion_solver::Formula;
use trion_solver::{Answer, Prover, Status};
use crate::syntax::ast::{Core, Modal};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

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

/// The reader's questions about one set of axioms.
struct Asker {
    prover: Prover,
    axioms: std::sync::Arc<Vec<Formula>>,
    ids: Vec<usize>,
    asked: Vec<ReaderQuery>,
}

impl Asker {
    fn new(axioms: Vec<Formula>) -> Self {
        let mut prover = Prover::default();
        let ids = axioms.iter().map(|f| prover.add(f)).collect();
        Self { prover, axioms: std::sync::Arc::new(axioms), ids, asked: Vec::new() }
    }

    /// Asks one question and keeps it with its certificate.
    fn ask(&mut self, purpose: &str, formulas: Vec<Formula>) -> Status {
        let mut ids = self.ids.clone();
        ids.extend(formulas.iter().map(|f| self.prover.add(f)));
        let answer = self.prover.decide(&ids);
        let status = answer.status;
        self.asked.push(ReaderQuery { purpose: purpose.to_string(), axioms: self.axioms.clone(), formulas, answer });
        status
    }

    /// The questions asked since `mark`.
    fn since(&self, mark: usize) -> Vec<ReaderQuery> {
        self.asked[mark..].to_vec()
    }
}

/// The actions that a formula forbids (`true`) or declares not forbidden (`false`).
fn forbidden(formula: &Formula, positive: bool) -> BTreeSet<String> {
    let mut keys = BTreeSet::new();
    formula.atoms(true, &mut |atom, polarity| {
        if let trion_solver::Atom::Forbid { key } = atom {
            if polarity == positive {
                keys.insert(key.clone());
            }
        }
    });
    keys
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

/// What the terms of the model say, for deciding whether two statements conflict:
/// the background and the axioms of definitions, inclusions and exclusions.
fn axioms(set: &SpecSet, lex: &crate::reading::lexicon::Lexicon, model: &Model) -> Vec<Formula> {
    let mut with_meaning = model.clone();
    crate::reading::meaning::apply(set, lex, &mut with_meaning);
    let stated = with_meaning.constraints.iter().filter(|c| c.kind.is_axiom()).map(|c| c.guarantee.clone());
    with_meaning.background.iter().cloned().chain(stated).collect()
}

/// Narrows the formula of each statement that yields to another one. This
/// runs before refinements are read, so that a detailed statement is the
/// conjunction of its details as they apply.
pub(super) fn apply(set: &SpecSet, lex: &crate::reading::lexicon::Lexicon, model: &mut Model) {
    let ranked: Vec<(&Spec, String)> = statements(set).filter(|(s, _)| !s.overrides.is_empty() || s.default).collect();
    let contract = |c: &Constraint| matches!(c.kind, ConstraintKind::Spec | ConstraintKind::Permission);
    // A permission and a conditional prohibition of the same action.
    let mut restricted: Vec<(usize, usize)> = Vec::new();
    for (p, permission) in model.constraints.iter().enumerate().filter(|(_, c)| c.kind == ConstraintKind::Permission) {
        let allowed = forbidden(&permission.guarantee, false);
        if allowed.is_empty() {
            continue;
        }
        for (q, prohibition) in model.constraints.iter().enumerate() {
            if q != p && prohibition.kind == ConstraintKind::Spec && prohibition.has_guard() && !forbidden(&prohibition.guarantee, true).is_disjoint(&allowed) {
                restricted.push((p, q));
            }
        }
    }
    if ranked.is_empty() && restricted.is_empty() {
        return;
    }
    let started = std::time::Instant::now();
    let mut asker = Asker::new(axioms(set, lex, model));
    if std::env::var("TRION_PROFILE").is_ok() {
        eprintln!("profile: priorities: {} ranked statements, {} permissions with a prohibition, axioms read in {:.3}s", ranked.len(), restricted.len(), started.elapsed().as_secs_f64());
    }
    let index_of = |id: &str, model: &Model| model.constraints.iter().position(|c| contract(c) && c.refs.first().is_some_and(|r| r.id == id));
    let conflict = |asker: &mut Asker, a: &Constraint, b: &Constraint| asker.ask("the two statements conflict where both apply", vec![a.assume.clone(), b.assume.clone(), a.guarantee.clone(), b.guarantee.clone()]) == Status::Unsatisfiable;
    // `(loser, winner, kind, conflict, queries)` over the constraints as authored.
    let mut pairs: Vec<(usize, usize, &str, bool, Vec<ReaderQuery>)> = Vec::new();
    for (spec, id) in &ranked {
        let Some(own) = index_of(id, model) else { continue };
        for target in &spec.overrides {
            let qualified = id.rsplit_once("::").map_or(target.clone(), |(pkg, _)| format!("{pkg}::{target}"));
            if let Some(loser) = index_of(&qualified, model).filter(|&l| l != own) {
                let mark = asker.asked.len();
                let conflicts = conflict(&mut asker, &model.constraints[loser], &model.constraints[own]);
                pairs.push((loser, own, "overrides", conflicts, asker.since(mark)));
            }
        }
        if spec.default {
            let general = &model.constraints[own];
            for (other, candidate) in model.constraints.iter().enumerate() {
                if other == own || !contract(candidate) || !candidate.has_guard() {
                    continue;
                }
                let mark = asker.asked.len();
                // More specific: the other condition holds only where the default applies.
                let narrower = !general.has_guard() || asker.ask("the condition of the more specific statement holds only where the default applies", vec![candidate.assume.clone(), Formula::not(general.assume.clone())]) == Status::Unsatisfiable;
                if narrower && conflict(&mut asker, general, candidate) && !pairs.iter().any(|(l, w, kind, _, _)| (*l, *w, *kind) == (own, other, "overrides")) {
                    pairs.push((own, other, "default", true, asker.since(mark)));
                }
            }
        }
    }
    for (p, q) in restricted {
        if pairs.iter().any(|(l, w, _, _, _)| (*l, *w) == (p, q) || (*l, *w) == (q, p)) {
            continue;
        }
        let (permission, prohibition) = (&model.constraints[p], &model.constraints[q]);
        let mark = asker.asked.len();
        // Narrower: the prohibition applies only where the permission does,
        // and the permission also applies somewhere else.
        let within = !permission.has_guard() || asker.ask("the condition of the prohibition holds only where the permission applies", vec![prohibition.assume.clone(), Formula::not(permission.assume.clone())]) == Status::Unsatisfiable;
        if within && asker.ask("the permission applies where the prohibition does not", vec![permission.assume.clone(), Formula::not(prohibition.assume.clone())]) == Status::Satisfiable && conflict(&mut asker, permission, prohibition) {
            pairs.push((p, q, "narrows", true, asker.since(mark)));
        }
    }
    if std::env::var("TRION_PROFILE").is_ok() {
        eprintln!("profile: priorities: {} questions asked, done in {:.3}s", asker.asked.len(), started.elapsed().as_secs_f64());
    }
    // A cycle leaves no winner: it is reported, and nothing is narrowed along it.
    let cyclic = cycle_members(&pairs.iter().map(|(l, w, _, _, _)| (*l, *w)).collect::<Vec<_>>());
    let authored: Vec<Constraint> = model.constraints.clone();
    for (loser, winner, kind, conflict, queries) in pairs {
        let (yields, to) = (&authored[loser], &authored[winner]);
        let (Some(yields_ref), Some(to_ref)) = (yields.refs.first(), to.refs.first()) else { continue };
        model.priorities.push(Priority { yields: yields_ref.clone(), to: to_ref.clone(), kind: kind.to_string(), condition: to.assume.to_string(), conflict, authored: yields.assume.clone(), queries });
        if cyclic.contains(&loser) && cyclic.contains(&winner) {
            continue;
        }
        let outside = Formula::not(to.assume.clone());
        let narrowed = &mut model.constraints[loser];
        narrowed.assume = match std::mem::replace(&mut narrowed.assume, Formula::True) {
            Formula::True => outside,
            Formula::And(mut parts) => {
                parts.push(outside);
                Formula::And(parts)
            }
            other => Formula::And(vec![other, outside]),
        };
    }
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

/// The constraints that lie on a cycle of `(loser, winner)` pairs.
fn cycle_members(pairs: &[(usize, usize)]) -> BTreeSet<usize> {
    let mut reach: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for (loser, winner) in pairs {
        reach.entry(*loser).or_default().insert(*winner);
    }
    loop {
        let mut grown = false;
        let snapshot = reach.clone();
        for targets in reach.values_mut() {
            let more: BTreeSet<usize> = targets.iter().filter_map(|t| snapshot.get(t)).flatten().copied().collect();
            let before = targets.len();
            targets.extend(more);
            grown |= targets.len() > before;
        }
        if !grown {
            break;
        }
    }
    reach.iter().filter(|(node, targets)| targets.contains(node)).map(|(node, _)| *node).collect()
}

/// Reports priority lines that name no statement, that form a cycle, or that
/// rank two statements that do not conflict.
pub fn check(set: &SpecSet, model: &Model) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let known: BTreeSet<String> = statements(set).flat_map(|(s, id)| s.parts.iter().cloned().chain([id])).collect();
    for (spec, id) in statements(set) {
        let at = SpecRef { id: id.clone(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
        for target in &spec.overrides {
            let qualified = id.rsplit_once("::").map_or(target.clone(), |(pkg, _)| format!("{pkg}::{target}"));
            if *target == id || qualified == id {
                out.push(Diagnostic::error("CYCLIC_PRIORITY", format!("the statement `{id}` cannot override itself"), vec![at.clone()]));
            } else if !known.contains(&qualified) {
                out.push(Diagnostic::error("UNRESOLVED_REFERENCE", format!("`overrides [{target}]` names no statement of this package"), vec![at.clone()]));
            }
        }
        if spec.weight.is_some() && !matches!(spec.sentence.core, Core::Deontic { modal: Modal::Should, .. }) {
            out.push(Diagnostic::error("parse-priority", "`weight` ranks a recommendation: the statement it is written under has no `should`", vec![at.clone()]));
        }
        if spec.default && matches!(spec.sentence.core, Core::Definition { .. }) {
            out.push(Diagnostic::error("parse-priority", "a definition is no default: it obliges nobody", vec![at.clone()]));
        }
    }
    let cyclic = cycle_members(&model.priorities.iter().filter_map(|p| Some((position(model, &p.yields)?, position(model, &p.to)?))).collect::<Vec<_>>());
    let mut reported = BTreeSet::new();
    for priority in &model.priorities {
        let (Some(loser), Some(winner)) = (position(model, &priority.yields), position(model, &priority.to)) else { continue };
        if cyclic.contains(&loser) && cyclic.contains(&winner) {
            let mut names: Vec<&str> = model.priorities.iter().filter(|p| position(model, &p.yields).is_some_and(|l| cyclic.contains(&l))).map(|p| p.yields.id.as_str()).collect();
            names.sort();
            names.dedup();
            if reported.insert(names.join(",")) {
                let refs = model.priorities.iter().filter(|p| names.contains(&p.yields.id.as_str())).map(|p| p.yields.clone()).fold(Vec::new(), |mut acc: Vec<SpecRef>, r| {
                    if !acc.contains(&r) {
                        acc.push(r);
                    }
                    acc
                });
                out.push(Diagnostic::error("CYCLIC_PRIORITY", format!("the statements {} override one another in a cycle: no statement wins", names.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ")), refs));
            }
        } else if !priority.conflict && priority.kind == "overrides" {
            out.push(Diagnostic::warning("priority-without-conflict", format!("`{}` overrides `{}`, and the two statements do not conflict where both apply: the priority changes nothing but removes `{}` there", priority.to.id, priority.yields.id, priority.yields.id), vec![priority.to.clone(), priority.yields.clone()]));
        }
    }
    out
}

fn position(model: &Model, at: &SpecRef) -> Option<usize> {
    model.constraints.iter().position(|c| matches!(c.kind, ConstraintKind::Spec | ConstraintKind::Permission) && c.refs.first() == Some(at))
}
