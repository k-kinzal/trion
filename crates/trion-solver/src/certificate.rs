//! Answers with certificates.
//!
//! A status alone is a claim. This module decides a list of formulas and
//! returns, beside the status, what lets another program check it without
//! trusting the search:
//!
//! - for `satisfiable`, a witness: a truth value for each atom of the query
//!   and an integer for each quantity;
//! - for `unsatisfiable`, a refutation: a list of clauses that ends with
//!   the empty clause. Each clause follows by unit propagation from the
//!   clauses of the query and the clauses before it, or it is a linear lemma
//!   with a derivation;
//! - for `unknown`, nothing.
//!
//! A clause of a refutation names atoms and subformulas of the query. A
//! subformula is named by a definition: its connective and its parts, each
//! an atom or a subformula that an earlier definition names. A checker
//! encodes the formulas in its own way, with one variable for each
//! subformula as it is written (`a ∧ b` in two formulas is one
//! subformula), finds the variable of each definition among them, and
//! refuses a definition that names no subformula of the query. The search
//! branches on atoms and learns clauses over the same encoding; unit
//! propagation over any such encoding accepts them.

use super::arith::{decide_certified, AtMost, Derivation, Outcome, Source, Unequal};
use crate::formula::{Atom, Cmp, Formula};
use serde::Serialize;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

/// What one solver query established. A consistency result has exactly one
/// of these statuses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    /// Some admissible interpretation was found.
    Satisfiable,
    /// The search space was exhausted without an interpretation.
    Unsatisfiable,
    /// The analysis bounds ended the search before either was established.
    Unknown,
}

impl Status {
    pub fn as_str(self) -> &'static str {
        match self {
            Status::Satisfiable => "satisfiable",
            Status::Unsatisfiable => "unsatisfiable",
            Status::Unknown => "unknown",
        }
    }
}

/// The clause visits that all queries of one instance may make together. An
/// analysis that would exceed it ends with `unknown` instead of running on:
/// an editor runs the analysis on every change.
pub(super) const WORK_LIMIT: u64 = 300_000_000;
/// The decisions that the search for one part of a query may make when the
/// caller sets no bound. A query that needs more is beyond this search; it
/// ends with `unknown`.
pub(super) const QUERY_DECISIONS: u64 = 400_000;

/// An atom or its negation.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Literal {
    pub atom: Atom,
    pub positive: bool,
}

/// A quantity: an attribute with its unit.
pub type Quantity = (String, String);

/// One part of a witness: the atoms and quantities of formulas that share
/// nothing with the other parts. Queries that agree on a part share it.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct WitnessPart {
    pub atoms: Vec<(Atom, bool)>,
    pub quantities: Vec<(Quantity, i64)>,
}

/// A truth value for each atom of a query and an integer for each quantity.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Witness {
    pub parts: Vec<Arc<WitnessPart>>,
}

impl Witness {
    /// The truth value of each atom.
    pub fn atoms(&self) -> BTreeMap<Atom, bool> {
        self.parts.iter().flat_map(|p| p.atoms.iter().cloned()).collect()
    }

    /// The integer of each quantity.
    pub fn quantities(&self) -> BTreeMap<Quantity, i64> {
        self.parts.iter().flat_map(|p| p.quantities.iter().cloned()).collect()
    }
}

/// Which inequality a numeric literal gives: `sum ≤ n` or `sum ≥ n`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
    Upper,
    Lower,
}

/// An inequality of a linear lemma.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinearSource {
    /// The inequality that the negation of the literal at this index of the
    /// clause gives on this side.
    Literal { index: usize, side: Side },
    /// The inequality that the split at this depth of the path added.
    Split(usize),
}

/// Why the negations of the literals of a clause have no integer solution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LinearDerivation {
    /// The inequalities, each multiplied by its non-negative integer, add up
    /// to `0 ≤ c` with a negative `c`.
    Leaf { multipliers: Vec<(LinearSource, i128)> },
    /// The negation of the literal at this index is a disequality `s ≠ v`:
    /// `below` refutes with `s ≤ v − 1` added, `above` with `s ≥ v + 1`.
    Split { literal: usize, below: Box<LinearDerivation>, above: Box<LinearDerivation> },
}

/// Why a clause of a refutation holds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Justification {
    /// Unit propagation over the clauses of the query, the clauses before
    /// this one and the negation of each literal of this one reaches a conflict.
    Propagation,
    /// Every literal is numeric, and the negations have no integer solution.
    Linear(LinearDerivation),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Step {
    /// The literals of the clause that are about atoms.
    pub clause: Vec<Literal>,
    /// The literals of the clause that are about subformulas: the number
    /// of the definition, and `false` for the denial of the subformula.
    pub formulas: Vec<(usize, bool)>,
    pub by: Justification,
}

/// How the parts of a subformula stand together.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Connective {
    /// The formula that holds.
    True,
    /// Each part holds.
    All,
    /// Some part holds. `a → b` is `¬a` or `b`.
    Any,
}

/// A part of a subformula: an atom, or a subformula that an earlier
/// definition names; each as it stands or denied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operand {
    Atom(Literal),
    Formula { definition: usize, positive: bool },
}

/// The name of one subformula of the query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    pub connective: Connective,
    pub operands: Vec<Operand>,
}

/// Clauses over the atoms and the named subformulas of a query, the last of
/// which is empty.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Refutation {
    pub steps: Vec<Step>,
    pub definitions: Vec<Definition>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Certificate {
    Witness(Witness),
    Refutation(Arc<Refutation>),
    /// An unknown status has no certificate.
    None,
}

/// A status with what shows it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Answer {
    pub status: Status,
    pub certificate: Certificate,
}

impl Answer {
    pub fn unknown() -> Self {
        Self { status: Status::Unknown, certificate: Certificate::None }
    }

    pub fn witness(&self) -> Option<&Witness> {
        match &self.certificate {
            Certificate::Witness(w) => Some(w),
            _ => None,
        }
    }

    pub fn refutation(&self) -> Option<&Refutation> {
        match &self.certificate {
            Certificate::Refutation(r) => Some(r),
            _ => None,
        }
    }
}

/// The terms and the comparison of a numeric atom.
fn numeric(atom: &Atom) -> Option<(Vec<(Quantity, i64)>, Cmp, i64)> {
    match atom {
        Atom::Num { attr, unit, cmp, n } => Some((vec![((attr.clone(), unit.clone()), 1)], *cmp, *n)),
        Atom::Lin { terms, unit, cmp, n } => Some((terms.iter().map(|(attr, coef)| ((attr.clone(), unit.clone()), *coef)).collect(), *cmp, *n)),
        _ => None,
    }
}

/// The inequalities and disequalities that an assignment of numeric atoms gives.
struct LinearSystem {
    at_most: Vec<AtMost>,
    /// The literal and the side of each inequality.
    sources: Vec<(usize, Side)>,
    unequal: Vec<Unequal>,
    /// The literal of each disequality.
    unequal_literals: Vec<usize>,
    names: Vec<Quantity>,
}

fn linear_system(assigned: &[(&Atom, bool)]) -> LinearSystem {
    let mut names: Vec<Quantity> = Vec::new();
    let mut index: HashMap<Quantity, usize> = HashMap::new();
    let mut system = LinearSystem { at_most: Vec::new(), sources: Vec::new(), unequal: Vec::new(), unequal_literals: Vec::new(), names: Vec::new() };
    for (position, (atom, value)) in assigned.iter().enumerate() {
        let Some((terms, cmp, n)) = numeric(atom) else { continue };
        let mut sum = |sign: i128| -> Vec<(usize, i128)> {
            terms
                .iter()
                .map(|(key, coef)| {
                    let at = *index.entry(key.clone()).or_insert_with(|| {
                        names.push(key.clone());
                        names.len() - 1
                    });
                    (at, sign * i128::from(*coef))
                })
                .collect()
        };
        let n = i128::from(n);
        // A strict inequality between integers is the one that is not strict, moved by one.
        let (upper, lower, differs) = match (cmp, value) {
            (Cmp::Eq, true) => (Some(n), Some(n), false),
            (Cmp::Eq, false) => (None, None, true),
            (Cmp::Le, true) | (Cmp::Gt, false) => (Some(n), None, false),
            (Cmp::Lt, true) | (Cmp::Ge, false) => (Some(n - 1), None, false),
            (Cmp::Ge, true) | (Cmp::Lt, false) => (None, Some(n), false),
            (Cmp::Gt, true) | (Cmp::Le, false) => (None, Some(n + 1), false),
        };
        if let Some(bound) = upper {
            system.at_most.push(AtMost { sum: sum(1), bound });
            system.sources.push((position, Side::Upper));
        }
        if let Some(bound) = lower {
            system.at_most.push(AtMost { sum: sum(-1), bound: -bound });
            system.sources.push((position, Side::Lower));
        }
        if differs {
            system.unequal.push(Unequal { sum: sum(1), value: n });
            system.unequal_literals.push(position);
        }
    }
    system.names = names;
    system
}

/// The literals that a derivation uses, in the order of the assignment.
fn used_literals(system: &LinearSystem, derivation: &Derivation, out: &mut Vec<usize>) {
    match derivation {
        Derivation::Leaf { multipliers } => {
            for (source, _) in multipliers {
                if let Source::Given(i) = source {
                    out.push(system.sources[*i].0);
                }
            }
        }
        Derivation::Split { unequal, below, above } => {
            out.push(system.unequal_literals[*unequal]);
            used_literals(system, below, out);
            used_literals(system, above, out);
        }
    }
}

fn translate(system: &LinearSystem, derivation: &Derivation, place: &HashMap<usize, usize>) -> LinearDerivation {
    match derivation {
        Derivation::Leaf { multipliers } => LinearDerivation::Leaf {
            multipliers: multipliers
                .iter()
                .map(|(source, by)| {
                    let source = match source {
                        Source::Given(i) => LinearSource::Literal { index: place[&system.sources[*i].0], side: system.sources[*i].1 },
                        Source::Split(depth) => LinearSource::Split(*depth),
                    };
                    (source, *by)
                })
                .collect(),
        },
        Derivation::Split { unequal, below, above } => LinearDerivation::Split { literal: place[&system.unequal_literals[*unequal]], below: Box::new(translate(system, below, place)), above: Box::new(translate(system, above, place)) },
    }
}

type Lit = i32;

/// One formula of a prover, encoded once.
struct Encoded {
    clauses: Vec<Vec<Lit>>,
    /// The variables of its atoms.
    atoms: Vec<Lit>,
}

/// What the search established for formulas that share atoms.
#[derive(Clone)]
enum Part {
    Satisfiable(Arc<WitnessPart>),
    Unsatisfiable(Arc<Refutation>),
    Unknown,
}

/// The literals that one refutation may hold.
const REFUTATION_LITERALS: usize = 4_000_000;

/// Decides queries over formulas that are added once and named by their
/// index. The formulas of a query that share atoms, directly or through
/// other formulas or through a quantity, form a part; a part is decided once
/// and its result is shared by every query that holds the same part.
pub struct Prover {
    formulas: Vec<Encoded>,
    variables: HashMap<Atom, Lit>,
    /// The atom of each variable; `None` for a variable of the encoding.
    atoms: Vec<Option<Atom>>,
    /// The quantities of each numeric atom, by variable.
    quantities: HashMap<Lit, Vec<Quantity>>,
    /// The number of each quantity, and the numbers of the quantities of each variable.
    quantity_ids: HashMap<Quantity, u32>,
    quantities_of: Vec<Vec<u32>>,
    parts: RefCell<HashMap<Vec<u32>, Part>>,
    decisions: u64,
    /// The clause visits of all queries so far.
    pub(crate) work: Cell<u64>,
    /// The most decisions that the search for one part has made.
    peak: Cell<u64>,
    /// For each variable of an atom: how often the formulas state the atom
    /// less how often they deny it. An atom that is denied more often is
    /// tried false first.
    leaning: Vec<i32>,
    /// The variable of each subformula, by its connective and the literals
    /// of its parts: a subformula that is written twice has one variable.
    nodes: HashMap<(Connective, Vec<Lit>), Lit>,
    /// The connective and the parts of each variable of a subformula.
    shapes: Vec<Option<(Connective, Vec<Lit>)>>,
}

impl Default for Prover {
    fn default() -> Self {
        Self::new(None)
    }
}

impl Prover {
    /// A prover whose search for one part ends after the given decisions.
    pub fn new(decisions: Option<u64>) -> Self {
        Self { formulas: Vec::new(), variables: HashMap::new(), atoms: vec![None], quantities: HashMap::new(), quantity_ids: HashMap::new(), quantities_of: vec![Vec::new()], parts: RefCell::new(HashMap::new()), decisions: decisions.unwrap_or(QUERY_DECISIONS), work: Cell::new(0), peak: Cell::new(0), leaning: vec![0], nodes: HashMap::new(), shapes: vec![None] }
    }

    fn fresh(&mut self) -> Lit {
        self.atoms.push(None);
        self.leaning.push(0);
        self.shapes.push(None);
        self.quantities_of.push(Vec::new());
        (self.atoms.len() - 1) as Lit
    }

    fn atom(&mut self, atom: &Atom) -> Lit {
        if let Some(&v) = self.variables.get(atom) {
            return v;
        }
        let v = self.fresh();
        self.atoms[v as usize] = Some(atom.clone());
        self.variables.insert(atom.clone(), v);
        if let Some((terms, _, _)) = numeric(atom) {
            let keys: Vec<Quantity> = terms.into_iter().map(|(key, _)| key).collect();
            for key in &keys {
                let next = self.quantity_ids.len() as u32;
                let id = *self.quantity_ids.entry(key.clone()).or_insert(next);
                self.quantities_of[v as usize].push(id);
            }
            self.quantities.insert(v, keys);
        }
        v
    }

    /// The variable of the subformula with this connective and these parts.
    fn node(&mut self, connective: Connective, parts: &[Lit]) -> Lit {
        if let Some(&v) = self.nodes.get(&(connective, parts.to_vec())) {
            return v;
        }
        let v = self.fresh();
        self.nodes.insert((connective, parts.to_vec()), v);
        self.shapes[v as usize] = Some((connective, parts.to_vec()));
        v
    }

    /// Tseitin: a literal that is equivalent to the formula. A subformula
    /// has one variable wherever it is written, and an atom has one
    /// variable everywhere; the clauses that define a subformula are given
    /// with each formula that holds it.
    fn encode(&mut self, f: &Formula, stated: bool, out: &mut Vec<Vec<Lit>>, atoms: &mut Vec<Lit>) -> Lit {
        match f {
            Formula::True => {
                let v = self.node(Connective::True, &[]);
                out.push(vec![v]);
                v
            }
            Formula::Atom(a) => {
                let v = self.atom(a);
                self.leaning[v as usize] += if stated { 1 } else { -1 };
                atoms.push(v);
                v
            }
            Formula::Not(x) => -self.encode(x, !stated, out, atoms),
            Formula::Implies(a, b) => {
                let lits = vec![-self.encode(a, !stated, out, atoms), self.encode(b, stated, out, atoms)];
                self.any(lits, out)
            }
            Formula::And(xs) => {
                let lits: Vec<Lit> = xs.iter().map(|x| self.encode(x, stated, out, atoms)).collect();
                let v = self.node(Connective::All, &lits);
                let mut long = vec![v];
                for &l in &lits {
                    out.push(vec![-v, l]);
                    long.push(-l);
                }
                out.push(long);
                v
            }
            Formula::Or(xs) => {
                let lits: Vec<Lit> = xs.iter().map(|x| self.encode(x, stated, out, atoms)).collect();
                self.any(lits, out)
            }
        }
    }

    fn any(&mut self, lits: Vec<Lit>, out: &mut Vec<Vec<Lit>>) -> Lit {
        let v = self.node(Connective::Any, &lits);
        let mut long = vec![-v];
        for &l in &lits {
            out.push(vec![v, -l]);
            long.push(l);
        }
        out.push(long);
        v
    }

    /// The number of the definition that names the subformula of a
    /// variable, with the definitions of its parts before it.
    fn define(&self, variable: Lit, defined: &mut HashMap<Lit, usize>, definitions: &mut Vec<Definition>) -> usize {
        if let Some(&number) = defined.get(&variable) {
            return number;
        }
        let (connective, parts) = self.shapes[variable as usize].clone().expect("a variable that is no atom is a subformula");
        let operands = parts
            .iter()
            .map(|&part| match &self.atoms[part.unsigned_abs() as usize] {
                Some(atom) => Operand::Atom(Literal { atom: atom.clone(), positive: part > 0 }),
                None => Operand::Formula { definition: self.define(part.abs(), defined, definitions), positive: part > 0 },
            })
            .collect();
        definitions.push(Definition { connective, operands });
        defined.insert(variable, definitions.len() - 1);
        definitions.len() - 1
    }

    /// Adds a formula and returns the index that names it in a query.
    pub fn add(&mut self, formula: &Formula) -> usize {
        let mut clauses = Vec::new();
        let mut atoms = Vec::new();
        let root = self.encode(formula, true, &mut clauses, &mut atoms);
        clauses.push(vec![root]);
        atoms.sort_unstable();
        atoms.dedup();
        self.formulas.push(Encoded { clauses, atoms });
        self.formulas.len() - 1
    }

    /// The clause visits that all queries of this prover may make
    /// together. A caller that allows a query more decisions than the
    /// default allows the queries together more work in the same
    /// proportion: the default keeps an analysis short enough for an
    /// editor, and a larger domain needs more of both.
    fn work_limit(&self) -> u64 {
        WORK_LIMIT.saturating_mul((self.decisions / QUERY_DECISIONS).max(1))
    }

    /// `true` when a query was refused because the work limit was reached.
    pub(crate) fn exhausted(&self) -> bool {
        self.work.get() > self.work_limit()
    }

    /// The most decisions that the search for one part has made.
    pub(crate) fn peak_decisions(&self) -> u64 {
        self.peak.get()
    }

    /// Decides the conjunction of the named formulas.
    pub fn decide(&self, query: &[usize]) -> Answer {
        self.decide_with_part(query).0
    }

    /// Decides the conjunction of the named formulas. With a refutation
    /// comes the part that is refuted: the formulas of the query that the
    /// refutation can rest on.
    pub(crate) fn decide_with_part(&self, query: &[usize]) -> (Answer, Option<Vec<usize>>) {
        let mut ids: Vec<usize> = query.to_vec();
        ids.sort_unstable();
        ids.dedup();
        // The formulas of the query that share an atom or a quantity form
        // one part. A variable without a parent stands for itself.
        let mut parent: Vec<u32> = vec![0; self.atoms.len()];
        fn find(parent: &mut [u32], x: u32) -> u32 {
            let mut root = x;
            while parent[root as usize] != 0 {
                root = parent[root as usize];
            }
            let mut at = x;
            while at != root {
                let next = parent[at as usize];
                parent[at as usize] = root;
                at = next;
            }
            root
        }
        fn join(parent: &mut [u32], a: u32, b: u32) {
            let (x, y) = (find(parent, a), find(parent, b));
            if x != y {
                parent[x as usize] = y;
            }
        }
        let mut by_quantity: Vec<u32> = vec![0; self.quantity_ids.len()];
        for &id in &ids {
            let atoms = &self.formulas[id].atoms;
            for &a in atoms {
                for &key in &self.quantities_of[a as usize] {
                    match by_quantity[key as usize] {
                        0 => by_quantity[key as usize] = a as u32,
                        other => join(&mut parent, a as u32, other),
                    }
                }
            }
            for pair in atoms.windows(2) {
                join(&mut parent, pair[0] as u32, pair[1] as u32);
            }
        }
        let mut groups: HashMap<i64, Vec<u32>> = HashMap::new();
        let mut order: Vec<i64> = Vec::new();
        for &id in &ids {
            // A formula without an atom is a part of its own.
            let root = match self.formulas[id].atoms.first() {
                Some(&a) => i64::from(find(&mut parent, a as u32)),
                None => -(id as i64) - 1,
            };
            let members = groups.entry(root).or_default();
            if members.is_empty() {
                order.push(root);
            }
            members.push(id as u32);
        }
        let mut witness = Witness::default();
        let mut unknown = false;
        for root in order {
            let Some(key) = groups.remove(&root) else { continue };
            let cached = self.parts.borrow().get(&key).cloned();
            let part = match cached {
                Some(part) => part,
                None => {
                    let part = self.search(&key);
                    self.parts.borrow_mut().insert(key.clone(), part.clone());
                    part
                }
            };
            match part {
                Part::Satisfiable(found) => witness.parts.push(found),
                Part::Unsatisfiable(refutation) => return (Answer { status: Status::Unsatisfiable, certificate: Certificate::Refutation(refutation) }, Some(key.into_iter().map(|id| id as usize).collect())),
                Part::Unknown => unknown = true,
            }
        }
        if unknown {
            return (Answer::unknown(), None);
        }
        (Answer { status: Status::Satisfiable, certificate: Certificate::Witness(witness) }, None)
    }

    /// The search for one part: DPLL that branches on atoms only.
    /// The search for one part: clause learning that branches on atoms
    /// only. A learned clause is the cut of the implications behind a
    /// conflict at the first consequence of the last decision that every
    /// way to the conflict passes. The negation of such a clause forces, by
    /// unit propagation, everything behind the cut and with it the
    /// conflict, so each learned clause is a step of the refutation; where
    /// it holds a variable of the encoding, the step names the subformula.
    fn search(&self, key: &[u32]) -> Part {
        if self.exhausted() {
            return Part::Unknown;
        }
        // The variables of the part are numbered densely.
        let mut local: HashMap<Lit, Lit> = HashMap::new();
        let mut global: Vec<Lit> = vec![0];
        let mut clauses: Vec<Vec<Lit>> = Vec::new();
        // The formulas that were added last come first: a question adds what
        // it asks to formulas that are known to hold together, and the search
        // branches on the atoms of what is asked before the others.
        for &id in key.iter().rev() {
            for clause in &self.formulas[id as usize].clauses {
                clauses.push(
                    clause
                        .iter()
                        .map(|&l| {
                            let next = global.len() as Lit;
                            let v = *local.entry(l.abs()).or_insert_with(|| {
                                global.push(l.abs());
                                next
                            });
                            if l < 0 {
                                -v
                            } else {
                                v
                            }
                        })
                        .collect(),
                );
            }
        }
        let count = global.len();
        let branch: Vec<Lit> = (1..count as Lit).filter(|&v| self.atoms[global[v as usize] as usize].is_some()).collect();
        let numeric_atoms: Vec<Lit> = branch.iter().copied().filter(|&v| self.quantities.contains_key(&global[v as usize])).collect();
        let mut is_atom = vec![false; count];
        for &v in &branch {
            is_atom[v as usize] = true;
        }
        let atom_of = |v: Lit| self.atoms[global[v as usize] as usize].clone().expect("a branching variable is an atom");
        let literal = |l: Lit| Literal { atom: atom_of(l.abs()), positive: l > 0 };
        let mut search = Search::new(count, is_atom, &branch);
        for &v in &branch {
            if self.leaning[global[v as usize] as usize] < 0 {
                search.phase[v as usize] = -1;
            }
        }
        let mut steps: Vec<Step> = Vec::new();
        let mut definitions: Vec<Definition> = Vec::new();
        let mut defined: HashMap<Lit, usize> = HashMap::new();
        let mut size = 0usize;
        let mut made = 0u64;
        let mut conflicts = 0u64;
        let mut restart = Restarts::default();
        let mut conflict: Option<usize> = None;
        let profile = std::env::var("TRION_PROFILE_SEARCH").is_ok();
        let started = std::time::Instant::now();
        let (mut lemmas, mut models) = (0u64, 0u64);
        let given = clauses.len();
        macro_rules! report {
            ($kind:expr) => {
                if profile && (started.elapsed().as_millis() > 300 || conflicts > 2000) {
                    eprintln!("profile: {} part of {} formulas, {} clauses, {} atoms: {made} decisions, {conflicts} conflicts, {lemmas} lemmas, {models} assignments, {} learned literals, {:?}", $kind, key.len(), given, branch.len(), size_of_steps(&steps), started.elapsed());
                }
            };
        }
        for clause in clauses {
            if let Some(n) = search.add(clause) {
                conflict = Some(n);
                break;
            }
        }
        loop {
            if conflict.is_none() {
                conflict = search.propagate();
            }
            let spent = self.work.get().saturating_add(std::mem::take(&mut search.work));
            self.work.set(spent);
            if spent > self.work_limit() {
                report!("unknown (work)");
                return Part::Unknown;
            }
            if conflict.is_none() {
                if restart.due(conflicts) {
                    search.back_to(0);
                }
                if let Some(v) = search.next() {
                    made += 1;
                    self.peak.set(self.peak.get().max(made));
                    if made > self.decisions {
                        report!("unknown (decisions)");
                        return Part::Unknown;
                    }
                    search.decide(v);
                    continue;
                }
                // Every atom has a value, and with it every variable of the encoding: the numbers decide.
                if search.assign.iter().skip(1).any(|v| *v == 0) || !search.satisfied() {
                    return Part::Unknown;
                }
                let assigned: Vec<(Atom, bool)> = numeric_atoms.iter().map(|&v| (atom_of(v), search.assign[v as usize] == 1)).collect();
                models += 1;
                match self.theory(&assigned) {
                    Theory::Point(quantities) => {
                        let atoms = branch.iter().map(|&v| (atom_of(v), search.assign[v as usize] == 1)).collect();
                        report!("sat");
                        return Part::Satisfiable(Arc::new(WitnessPart { atoms, quantities }));
                    }
                    Theory::Undecided => return Part::Unknown,
                    Theory::Lemma(lemma, derivation) => {
                        lemmas += 1;
                        let mut clause: Vec<Lit> = lemma.iter().map(|l| if l.positive { local[&self.variables[&l.atom]] } else { -local[&self.variables[&l.atom]] }).collect();
                        clause.sort_by_key(|l| std::cmp::Reverse(search.level[l.unsigned_abs() as usize]));
                        size += lemma.len() + 1;
                        steps.push(Step { clause: lemma, formulas: Vec::new(), by: Justification::Linear(derivation) });
                        // Every literal of the lemma is false: the search goes back to the last of them.
                        let last = clause.iter().map(|l| search.level[l.unsigned_abs() as usize]).max().unwrap_or(0);
                        search.back_to(last);
                        conflict = Some(search.learn(clause));
                    }
                }
            }
            let Some(at) = conflict.take() else { continue };
            conflicts += 1;
            if search.marks.is_empty() {
                // No decision is involved: the clauses refute themselves.
                steps.push(Step { clause: Vec::new(), formulas: Vec::new(), by: Justification::Propagation });
                report!("unsat");
                return Part::Unsatisfiable(Arc::new(Refutation { steps, definitions }));
            }
            let (learned, back) = search.analyze(at);
            size += learned.len() + 1;
            // The clause names each atom by itself and each subformula by its definition.
            let mut step = Step { clause: Vec::new(), formulas: Vec::new(), by: Justification::Propagation };
            for &l in &learned {
                let variable = global[l.unsigned_abs() as usize];
                if self.atoms[variable as usize].is_some() {
                    step.clause.push(literal(l));
                } else {
                    step.formulas.push((self.define(variable, &mut defined, &mut definitions), l > 0));
                }
            }
            steps.push(step);
            if size > REFUTATION_LITERALS {
                report!("unknown (refutation size)");
                return Part::Unknown;
            }
            let asserted = learned[0];
            search.back_to(back);
            let clause = search.learn(learned);
            search.imply(asserted, clause);
        }
    }

    /// Decides the numeric atoms of a full assignment, one set of shared
    /// quantities at a time.
    fn theory(&self, assigned: &[(Atom, bool)]) -> Theory {
        let mut parent: Vec<usize> = (0..assigned.len()).collect();
        fn find(parent: &mut [usize], mut x: usize) -> usize {
            while parent[x] != x {
                parent[x] = parent[parent[x]];
                x = parent[x];
            }
            x
        }
        let terms: Vec<Vec<Quantity>> = assigned.iter().map(|(atom, _)| numeric(atom).map(|(terms, _, _)| terms.into_iter().map(|(key, _)| key).collect()).unwrap_or_default()).collect();
        // A quantity that a literal sets to one number joins nothing: every
        // set that names it holds the literals that set it, so the sets
        // agree on its number without being decided together.
        let mut set_by: HashMap<&Quantity, Vec<usize>> = HashMap::new();
        for (index, (atom, value)) in assigned.iter().enumerate() {
            if *value && terms[index].len() == 1 && matches!(numeric(atom), Some((_, Cmp::Eq, _))) {
                set_by.entry(&terms[index][0]).or_default().push(index);
            }
        }
        let sets_one = |index: usize| terms[index].len() == 1 && set_by.get(&terms[index][0]).is_some_and(|by| by.contains(&index));
        let mut first: HashMap<&Quantity, usize> = HashMap::new();
        for index in 0..assigned.len() {
            if sets_one(index) {
                continue;
            }
            for key in &terms[index] {
                if set_by.contains_key(key) {
                    continue;
                }
                match first.get(key) {
                    Some(&other) => {
                        let (a, b) = (find(&mut parent, index), find(&mut parent, other));
                        parent[a] = b;
                    }
                    None => {
                        first.insert(key, index);
                    }
                }
            }
        }
        let mut sets: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for index in 0..assigned.len() {
            if !sets_one(index) {
                sets.entry(find(&mut parent, index)).or_default().push(index);
            }
        }
        let mut sets: Vec<Vec<usize>> = sets.into_values().collect();
        for members in &mut sets {
            let mut with: Vec<usize> = members.iter().flat_map(|&index| terms[index].iter()).filter_map(|key| set_by.get(key)).flatten().copied().collect();
            members.append(&mut with);
            members.sort_unstable();
            members.dedup();
        }
        // The literals that set one quantity, among themselves.
        let mut alone: Vec<Vec<usize>> = set_by.values().cloned().collect();
        alone.sort_unstable();
        sets.extend(alone);
        let mut quantities: Vec<(Quantity, i64)> = Vec::new();
        let mut undecided = false;
        for members in sets {
            let lits: Vec<(&Atom, bool)> = members.iter().map(|&i| (&assigned[i].0, assigned[i].1)).collect();
            let system = linear_system(&lits);
            match decide_certified(&system.at_most, &system.unequal) {
                Outcome::Consistent(point) => {
                    for (index, name) in system.names.iter().enumerate() {
                        match i64::try_from(point.get(&index).copied().unwrap_or(0)) {
                            Ok(value) => quantities.push((name.clone(), value)),
                            Err(_) => undecided = true,
                        }
                    }
                }
                Outcome::Undecided => undecided = true,
                Outcome::Inconsistent(derivation) => {
                    // The lemma names only the literals that the derivation uses.
                    let mut used = Vec::new();
                    used_literals(&system, &derivation, &mut used);
                    used.sort_unstable();
                    used.dedup();
                    let place: HashMap<usize, usize> = used.iter().enumerate().map(|(new, old)| (*old, new)).collect();
                    let lemma = used.iter().map(|&i| Literal { atom: lits[i].0.clone(), positive: !lits[i].1 }).collect();
                    return Theory::Lemma(lemma, translate(&system, &derivation, &place));
                }
            }
        }
        if undecided {
            Theory::Undecided
        } else {
            quantities.sort();
            quantities.dedup();
            Theory::Point(quantities)
        }
    }
}

enum Theory {
    Point(Vec<(Quantity, i64)>),
    Lemma(Vec<Literal>, LinearDerivation),
    Undecided,
}

fn size_of_steps(steps: &[Step]) -> usize {
    steps.iter().map(|step| step.clause.len()).sum()
}

/// No clause: the mark of a decision.
const NONE: u32 = u32::MAX;

/// When the search starts again from no decision: after 64 conflicts times
/// the next number of the sequence 1, 1, 2, 1, 1, 2, 4, ….
#[derive(Default)]
struct Restarts {
    done: u64,
    at: u64,
}

impl Restarts {
    fn due(&mut self, conflicts: u64) -> bool {
        if self.at == 0 {
            self.at = 64 * Self::luby(self.done);
        }
        if conflicts < self.at {
            return false;
        }
        self.done += 1;
        self.at = conflicts + 64 * Self::luby(self.done);
        true
    }

    fn luby(mut n: u64) -> u64 {
        let mut size = 1u64;
        let mut power = 0u32;
        while size < n + 1 {
            power += 1;
            size = 2 * size + 1;
        }
        while size - 1 != n {
            size = (size - 1) / 2;
            power -= 1;
            n %= size;
        }
        1u64 << power
    }
}

/// The state of one search: an assignment with its trail, for each
/// variable the clause that forced its value, and the order in which the
/// atoms are decided.
struct Search {
    clauses: Vec<Vec<Lit>>,
    /// For each literal, the clauses that watch it: a clause of two or more
    /// literals watches its first two.
    watches: Vec<Vec<u32>>,
    assign: Vec<i8>,
    reason: Vec<u32>,
    level: Vec<u32>,
    trail: Vec<Lit>,
    /// The length of the trail before each decision.
    marks: Vec<usize>,
    head: usize,
    work: u64,
    is_atom: Vec<bool>,
    /// The value that an atom had last; an atom is decided true at first.
    phase: Vec<i8>,
    /// How often an atom stood behind a recent conflict.
    activity: Vec<f64>,
    step: f64,
    /// The atoms without a value, the most active first; among equals the
    /// one that comes first in the formulas.
    heap: Vec<u32>,
    place: Vec<u32>,
    seen: Vec<bool>,
}

fn slot(l: Lit) -> usize {
    (l.unsigned_abs() as usize) * 2 + usize::from(l < 0)
}

impl Search {
    fn new(count: usize, is_atom: Vec<bool>, branch: &[Lit]) -> Self {
        let mut search = Search { clauses: Vec::new(), watches: vec![Vec::new(); count * 2], assign: vec![0; count], reason: vec![NONE; count], level: vec![0; count], trail: Vec::new(), marks: Vec::new(), head: 0, work: 0, is_atom, phase: vec![1; count], activity: vec![0.0; count], step: 1.0, heap: Vec::new(), place: vec![NONE; count], seen: vec![false; count] };
        for &v in branch {
            search.insert(v as u32);
        }
        search
    }

    fn value(&self, l: Lit) -> i8 {
        let v = self.assign[l.unsigned_abs() as usize];
        if l > 0 {
            v
        } else {
            -v
        }
    }

    fn before(&self, a: u32, b: u32) -> bool {
        let (x, y) = (self.activity[a as usize], self.activity[b as usize]);
        x > y || (x == y && a < b)
    }

    fn up(&mut self, mut at: usize) {
        while at > 0 {
            let parent = (at - 1) / 2;
            if !self.before(self.heap[at], self.heap[parent]) {
                break;
            }
            self.heap.swap(at, parent);
            self.place[self.heap[at] as usize] = at as u32;
            self.place[self.heap[parent] as usize] = parent as u32;
            at = parent;
        }
    }

    fn down(&mut self, mut at: usize) {
        loop {
            let (left, right) = (2 * at + 1, 2 * at + 2);
            let mut best = at;
            if left < self.heap.len() && self.before(self.heap[left], self.heap[best]) {
                best = left;
            }
            if right < self.heap.len() && self.before(self.heap[right], self.heap[best]) {
                best = right;
            }
            if best == at {
                break;
            }
            self.heap.swap(at, best);
            self.place[self.heap[at] as usize] = at as u32;
            self.place[self.heap[best] as usize] = best as u32;
            at = best;
        }
    }

    fn insert(&mut self, v: u32) {
        if self.place[v as usize] != NONE {
            return;
        }
        self.place[v as usize] = self.heap.len() as u32;
        self.heap.push(v);
        self.up(self.heap.len() - 1);
    }

    /// The atom to decide next: the first of the order that has no value.
    fn next(&mut self) -> Option<Lit> {
        while let Some(&top) = self.heap.first() {
            let last = self.heap.len() - 1;
            self.heap.swap(0, last);
            self.heap.pop();
            self.place[top as usize] = NONE;
            if let Some(&moved) = self.heap.first() {
                self.place[moved as usize] = 0;
                self.down(0);
            }
            if self.assign[top as usize] == 0 {
                return Some(top as Lit);
            }
        }
        None
    }

    fn bump(&mut self, v: usize) {
        self.activity[v] += self.step;
        if self.activity[v] > 1e100 {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.step *= 1e-100;
        }
        if self.place[v] != NONE {
            self.up(self.place[v] as usize);
        }
    }

    fn imply(&mut self, l: Lit, clause: usize) {
        let v = l.unsigned_abs() as usize;
        self.assign[v] = if l > 0 { 1 } else { -1 };
        self.reason[v] = clause as u32;
        self.level[v] = self.marks.len() as u32;
        self.trail.push(l);
    }

    /// Gives an atom the value that it had last as a decision.
    fn decide(&mut self, v: Lit) {
        self.marks.push(self.trail.len());
        let at = v as usize;
        self.assign[at] = self.phase[at];
        self.reason[at] = NONE;
        self.level[at] = self.marks.len() as u32;
        self.trail.push(if self.phase[at] == 1 { v } else { -v });
    }

    /// Takes back every decision after the first `level` ones.
    fn back_to(&mut self, level: u32) {
        let Some(&mark) = self.marks.get(level as usize) else { return };
        while self.trail.len() > mark {
            if let Some(l) = self.trail.pop() {
                let v = l.unsigned_abs() as usize;
                self.phase[v] = self.assign[v];
                self.assign[v] = 0;
                if self.is_atom[v] {
                    self.insert(v as u32);
                }
            }
        }
        self.marks.truncate(level as usize);
        self.head = self.trail.len();
    }

    /// Adds a clause of the formulas before any decision. The clause when
    /// it is false already.
    fn add(&mut self, mut clause: Vec<Lit>) -> Option<usize> {
        // A literal that stands twice in a clause is one literal, and a
        // clause with a literal and its negation holds.
        clause.sort_unstable_by_key(|l| (l.unsigned_abs(), *l < 0));
        clause.dedup();
        if clause.windows(2).any(|pair| pair[0] == -pair[1]) {
            return None;
        }
        let n = self.clauses.len();
        match clause.len() {
            0 => {
                self.clauses.push(clause);
                return Some(n);
            }
            1 => {
                let l = clause[0];
                self.clauses.push(clause);
                match self.value(l) {
                    0 => self.imply(l, n),
                    1 => {}
                    _ => return Some(n),
                }
            }
            _ => {
                self.watches[slot(clause[0])].push(n as u32);
                self.watches[slot(clause[1])].push(n as u32);
                self.clauses.push(clause);
            }
        }
        None
    }

    /// Unit propagation; the clause of a conflict when there is one.
    fn propagate(&mut self) -> Option<usize> {
        while self.head < self.trail.len() {
            let failed = -self.trail[self.head];
            self.head += 1;
            let watching = std::mem::take(&mut self.watches[slot(failed)]);
            let mut kept: Vec<u32> = Vec::with_capacity(watching.len());
            let mut conflict = None;
            let mut at = 0;
            while at < watching.len() {
                let n = watching[at] as usize;
                at += 1;
                self.work += 1;
                if self.clauses[n][0] == failed {
                    self.clauses[n].swap(0, 1);
                }
                let first = self.clauses[n][0];
                if self.value(first) == 1 {
                    kept.push(n as u32);
                    continue;
                }
                // Another literal that is not false takes the watch.
                let other = (2..self.clauses[n].len()).find(|&k| self.value(self.clauses[n][k]) != -1);
                if let Some(k) = other {
                    self.clauses[n].swap(1, k);
                    let moved = self.clauses[n][1];
                    self.watches[slot(moved)].push(n as u32);
                    continue;
                }
                kept.push(n as u32);
                if self.value(first) == -1 {
                    conflict = Some(n);
                    kept.extend_from_slice(&watching[at..]);
                    break;
                }
                self.imply(first, n);
            }
            self.watches[slot(failed)] = kept;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }

    /// The clause that a conflict teaches, and the decisions to keep. Its
    /// first literal is the one consequence of the last decision that every
    /// way to the conflict passes; the others were given their value before
    /// that decision. A value that holds without any decision is left out.
    fn analyze(&mut self, conflict: usize) -> (Vec<Lit>, u32) {
        let current = self.marks.len() as u32;
        let mut learned: Vec<Lit> = vec![0];
        let mut marked: Vec<usize> = Vec::new();
        // The marked consequences of the last decision that are not replaced yet.
        let mut here = 0usize;
        let mut clause = Some(conflict);
        let mut at = self.trail.len();
        loop {
            if let Some(n) = clause.take() {
                for k in 0..self.clauses[n].len() {
                    let q = self.clauses[n][k];
                    let v = q.unsigned_abs() as usize;
                    if self.seen[v] || self.level[v] == 0 {
                        continue;
                    }
                    self.seen[v] = true;
                    marked.push(v);
                    if self.level[v] == current {
                        here += 1;
                    } else {
                        learned.push(q);
                    }
                }
            }
            if here == 0 || at == 0 {
                break;
            }
            at -= 1;
            let p = self.trail[at];
            let v = p.unsigned_abs() as usize;
            if !self.seen[v] || self.level[v] != current {
                continue;
            }
            if here == 1 {
                learned[0] = -p;
                break;
            }
            here -= 1;
            clause = Some(self.reason[v] as usize);
        }
        for &v in &marked {
            self.seen[v] = false;
            if self.is_atom[v] {
                self.bump(v);
            }
        }
        self.step /= 0.95;
        // The second literal is the one that was given its value last.
        let mut back = 0;
        for k in 1..learned.len() {
            let level = self.level[learned[k].unsigned_abs() as usize];
            if level > back {
                back = level;
                learned.swap(1, k);
            }
        }
        (learned, back)
    }

    fn satisfied(&self) -> bool {
        self.clauses.iter().all(|clause| clause.iter().any(|&l| self.value(l) == 1))
    }

    /// Adds a clause and returns its index. Its first two literals are
    /// watched: the caller puts first the two that lose their value first
    /// when decisions are taken back.
    fn learn(&mut self, clause: Vec<Lit>) -> usize {
        let n = self.clauses.len();
        if clause.len() >= 2 {
            self.watches[slot(clause[0])].push(n as u32);
            self.watches[slot(clause[1])].push(n as u32);
        }
        self.clauses.push(clause);
        n
    }
}

/// Decides the conjunction of the formulas, with a certificate.
pub fn decide(formulas: &[Formula]) -> Answer {
    let mut prover = Prover::default();
    let ids: Vec<usize> = formulas.iter().map(|f| prover.add(f)).collect();
    prover.decide(&ids)
}
