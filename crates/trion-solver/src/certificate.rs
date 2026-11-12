//! Answers with certificates.
//!
//! A status alone is a claim. This module decides a list of formulas and
//! returns, beside the status, what lets another program check it without
//! trusting the search:
//!
//! - for `satisfiable`, a witness: a truth value for each atom of the query
//!   and an integer for each quantity;
//! - for `unsatisfiable`, a refutation: a list of clauses over the atoms of
//!   the query that ends with the empty clause. Each clause follows by unit
//!   propagation from the clauses of the query and the clauses before it, or
//!   it is a linear lemma with a derivation;
//! - for `unknown`, nothing.
//!
//! A refutation names atoms only. The search branches on atoms and never on
//! a variable of its own encoding, so a checker may encode the formulas in
//! its own way. The clauses are produced against a plain Tseitin encoding in
//! which no two subformulas share a variable; unit propagation over any
//! encoding that propagates as much accepts them.

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
    pub clause: Vec<Literal>,
    pub by: Justification,
}

/// Clauses over the atoms of a query, the last of which is empty.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Refutation {
    pub steps: Vec<Step>,
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
}

impl Default for Prover {
    fn default() -> Self {
        Self::new(None)
    }
}

impl Prover {
    /// A prover whose search for one part ends after the given decisions.
    pub fn new(decisions: Option<u64>) -> Self {
        Self { formulas: Vec::new(), variables: HashMap::new(), atoms: vec![None], quantities: HashMap::new(), quantity_ids: HashMap::new(), quantities_of: vec![Vec::new()], parts: RefCell::new(HashMap::new()), decisions: decisions.unwrap_or(QUERY_DECISIONS), work: Cell::new(0), peak: Cell::new(0) }
    }

    fn fresh(&mut self) -> Lit {
        self.atoms.push(None);
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

    /// Tseitin: a literal that is equivalent to the formula. No two
    /// subformulas share a variable; an atom has one variable everywhere.
    fn encode(&mut self, f: &Formula, out: &mut Vec<Vec<Lit>>, atoms: &mut Vec<Lit>) -> Lit {
        match f {
            Formula::True => {
                let v = self.fresh();
                out.push(vec![v]);
                v
            }
            Formula::Atom(a) => {
                let v = self.atom(a);
                atoms.push(v);
                v
            }
            Formula::Not(x) => -self.encode(x, out, atoms),
            Formula::Implies(a, b) => {
                let lits = vec![-self.encode(a, out, atoms), self.encode(b, out, atoms)];
                self.any(lits, out)
            }
            Formula::And(xs) => {
                let lits: Vec<Lit> = xs.iter().map(|x| self.encode(x, out, atoms)).collect();
                let v = self.fresh();
                let mut long = vec![v];
                for &l in &lits {
                    out.push(vec![-v, l]);
                    long.push(-l);
                }
                out.push(long);
                v
            }
            Formula::Or(xs) => {
                let lits: Vec<Lit> = xs.iter().map(|x| self.encode(x, out, atoms)).collect();
                self.any(lits, out)
            }
        }
    }

    fn any(&mut self, lits: Vec<Lit>, out: &mut Vec<Vec<Lit>>) -> Lit {
        let v = self.fresh();
        let mut long = vec![-v];
        for &l in &lits {
            out.push(vec![v, -l]);
            long.push(l);
        }
        out.push(long);
        v
    }

    /// Adds a formula and returns the index that names it in a query.
    pub fn add(&mut self, formula: &Formula) -> usize {
        let mut clauses = Vec::new();
        let mut atoms = Vec::new();
        let root = self.encode(formula, &mut clauses, &mut atoms);
        clauses.push(vec![root]);
        atoms.sort_unstable();
        atoms.dedup();
        self.formulas.push(Encoded { clauses, atoms });
        self.formulas.len() - 1
    }

    /// `true` when a query was refused because the work limit was reached.
    pub(crate) fn exhausted(&self) -> bool {
        self.work.get() > WORK_LIMIT
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
        let slot = |l: Lit| (l.unsigned_abs() as usize) * 2 + usize::from(l < 0);
        let mut occurs: Vec<Vec<u32>> = vec![Vec::new(); count * 2];
        for (n, clause) in clauses.iter().enumerate() {
            for &l in clause {
                occurs[slot(l)].push(n as u32);
            }
        }
        let mut search = Search { clauses, occurs, assign: vec![0; count], reason: vec![NONE; count], level: vec![0; count], trail: Vec::new(), marks: Vec::new(), head: 0, work: 0 };
        let atom_of = |v: Lit| self.atoms[global[v as usize] as usize].clone().expect("a branching variable is an atom");
        let literal = |l: Lit| Literal { atom: atom_of(l.abs()), positive: l > 0 };
        let mut steps: Vec<Step> = Vec::new();
        let mut size = 0usize;
        let mut made = 0u64;
        let mut next = 0usize;
        // The clauses that are unit or empty before any decision.
        let mut conflict: Option<usize> = (0..search.clauses.len()).find(|&n| !search.visit(n));
        loop {
            if conflict.is_none() {
                conflict = search.propagate();
            }
            let spent = self.work.get().saturating_add(std::mem::take(&mut search.work));
            self.work.set(spent);
            if spent > WORK_LIMIT {
                return Part::Unknown;
            }
            if conflict.is_none() {
                while next < branch.len() && search.assign[branch[next] as usize] != 0 {
                    next += 1;
                }
                if next < branch.len() {
                    made += 1;
                    self.peak.set(self.peak.get().max(made));
                    if made > self.decisions {
                        return Part::Unknown;
                    }
                    search.decide(branch[next]);
                    continue;
                }
                // Every atom has a value, and with it every variable of the encoding: the numbers decide.
                if search.assign.iter().skip(1).any(|v| *v == 0) || !search.satisfied() {
                    return Part::Unknown;
                }
                let assigned: Vec<(Atom, bool)> = numeric_atoms.iter().map(|&v| (atom_of(v), search.assign[v as usize] == 1)).collect();
                match self.theory(&assigned) {
                    Theory::Point(quantities) => {
                        let atoms = branch.iter().map(|&v| (atom_of(v), search.assign[v as usize] == 1)).collect();
                        return Part::Satisfiable(Arc::new(WitnessPart { atoms, quantities }));
                    }
                    Theory::Undecided => return Part::Unknown,
                    Theory::Lemma(lemma, derivation) => {
                        let clause: Vec<Lit> = lemma.iter().map(|l| if l.positive { local[&self.variables[&l.atom]] } else { -local[&self.variables[&l.atom]] }).collect();
                        size += lemma.len() + 1;
                        steps.push(Step { clause: lemma, by: Justification::Linear(derivation) });
                        conflict = Some(search.learn(clause));
                    }
                }
            }
            let Some(at) = conflict.take() else { continue };
            // The decisions that the conflict follows from cannot all hold.
            let involved = search.decisions_behind(at);
            let learned: Vec<Lit> = involved.iter().map(|&d| -d).collect();

            size += learned.len() + 1;
            steps.push(Step { clause: learned.iter().map(|&l| literal(l)).collect(), by: Justification::Propagation });
            if size > REFUTATION_LITERALS {
                return Part::Unknown;
            }
            let mut levels: Vec<u32> = involved.iter().map(|d| search.level[d.unsigned_abs() as usize]).collect();
            levels.sort_unstable();
            let Some(&highest) = levels.last() else {
                if std::env::var("TRION_PROFILE_SEARCH").is_ok() && made > 200 {
                    eprintln!("profile: refuted a part of {} formulas, {} atoms: {made} decisions, {} steps, {size} literals", key.len(), branch.len(), steps.len());
                }
                // No decision is involved: the clauses refute themselves.
                return Part::Unsatisfiable(Arc::new(Refutation { steps }));
            };
            let back = if levels.len() > 1 { levels[levels.len() - 2] } else { 0 };
            let Some(&asserted) = learned.iter().find(|l| search.level[l.unsigned_abs() as usize] == highest) else { return Part::Unknown };
            search.back_to(back);
            let clause = search.learn(learned);
            search.imply(asserted, clause);
            next = 0;
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
        let mut first: HashMap<Quantity, usize> = HashMap::new();
        for (index, (atom, _)) in assigned.iter().enumerate() {
            for (key, _) in numeric(atom).map(|(terms, _, _)| terms).unwrap_or_default() {
                match first.get(&key) {
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
            sets.entry(find(&mut parent, index)).or_default().push(index);
        }
        let mut quantities: Vec<(Quantity, i64)> = Vec::new();
        let mut undecided = false;
        for members in sets.into_values() {
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
            Theory::Point(quantities)
        }
    }
}

enum Theory {
    Point(Vec<(Quantity, i64)>),
    Lemma(Vec<Literal>, LinearDerivation),
    Undecided,
}

/// No clause: the mark of a decision.
const NONE: u32 = u32::MAX;

/// The state of one search: an assignment with its trail, and for each
/// variable the clause that forced its value and the decisions before it.
struct Search {
    clauses: Vec<Vec<Lit>>,
    /// For each literal, the clauses that hold it.
    occurs: Vec<Vec<u32>>,
    assign: Vec<i8>,
    reason: Vec<u32>,
    level: Vec<u32>,
    trail: Vec<Lit>,
    /// The length of the trail before each decision.
    marks: Vec<usize>,
    head: usize,
    work: u64,
}

impl Search {
    fn value(&self, l: Lit) -> i8 {
        let v = self.assign[l.unsigned_abs() as usize];
        if l > 0 {
            v
        } else {
            -v
        }
    }

    fn imply(&mut self, l: Lit, clause: usize) {
        let v = l.unsigned_abs() as usize;
        self.assign[v] = if l > 0 { 1 } else { -1 };
        self.reason[v] = clause as u32;
        self.level[v] = self.marks.len() as u32;
        self.trail.push(l);
    }

    /// Makes an atom true as a decision.
    fn decide(&mut self, v: Lit) {
        self.marks.push(self.trail.len());
        let at = v as usize;
        self.assign[at] = 1;
        self.reason[at] = NONE;
        self.level[at] = self.marks.len() as u32;
        self.trail.push(v);
    }

    /// Takes back every decision after the first `level` ones.
    fn back_to(&mut self, level: u32) {
        let Some(&mark) = self.marks.get(level as usize) else { return };
        while self.trail.len() > mark {
            if let Some(l) = self.trail.pop() {
                self.assign[l.unsigned_abs() as usize] = 0;
            }
        }
        self.marks.truncate(level as usize);
        self.head = self.trail.len();
    }

    /// Looks at one clause: `false` when every literal is false. A clause
    /// with one literal left makes that literal true.
    fn visit(&mut self, n: usize) -> bool {
        self.work += 1;
        let mut unit = None;
        let mut free = 0;
        for &l in &self.clauses[n] {
            match self.value(l) {
                1 => return true,
                0 => {
                    // A literal that stands twice in a clause is one literal.
                    if unit != Some(l) {
                        free += 1;
                    }
                    unit = Some(l);
                }
                _ => {}
            }
        }
        match (free, unit) {
            (0, _) => false,
            (1, Some(l)) => {
                self.imply(l, n);
                true
            }
            _ => true,
        }
    }

    /// Unit propagation; the clause of a conflict when there is one.
    fn propagate(&mut self) -> Option<usize> {
        while self.head < self.trail.len() {
            let l = self.trail[self.head];
            self.head += 1;
            let slot = (l.unsigned_abs() as usize) * 2 + usize::from(l > 0);
            for at in 0..self.occurs[slot].len() {
                let n = self.occurs[slot][at] as usize;
                if !self.visit(n) {
                    return Some(n);
                }
            }
        }
        None
    }

    /// The decisions that make every literal of the clause false, as they were made.
    fn decisions_behind(&self, clause: usize) -> Vec<Lit> {
        let mut seen = vec![false; self.assign.len()];
        let mut open: Vec<usize> = self.clauses[clause].iter().map(|l| l.unsigned_abs() as usize).collect();
        let mut found = Vec::new();
        while let Some(v) = open.pop() {
            if std::mem::replace(&mut seen[v], true) {
                continue;
            }
            match self.reason[v] {
                NONE => found.push(if self.assign[v] == 1 { v as Lit } else { -(v as Lit) }),
                reason => open.extend(self.clauses[reason as usize].iter().map(|l| l.unsigned_abs() as usize).filter(|&other| other != v)),
            }
        }
        found.sort_unstable_by_key(|d| self.level[d.unsigned_abs() as usize]);
        found
    }

    fn satisfied(&self) -> bool {
        self.clauses.iter().all(|clause| clause.iter().any(|&l| self.value(l) == 1))
    }

    /// Adds a clause and returns its index.
    fn learn(&mut self, clause: Vec<Lit>) -> usize {
        let n = self.clauses.len();
        for &l in &clause {
            self.occurs[(l.unsigned_abs() as usize) * 2 + usize::from(l < 0)].push(n as u32);
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
