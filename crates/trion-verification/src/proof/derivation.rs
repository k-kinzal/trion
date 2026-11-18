//! A refutation of trion's solver, stated over the terms of its problem.
//!
//! The solver refutes a set of formulas with clauses over its own encoding
//! ([`trion_solver::Refutation`]): each clause follows by unit propagation
//! from the clauses before it, or it is a linear lemma whose negation the
//! Farkas multipliers of its derivation refute, with case splits on
//! disequalities. A proof checker reads the SMT-LIB problem instead, so a
//! certificate must speak of the terms of the problem. [`derive`] restates
//! the refutation as a [`Derivation`]: clauses whose literals are the terms
//! of the problem, each justified by one step of a small calculus that both
//! formats of proofs that trion writes have.
//!
//! | Step | Clause | Alethe | CPC |
//! | - | - | - | - |
//! | assumption | an assertion of the problem | `assume` | `assume` |
//! | definition | a clause of the Tseitin encoding of an `and`, `or` or `=>` term, `true`, `(not false)` | `and_pos`, …, `true`, `false` | `cnf_and_pos`, …, `refl` |
//! | double negation | the premise with `(not (not t))` written `t` | `not_not` and `resolution` | `split` and `resolution` |
//! | factoring | the premise with each literal once | `contraction` | `factoring` |
//! | resolution | of two clauses on a pivot | `resolution` | `resolution` |
//! | Farkas lemma | literals over comparisons whose negations sum to a false constant comparison, after integer tightening | `la_generic` | the arithmetic rules in a scope |
//! | trichotomy | `(= s v)`, `(not (<= s v))`, `(not (<= v s))` | `la_disequality` | `arith_trichotomy` in a scope |
//!
//! How the refutation is restated:
//!
//! - Each term of the problem that is not a negation is a *base*; a literal
//!   is a base or its negation, and `(not (not t))` is the literal of `t`.
//!   Each `and`, `or` and `=>` base has the clauses of its definition.
//! - A subformula of the solver is named by its connective and the literals
//!   of its parts; it is the base with the same connective and parts (`(=> a
//!   b)` is "some of `(not a)`, `b`"). Two bases that the solver takes for one
//!   subformula are related by two clauses that unit propagation derives
//!   from their definitions; with them, unit propagation over the bases
//!   simulates it over the solver's encoding.
//! - A clause that follows by unit propagation is derived by resolution:
//!   unit propagation from its negation runs to a conflict, and the clauses
//!   that forced each literal on the way are resolved into the conflict, in
//!   the reverse order of the assignment (conflict analysis). What remains
//!   is a subset of the clause, which serves in its place.
//! - A linear lemma becomes one Farkas lemma for each leaf of its
//!   derivation; a split of `s ≠ v` into `s ≤ v − 1` and `s ≥ v + 1` adds
//!   `(<= v s)` or `(<= s v)` to the lemmas of its branches, which the
//!   trichotomy of `s` and `v` resolves away. Each Farkas lemma is checked
//!   here, in its own arithmetic: its rows must sum to a false constant.
//!
//! Nothing here trusts the solver: a step that cannot be restated is an
//! error, and no derivation is returned.

use super::smt::{apply, boolean, not, Names};
use smtlib::lexicon::SpecConstant;
use smtlib::Term;
use std::collections::{BTreeMap, HashMap, HashSet};
use trion_solver::{Connective, Formula, Justification, LinearDerivation, LinearSource, Literal, Operand, Refutation};

/// A clause of a [`Derivation`], justified by one step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Step {
    /// The literals, in the order in which the step concludes them.
    pub(crate) clause: Vec<Term>,
    pub(crate) how: How,
}

/// How a step concludes its clause. A premise is the index of an earlier step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum How {
    /// The assertion at this index of the problem: the clause of one literal.
    Assume(usize),
    /// A clause of the definition of a term.
    Definition(Definition, Term),
    /// The premise, with its literal `(not (not inner))` written `inner`, last.
    Unwrap { premise: usize, inner: Term },
    /// The premise with each literal once, at its first place.
    Factor(usize),
    /// The literals of `left` without `pivot` (or `(not pivot)` when
    /// `polarity` is false), then those of `right` without its negation.
    Resolve { left: usize, right: usize, pivot: Term, polarity: bool },
    /// Literals over comparisons whose negations, each scaled by its
    /// weight, sum to a false comparison of constants.
    Farkas(Vec<Row>),
    /// `(= sum value)`, `(not (<= sum value))`, `(not (<= value sum))`.
    Trichotomy { sum: Term, value: Term },
}

/// The clauses that define a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Definition {
    /// `(not (and t…))`, `tᵢ`.
    AndPos(usize),
    /// `(and t…)`, `(not t₁)`, …, `(not tₙ)`.
    AndNeg,
    /// `(not (or t…))`, `t₁`, …, `tₙ`.
    OrPos,
    /// `(or t…)`, `(not tᵢ)`.
    OrNeg(usize),
    /// `(not (=> a b))`, `(not a)`, `b`.
    ImpliesPos,
    /// `(=> a b)`, `a`.
    ImpliesNeg1,
    /// `(=> a b)`, `(not b)`.
    ImpliesNeg2,
    /// `true`.
    True,
    /// `(not false)`.
    False,
}

/// A comparison of integer terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Op {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
}

impl Op {
    fn of(name: &str) -> Option<Op> {
        Some(match name {
            "<=" => Op::Le,
            "<" => Op::Lt,
            ">=" => Op::Ge,
            ">" => Op::Gt,
            "=" => Op::Eq,
            _ => return None,
        })
    }
}

/// `(op left right)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Relation {
    pub(crate) op: Op,
    pub(crate) left: Term,
    pub(crate) right: Term,
}

/// The weight of a row of a Farkas lemma.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Weight {
    /// The multiplier of the one inequality that the negation of the literal is.
    One(i128),
    /// The negation of the literal is an equation `left = right`: the
    /// multipliers of `left ≤ right` and of `left ≥ right`.
    Equality { upper: i128, lower: i128 },
}

/// One literal of a Farkas lemma: the negation of the literal, an
/// inequality or an equation, enters the sum with its weight.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Row {
    /// The literal: the relation, or its negation when `positive` is false.
    pub(crate) literal: Term,
    pub(crate) relation: Relation,
    pub(crate) positive: bool,
    pub(crate) weight: Weight,
}

/// A refutation of a problem over the terms of the problem: steps whose
/// last concludes the empty clause. Its formats are written by
/// [`Derivation::alethe`] and [`Derivation::cpc`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Derivation {
    /// The assertions of the problem, in its order.
    pub(crate) assertions: Vec<Term>,
    pub(crate) steps: Vec<Step>,
}

impl Derivation {
    /// The number of steps.
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Whether there is no step; never true of a derivation that [`derive`]
    /// returns.
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

/// The terms of a negation, of a function application and of a constant.
pub(crate) fn negated(term: &Term) -> Option<&Term> {
    match application(term) {
        Some(("not", [inner])) => Some(inner),
        _ => None,
    }
}

pub(crate) fn application(term: &Term) -> Option<(&str, &[Term])> {
    match term {
        Term::Application(head, args) if head.sort().is_none() => head.identifier().as_simple().map(|s| (s.as_str(), &args[..])),
        _ => None,
    }
}

fn constant_name(term: &Term) -> Option<&str> {
    match term {
        Term::Identifier(head) if head.sort().is_none() => head.identifier().as_simple().map(|s| s.as_str()),
        _ => None,
    }
}

/// The relation of a comparison term.
pub(crate) fn relation(term: &Term) -> Option<Relation> {
    match application(term) {
        Some((name, [left, right])) => Op::of(name).map(|op| Relation { op, left: left.clone(), right: right.clone() }),
        _ => None,
    }
}

/// A term with its negations removed, and whether their number is even.
fn strip(mut term: &Term) -> (&Term, bool) {
    let mut positive = true;
    while let Some(inner) = negated(term) {
        term = inner;
        positive = !positive;
    }
    (term, positive)
}

/// The literal term of a base with a polarity.
fn literal_term(base: &Term, positive: bool) -> Term {
    if positive {
        base.clone()
    } else {
        not(base.clone())
    }
}

/// A literal of the encoding: base `b` is `2b`, its negation `2b + 1`.
type Lit = u32;

fn negate(l: Lit) -> Lit {
    l ^ 1
}

fn base_of(l: Lit) -> usize {
    (l >> 1) as usize
}

fn is_positive(l: Lit) -> bool {
    l & 1 == 0
}

/// Where a clause of the encoding comes from.
#[derive(Debug, Clone)]
enum Origin {
    Assertion(usize),
    Definition(Definition, usize),
    Derived,
}

/// A clause of the encoding, with the step that concludes it once it is
/// written.
#[derive(Debug, Clone)]
struct Entry {
    lits: Vec<Lit>,
    origin: Origin,
    step: Option<usize>,
}

/// The assignment of one unit propagation.
#[derive(Debug, Default)]
struct Assignment {
    /// For each base: 1 true, -1 false, 0 open.
    value: Vec<i8>,
    /// For each assigned base, the clause that forced it; `None` for an assumption.
    reason: Vec<Option<usize>>,
    trail: Vec<Lit>,
}

impl Assignment {
    fn of(&self, l: Lit) -> i8 {
        let v = self.value[base_of(l)];
        if is_positive(l) {
            v
        } else {
            -v
        }
    }

    fn set(&mut self, l: Lit, reason: Option<usize>) {
        self.value[base_of(l)] = if is_positive(l) { 1 } else { -1 };
        self.reason[base_of(l)] = reason;
        self.trail.push(l);
    }

    fn clear(&mut self, bases: usize) {
        for l in self.trail.drain(..) {
            self.value[base_of(l)] = 0;
            self.reason[base_of(l)] = None;
        }
        self.value.resize(bases, 0);
        self.reason.resize(bases, None);
    }
}

struct Builder<'a> {
    names: &'a Names,
    assertions: Vec<Term>,
    bases: Vec<Term>,
    index: HashMap<Term, usize>,
    /// The base of each connective with the literals of its parts, and
    /// for each base the literal that stands for it there.
    signatures: HashMap<(Connective, Vec<Lit>), Lit>,
    canonical: Vec<Lit>,
    /// Bases that the solver takes for one subformula: the first, then the other.
    links: Vec<(Lit, Lit)>,
    entries: Vec<Entry>,
    known: HashSet<Vec<Lit>>,
    watches: Vec<Vec<usize>>,
    units: Vec<usize>,
    assignment: Assignment,
    steps: Vec<Step>,
    /// The step of the empty clause, once there is one.
    empty: Option<usize>,
}

/// Restates the refutation of `assertions` over the terms that `names`
/// gives them. The assertions are those of the problem, in its order; the
/// refutation is one that `trion_checker` accepts for them.
pub fn derive(names: &Names, assertions: &[Formula], refutation: &Refutation) -> Result<Derivation, String> {
    let terms = assertions.iter().map(|f| names.term(f)).collect::<Result<Vec<_>, _>>()?;
    let mut builder = Builder { names, assertions: terms.clone(), bases: Vec::new(), index: HashMap::new(), signatures: HashMap::new(), canonical: Vec::new(), links: Vec::new(), entries: Vec::new(), known: HashSet::new(), watches: Vec::new(), units: Vec::new(), assignment: Assignment::default(), steps: Vec::new(), empty: None };
    for (k, term) in terms.iter().enumerate() {
        let l = builder.literal(term);
        builder.add(vec![l], Origin::Assertion(k));
    }
    builder.link()?;
    builder.restate(refutation)?;
    let Some(last) = builder.empty else { return Err("the refutation ends without the empty clause".to_string()) };
    builder.steps.truncate(last + 1);
    Ok(Derivation { assertions: builder.assertions, steps: builder.steps })
}

impl Builder<'_> {
    // The bases and their definitions.

    /// The literal of a term, with the bases of the term and of its parts.
    fn literal(&mut self, term: &Term) -> Lit {
        let (base, positive) = strip(term);
        let b = self.base(base);
        let l = (b as Lit) << 1;
        if positive {
            l
        } else {
            negate(l)
        }
    }

    fn base(&mut self, term: &Term) -> usize {
        if let Some(&b) = self.index.get(term) {
            return b;
        }
        let shape: Option<(Connective, Vec<Lit>, Vec<Definition>)> = match (constant_name(term), application(term)) {
            (Some("true"), _) => Some((Connective::True, Vec::new(), vec![Definition::True])),
            (Some("false"), _) => Some((Connective::Any, Vec::new(), vec![Definition::False])),
            (_, Some(("and", parts))) => {
                let lits = parts.iter().map(|p| self.literal(p)).collect();
                Some((Connective::All, lits, (0..parts.len()).map(Definition::AndPos).chain([Definition::AndNeg]).collect()))
            }
            (_, Some(("or", parts))) => {
                let lits = parts.iter().map(|p| self.literal(p)).collect();
                Some((Connective::Any, lits, [Definition::OrPos].into_iter().chain((0..parts.len()).map(Definition::OrNeg)).collect()))
            }
            (_, Some(("=>", [a, b]))) => {
                let lits = vec![negate(self.literal(a)), self.literal(b)];
                Some((Connective::Any, lits, vec![Definition::ImpliesPos, Definition::ImpliesNeg1, Definition::ImpliesNeg2]))
            }
            _ => None,
        };
        let b = self.bases.len();
        self.bases.push(term.clone());
        self.index.insert(term.clone(), b);
        self.watches.extend([Vec::new(), Vec::new()]);
        let me = (b as Lit) << 1;
        self.canonical.push(me);
        if let Some((connective, lits, definitions)) = shape {
            let key = (connective, lits.iter().map(|l| self.canon(*l)).collect::<Vec<_>>());
            match self.signatures.get(&key) {
                Some(&first) => {
                    self.canonical[b] = first;
                    self.links.push((first, me));
                }
                None => {
                    self.signatures.insert(key, me);
                }
            }
            // `true` is also the conjunction of nothing.
            if connective == Connective::True {
                self.signatures.entry((Connective::All, Vec::new())).or_insert(me);
            }
            for definition in definitions {
                let clause = self.definition(definition, term);
                let lits = clause.iter().map(|t| self.literal(t)).collect();
                self.add(lits, Origin::Definition(definition, b));
            }
        }
        b
    }

    /// The literal that stands for `l` in the signatures.
    fn canon(&self, l: Lit) -> Lit {
        let c = self.canonical[base_of(l)];
        if is_positive(l) {
            c
        } else {
            negate(c)
        }
    }

    /// The clause of a definition of `term`, as its rule concludes it.
    fn definition(&self, definition: Definition, term: &Term) -> Vec<Term> {
        let parts: &[Term] = application(term).map_or(&[], |(_, parts)| parts);
        let negation = || not(term.clone());
        match definition {
            Definition::AndPos(i) => vec![negation(), parts[i].clone()],
            Definition::AndNeg => [term.clone()].into_iter().chain(parts.iter().map(|p| not(p.clone()))).collect(),
            Definition::OrPos => [negation()].into_iter().chain(parts.iter().cloned()).collect(),
            Definition::OrNeg(i) => vec![term.clone(), not(parts[i].clone())],
            Definition::ImpliesPos => vec![negation(), not(parts[0].clone()), parts[1].clone()],
            Definition::ImpliesNeg1 => vec![term.clone(), parts[0].clone()],
            Definition::ImpliesNeg2 => vec![term.clone(), not(parts[1].clone())],
            Definition::True => vec![boolean(true)],
            Definition::False => vec![not(boolean(false))],
        }
    }

    // The clauses of the encoding and unit propagation over them.

    /// Adds a clause; a tautology or a clause that is there already is not
    /// added. Returns the clause, if it was added.
    fn add(&mut self, mut lits: Vec<Lit>, origin: Origin) -> Option<usize> {
        lits.sort_unstable();
        lits.dedup();
        if lits.windows(2).any(|w| w[1] == negate(w[0])) || !self.known.insert(lits.clone()) {
            return None;
        }
        let e = self.entries.len();
        match lits.len() {
            0 => {}
            1 => self.units.push(e),
            _ => {
                self.watches[lits[0] as usize].push(e);
                self.watches[lits[1] as usize].push(e);
            }
        }
        self.entries.push(Entry { lits, origin, step: None });
        Some(e)
    }

    /// Unit propagation from the units and the assumptions: the clause whose
    /// literals are all false, if one is reached.
    fn propagate(&mut self, assumptions: &[Lit]) -> Option<usize> {
        self.assignment.clear(self.bases.len());
        for k in 0..self.units.len() {
            let e = self.units[k];
            let l = self.entries[e].lits[0];
            match self.assignment.of(l) {
                1 => {}
                -1 => return Some(e),
                _ => self.assignment.set(l, Some(e)),
            }
        }
        for &l in assumptions {
            match self.assignment.of(l) {
                1 => {}
                // The negation of the assumption was forced: its reason
                // holds the negation of the assumption, a literal of the
                // clause to derive, and conflict analysis starts there.
                -1 => return self.assignment.reason[base_of(l)],
                _ => self.assignment.set(l, None),
            }
        }
        let mut head = 0;
        while head < self.assignment.trail.len() {
            let falsified = negate(self.assignment.trail[head]);
            head += 1;
            let watching = std::mem::take(&mut self.watches[falsified as usize]);
            let mut kept = Vec::with_capacity(watching.len());
            let mut conflict = None;
            for (k, &e) in watching.iter().enumerate() {
                if conflict.is_some() {
                    kept.extend_from_slice(&watching[k..]);
                    break;
                }
                let lits = &mut self.entries[e].lits;
                if lits[0] == falsified {
                    lits.swap(0, 1);
                }
                if self.assignment.of(lits[0]) == 1 {
                    kept.push(e);
                    continue;
                }
                if let Some(free) = (2..lits.len()).find(|&j| self.assignment.of(lits[j]) != -1) {
                    lits.swap(1, free);
                    let watched = lits[1] as usize;
                    self.watches[watched].push(e);
                    continue;
                }
                kept.push(e);
                let first = lits[0];
                if self.assignment.of(first) == -1 {
                    conflict = Some(e);
                } else {
                    self.assignment.set(first, Some(e));
                }
            }
            self.watches[falsified as usize] = kept;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }

    // The steps.

    fn push(&mut self, clause: Vec<Term>, how: How) -> usize {
        self.steps.push(Step { clause, how });
        self.steps.len() - 1
    }

    /// The step of a clause of the encoding, written when first needed.
    fn written(&mut self, e: usize) -> usize {
        if let Some(step) = self.entries[e].step {
            return step;
        }
        let step = match self.entries[e].origin.clone() {
            Origin::Assertion(k) => {
                let s = self.push(vec![self.assertions[k].clone()], How::Assume(k));
                self.normalized(s)
            }
            Origin::Definition(definition, b) => {
                let term = self.bases[b].clone();
                let clause = self.definition(definition, &term);
                let s = self.push(clause, How::Definition(definition, term));
                self.normalized(s)
            }
            Origin::Derived => unreachable!("a derived clause is entered with its step"),
        };
        self.entries[e].step = Some(step);
        step
    }

    /// The step with each `(not (not t))` written `t` and each literal once.
    /// A clause is factored before each resolution, since resolution may
    /// remove each occurrence of its pivot (Carcara does) or only one (CPC).
    fn normalized(&mut self, mut step: usize) -> usize {
        loop {
            step = self.factored(step);
            let Some(at) = self.steps[step].clause.iter().position(|t| negated(t).and_then(negated).is_some()) else { return step };
            let mut clause = self.steps[step].clause.clone();
            let doubled = clause.remove(at);
            let inner = negated(&doubled).and_then(negated).cloned().unwrap_or_else(|| unreachable!());
            clause.push(inner.clone());
            step = self.push(clause, How::Unwrap { premise: step, inner });
        }
    }

    fn factored(&mut self, step: usize) -> usize {
        let clause = &self.steps[step].clause;
        let mut seen = HashSet::new();
        let once: Vec<Term> = clause.iter().filter(|t| seen.insert((*t).clone())).cloned().collect();
        if once.len() == clause.len() {
            step
        } else {
            self.push(once, How::Factor(step))
        }
    }

    /// Resolves two steps on a base: `polarity` is whether the base itself
    /// (rather than its negation) is a literal of `left`.
    fn resolve(&mut self, left: usize, right: usize, pivot: &Term, polarity: bool) -> Result<usize, String> {
        let here = literal_term(pivot, polarity);
        let there = literal_term(pivot, !polarity);
        let mut clause = self.steps[left].clause.clone();
        let at = clause.iter().position(|t| *t == here).ok_or("a resolution misses its pivot on the left")?;
        clause.remove(at);
        let mut other = self.steps[right].clause.clone();
        let at = other.iter().position(|t| *t == there).ok_or("a resolution misses its pivot on the right")?;
        other.remove(at);
        clause.extend(other);
        let step = self.push(clause, How::Resolve { left, right, pivot: pivot.clone(), polarity });
        Ok(self.factored(step))
    }

    /// The literals of a step's clause.
    fn lits(&mut self, step: usize) -> Vec<Lit> {
        let clause = self.steps[step].clause.clone();
        clause.iter().map(|t| self.literal(t)).collect()
    }

    /// Enters a derived clause; the empty clause ends the derivation.
    fn derived(&mut self, step: usize) {
        let lits = self.lits(step);
        if lits.is_empty() {
            self.empty.get_or_insert(step);
        }
        if let Some(e) = self.add(lits, Origin::Derived) {
            self.entries[e].step = Some(step);
        }
    }

    /// A subset of `clause` by resolution, if unit propagation from its
    /// negation reaches a conflict.
    fn by_propagation(&mut self, clause: &[Lit]) -> Option<usize> {
        let assumptions: Vec<Lit> = clause.iter().map(|l| negate(*l)).collect();
        let conflict = self.propagate(&assumptions)?;
        let trail = self.assignment.trail.clone();
        let reasons: Vec<Option<usize>> = trail.iter().map(|l| self.assignment.reason[base_of(*l)]).collect();
        let mut step = self.written(conflict);
        let mut current: HashSet<Lit> = self.lits(step).into_iter().collect();
        for (t, reason) in trail.iter().zip(reasons).rev() {
            let Some(reason) = reason else { continue };
            if !current.contains(&negate(*t)) {
                continue;
            }
            let right = self.written(reason);
            let pivot = self.bases[base_of(*t)].clone();
            // The current clause holds the negation of `t`.
            step = self.resolve(step, right, &pivot, !is_positive(*t)).ok()?;
            current = self.lits(step).into_iter().collect();
        }
        Some(step)
    }

    /// Relates the bases that the solver takes for one subformula, both ways.
    fn link(&mut self) -> Result<(), String> {
        for (first, other) in self.links.clone() {
            for clause in [[negate(first), other], [negate(other), first]] {
                let step = self.by_propagation(&clause).ok_or_else(|| format!("{} and {} are not related by their definitions", self.bases[base_of(first)], self.bases[base_of(other)]))?;
                self.derived(step);
            }
        }
        Ok(())
    }

    // The refutation.

    fn atom(&mut self, literal: &Literal) -> Result<(Lit, Term), String> {
        let term = self.names.atom_term(&literal.atom)?;
        let l = self.literal(&term);
        Ok(if literal.positive { (l, term) } else { (negate(l), not(term)) })
    }

    fn restate(&mut self, refutation: &Refutation) -> Result<(), String> {
        let mut defined: Vec<Lit> = Vec::new();
        for (k, definition) in refutation.definitions.iter().enumerate() {
            let mut parts = Vec::new();
            for operand in &definition.operands {
                parts.push(match operand {
                    Operand::Atom(literal) => self.atom(literal)?.0,
                    Operand::Formula { definition, positive } => {
                        let l = *defined.get(*definition).ok_or_else(|| format!("definition {k} names a definition that does not stand before it"))?;
                        if *positive {
                            l
                        } else {
                            negate(l)
                        }
                    }
                });
            }
            let l = match (definition.connective, parts.len()) {
                (Connective::True, _) | (Connective::All, 0) => self.literal(&boolean(true)),
                (Connective::Any, 0) => self.literal(&boolean(false)),
                (_, 1) => parts[0],
                (connective, _) => {
                    let key = (connective, parts.iter().map(|l| self.canon(*l)).collect::<Vec<_>>());
                    *self.signatures.get(&key).ok_or_else(|| format!("definition {k} names no subformula of the problem"))?
                }
            };
            defined.push(l);
        }
        for (n, step) in refutation.steps.iter().enumerate() {
            if self.empty.is_some() {
                break;
            }
            let mut clause = Vec::new();
            let mut atoms = Vec::new();
            for literal in &step.clause {
                let (l, term) = self.atom(literal)?;
                clause.push(l);
                atoms.push((l, term, literal.positive));
            }
            for (definition, positive) in &step.formulas {
                let l = *defined.get(*definition).ok_or_else(|| format!("step {n} names a subformula without a definition"))?;
                clause.push(if *positive { l } else { negate(l) });
            }
            let mut sorted = clause.clone();
            sorted.sort_unstable();
            sorted.dedup();
            if sorted.windows(2).any(|w| w[1] == negate(w[0])) {
                continue;
            }
            let derived = match &step.by {
                Justification::Propagation => self.by_propagation(&clause).ok_or_else(|| format!("step {n} does not follow by unit propagation over the terms of the problem"))?,
                Justification::Linear(derivation) => self.lemma(&atoms, derivation, &mut Vec::new()).map_err(|e| format!("step {n}: {e}"))?,
            };
            let lits = self.lits(derived);
            if let Some(extra) = lits.iter().find(|l| !clause.contains(l)) {
                return Err(format!("step {n} derives {}, which is no literal of its clause", self.bases[base_of(*extra)]));
            }
            self.derived(derived);
        }
        Ok(())
    }

    /// The Farkas lemmas and trichotomies of a linear lemma: a clause whose
    /// literals are among those of `clause` that the derivation uses.
    /// `extra` holds the literal of each split that encloses this node.
    fn lemma(&mut self, clause: &[(Lit, Term, bool)], derivation: &LinearDerivation, extra: &mut Vec<Term>) -> Result<usize, String> {
        match derivation {
            LinearDerivation::Leaf { multipliers } => {
                let mut rows: Vec<Row> = Vec::new();
                for (source, by) in multipliers {
                    if *by == 0 {
                        continue;
                    }
                    let (literal, positive, upper) = match source {
                        LinearSource::Literal { index, side } => {
                            let (_, term, positive) = clause.get(*index).ok_or("a leaf names a literal that the clause does not have")?;
                            (term.clone(), *positive, *side == trion_solver::Side::Upper)
                        }
                        LinearSource::Split(depth) => (extra.get(*depth).ok_or("a leaf names a split that does not enclose it")?.clone(), true, true),
                    };
                    let atom = if positive { literal.clone() } else { negated(&literal).cloned().unwrap_or_else(|| unreachable!()) };
                    let relation = relation(&atom).ok_or_else(|| format!("{atom} is no comparison"))?;
                    if positive && relation.op == Op::Eq {
                        return Err(format!("a leaf uses the disequality that {literal} denies"));
                    }
                    let row = match rows.iter_mut().find(|r| r.literal == literal) {
                        Some(row) => row,
                        None => {
                            let weight = if relation.op == Op::Eq { Weight::Equality { upper: 0, lower: 0 } } else { Weight::One(0) };
                            rows.push(Row { literal, relation, positive, weight });
                            rows.last_mut().unwrap_or_else(|| unreachable!())
                        }
                    };
                    let add = |a: i128| a.checked_add(*by).ok_or("a multiplier overflows");
                    row.weight = match row.weight {
                        Weight::One(m) => Weight::One(add(m)?),
                        Weight::Equality { upper: u, lower: l } if upper => Weight::Equality { upper: add(u)?, lower: l },
                        Weight::Equality { upper: u, lower: l } => Weight::Equality { upper: u, lower: add(l)? },
                    };
                }
                farkas(&rows)?;
                let literals = rows.iter().map(|r| r.literal.clone()).collect();
                Ok(self.push(literals, How::Farkas(rows)))
            }
            LinearDerivation::Split { literal, below, above } => {
                let (_, term, positive) = clause.get(*literal).ok_or("a split names a literal that the clause does not have")?;
                let relation = relation(term).filter(|r| *positive && r.op == Op::Eq).ok_or_else(|| format!("a split names {term}, whose negation is no disequality"))?;
                let (sum, value) = (relation.left, relation.right);
                let at_least = apply("<=", vec![value.clone(), sum.clone()]);
                let at_most = apply("<=", vec![sum.clone(), value.clone()]);
                extra.push(at_least.clone());
                let low = self.lemma(clause, below, extra);
                extra.pop();
                let low = low?;
                if !self.steps[low].clause.contains(&at_least) {
                    return Ok(low);
                }
                extra.push(at_most.clone());
                let high = self.lemma(clause, above, extra);
                extra.pop();
                let high = high?;
                if !self.steps[high].clause.contains(&at_most) {
                    return Ok(high);
                }
                let trichotomy = vec![term.clone(), not(at_most.clone()), not(at_least.clone())];
                let split = self.push(trichotomy, How::Trichotomy { sum, value });
                let step = self.resolve(split, low, &at_least, false)?;
                self.resolve(step, high, &at_most, false)
            }
        }
    }
}

/// A linear polynomial with integer coefficients over the constants of a
/// problem: the coefficient of each constant, none of them zero, and the
/// constant part.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Poly {
    pub(crate) coefficients: BTreeMap<Term, i128>,
    pub(crate) constant: i128,
}

const OVERFLOW: &str = "a number of a Farkas lemma overflows";

impl Poly {
    fn number(n: i128) -> Poly {
        Poly { coefficients: BTreeMap::new(), constant: n }
    }

    /// `self + by · other`.
    pub(crate) fn add(mut self, by: i128, other: &Poly) -> Result<Poly, String> {
        for (x, c) in &other.coefficients {
            let entry = self.coefficients.entry(x.clone()).or_insert(0);
            *entry = c.checked_mul(by).and_then(|c| entry.checked_add(c)).ok_or(OVERFLOW)?;
            if *entry == 0 {
                self.coefficients.remove(x);
            }
        }
        self.constant = other.constant.checked_mul(by).and_then(|c| self.constant.checked_add(c)).ok_or(OVERFLOW)?;
        Ok(self)
    }

    /// The polynomial of an integer term built from numerals, constants,
    /// `+`, `-` and `*` by a number: the terms that trion writes.
    pub(crate) fn of(term: &Term) -> Result<Poly, String> {
        if let Term::Constant(SpecConstant::Numeral(n)) = term {
            return n.as_str().parse().map(Poly::number).map_err(|_| OVERFLOW.to_string());
        }
        if constant_name(term).is_some() {
            return Ok(Poly { coefficients: BTreeMap::from([(term.clone(), 1)]), constant: 0 });
        }
        let Some((name, args)) = application(term) else { return Err(format!("{term} is no linear term")) };
        match (name, args) {
            ("+", _) => args.iter().try_fold(Poly::default(), |sum, a| sum.add(1, &Poly::of(a)?)),
            ("-", [a]) => Poly::default().add(-1, &Poly::of(a)?),
            ("-", [a, rest @ ..]) => rest.iter().try_fold(Poly::of(a)?, |sum, b| sum.add(-1, &Poly::of(b)?)),
            ("*", _) => {
                let mut product = Poly::number(1);
                for a in args {
                    let factor = Poly::of(a)?;
                    product = match (product.coefficients.is_empty(), factor.coefficients.is_empty()) {
                        (true, _) => Poly::default().add(product.constant, &factor)?,
                        (_, true) => Poly::default().add(factor.constant, &product)?,
                        _ => return Err(format!("{term} is no linear term")),
                    };
                }
                Ok(product)
            }
            _ => Err(format!("{term} is no linear term")),
        }
    }
}

/// The negation of a row's literal as `P ≤ 0` over the integers, with a
/// strict comparison tightened by one, or as `P = 0`; `true` for an equation.
pub(crate) fn constraint(row: &Row) -> Result<(Poly, bool), String> {
    let (a, b) = (Poly::of(&row.relation.left)?, Poly::of(&row.relation.right)?);
    let a_minus_b = a.clone().add(-1, &b)?;
    let b_minus_a = b.add(-1, &a)?;
    let one = Poly::number(1);
    // The negation of the literal is the relation itself when the literal
    // is its negation, and the negated relation otherwise.
    Ok(match (row.relation.op, row.positive) {
        (Op::Le, false) | (Op::Gt, true) => (a_minus_b, false),
        (Op::Lt, false) | (Op::Ge, true) => (a_minus_b.add(1, &one)?, false),
        (Op::Ge, false) | (Op::Lt, true) => (b_minus_a, false),
        (Op::Gt, false) | (Op::Le, true) => (b_minus_a.add(1, &one)?, false),
        (Op::Eq, false) => (a_minus_b, true),
        (Op::Eq, true) => return Err(format!("the negation of {} is no inequality", row.literal)),
    })
}

/// Checks a Farkas lemma: the negations of its literals, each scaled by its
/// weight, sum to `K ≤ 0` with a positive constant `K`.
fn farkas(rows: &[Row]) -> Result<(), String> {
    let mut sum = Poly::default();
    for row in rows {
        let (p, equation) = constraint(row)?;
        let by = match (row.weight, equation) {
            (Weight::One(m), false) if m >= 0 => m,
            (Weight::Equality { upper, lower }, true) => upper.checked_sub(lower).ok_or(OVERFLOW)?,
            _ => return Err(format!("the weight of {} does not fit its negation", row.literal)),
        };
        sum = sum.add(by, &p)?;
    }
    if sum.coefficients.is_empty() && sum.constant > 0 {
        Ok(())
    } else {
        Err("the rows of a Farkas lemma do not sum to a false comparison of constants".to_string())
    }
}
