//! A checker of certificates for the tests. It shares no code with the
//! search: it has its own encoding, its own propagation and its own
//! arithmetic. It is not the kernel; it only keeps the tests honest.
#![allow(dead_code)]

use std::collections::{BTreeMap, HashMap};
use trion_verification::proof::{Answer, Certificate, Justification, LinearDerivation, LinearSource, Literal, Refutation, Side, Witness};
use trion_solver::{Atom, Cmp, Formula, Status};

type Key = (String, String);

fn terms(atom: &Atom) -> Option<(Vec<(Key, i128)>, Cmp, i128)> {
    match atom {
        Atom::Num { attr, unit, cmp, n } => Some((vec![((attr.clone(), unit.clone()), 1)], *cmp, i128::from(*n))),
        Atom::Lin { terms, unit, cmp, n } => Some((terms.iter().map(|(a, c)| ((a.clone(), unit.clone()), i128::from(*c))).collect(), *cmp, i128::from(*n))),
        _ => None,
    }
}

fn holds(formula: &Formula, atoms: &BTreeMap<Atom, bool>) -> Result<bool, String> {
    Ok(match formula {
        Formula::True => true,
        Formula::Atom(a) => *atoms.get(a).ok_or_else(|| format!("the witness has no value for {a}"))?,
        Formula::Not(x) => !holds(x, atoms)?,
        Formula::And(xs) => {
            let mut all = true;
            for x in xs {
                all &= holds(x, atoms)?;
            }
            all
        }
        Formula::Or(xs) => {
            let mut any = false;
            for x in xs {
                any |= holds(x, atoms)?;
            }
            any
        }
        Formula::Implies(a, b) => !holds(a, atoms)? || holds(b, atoms)?,
    })
}

pub fn check_witness(formulas: &[Formula], witness: &Witness) -> Result<(), String> {
    let atoms = witness.atoms();
    let quantities = witness.quantities();
    for (n, formula) in formulas.iter().enumerate() {
        if !holds(formula, &atoms)? {
            return Err(format!("formula {n} is false under the witness: {formula}"));
        }
        let mut error = None;
        formula.atoms(true, &mut |atom, _| {
            let Some((sum, cmp, n)) = terms(atom) else { return };
            let mut total: i128 = 0;
            for (key, coef) in &sum {
                match quantities.get(key) {
                    Some(v) => total += coef * i128::from(*v),
                    None => error = Some(format!("the witness has no integer for {key:?}")),
                }
            }
            let truth = match cmp {
                Cmp::Eq => total == n,
                Cmp::Ge => total >= n,
                Cmp::Le => total <= n,
                Cmp::Gt => total > n,
                Cmp::Lt => total < n,
            };
            if atoms.get(atom) != Some(&truth) {
                error = Some(format!("{atom} is {:?} in the witness and {truth} by its integers", atoms.get(atom)));
            }
        });
        if let Some(error) = error {
            return Err(error);
        }
    }
    Ok(())
}

struct Clauses {
    vars: HashMap<Atom, i32>,
    next: i32,
    clauses: Vec<Vec<i32>>,
}

impl Clauses {
    fn fresh(&mut self) -> i32 {
        self.next += 1;
        self.next
    }

    fn encode(&mut self, f: &Formula) -> i32 {
        match f {
            Formula::True => {
                let v = self.fresh();
                self.clauses.push(vec![v]);
                v
            }
            Formula::Atom(a) => match self.vars.get(a) {
                Some(v) => *v,
                None => {
                    let v = self.fresh();
                    self.vars.insert(a.clone(), v);
                    v
                }
            },
            Formula::Not(x) => -self.encode(x),
            Formula::Implies(a, b) => {
                let (a, b) = (self.encode(a), self.encode(b));
                let v = self.fresh();
                self.clauses.extend([vec![-v, -a, b], vec![v, a], vec![v, -b]]);
                v
            }
            Formula::And(xs) => {
                let lits: Vec<i32> = xs.iter().map(|x| self.encode(x)).collect();
                let v = self.fresh();
                let mut long = vec![v];
                for l in lits {
                    self.clauses.push(vec![-v, l]);
                    long.push(-l);
                }
                self.clauses.push(long);
                v
            }
            Formula::Or(xs) => {
                let lits: Vec<i32> = xs.iter().map(|x| self.encode(x)).collect();
                let v = self.fresh();
                let mut long = vec![-v];
                for l in lits {
                    self.clauses.push(vec![v, -l]);
                    long.push(l);
                }
                self.clauses.push(long);
                v
            }
        }
    }

    /// `true` when unit propagation from the assumptions reaches a conflict.
    fn refutes(&self, assumptions: &[i32]) -> bool {
        let mut value: Vec<i8> = vec![0; self.next as usize + 1];
        let of = |value: &[i8], l: i32| if l > 0 { value[l as usize] } else { -value[(-l) as usize] };
        for &l in assumptions {
            if of(&value, l) == -1 {
                return true;
            }
            value[l.unsigned_abs() as usize] = if l > 0 { 1 } else { -1 };
        }
        loop {
            let mut changed = false;
            for clause in &self.clauses {
                let mut free = None;
                let mut count = 0;
                let mut satisfied = false;
                for &l in clause {
                    match of(&value, l) {
                        1 => {
                            satisfied = true;
                            break;
                        }
                        0 => {
                            count += 1;
                            free = Some(l);
                        }
                        _ => {}
                    }
                }
                if satisfied {
                    continue;
                }
                match (count, free) {
                    (0, _) => return true,
                    (1, Some(l)) => {
                        value[l.unsigned_abs() as usize] = if l > 0 { 1 } else { -1 };
                        changed = true;
                    }
                    _ => {}
                }
            }
            if !changed {
                return false;
            }
        }
    }
}

type Row = (BTreeMap<Key, i128>, i128);

fn row(sum: &[(Key, i128)], sign: i128, bound: i128) -> Row {
    let mut out = BTreeMap::new();
    for (key, coef) in sum {
        *out.entry(key.clone()).or_insert(0) += sign * coef;
    }
    (out, bound)
}

fn linear(node: &LinearDerivation, upper: &[Option<Row>], lower: &[Option<Row>], differs: &[Option<(Vec<(Key, i128)>, i128)>], added: &mut Vec<Row>) -> Result<(), String> {
    match node {
        LinearDerivation::Leaf { multipliers } => {
            let mut total: BTreeMap<Key, i128> = BTreeMap::new();
            let mut bound = 0i128;
            for (source, by) in multipliers {
                if *by < 0 {
                    return Err("a multiplier is negative".to_string());
                }
                let found = match source {
                    LinearSource::Literal { index, side: Side::Upper } => upper.get(*index).cloned().flatten(),
                    LinearSource::Literal { index, side: Side::Lower } => lower.get(*index).cloned().flatten(),
                    LinearSource::Split(depth) => added.get(*depth).cloned(),
                };
                let (sum, limit) = found.ok_or("a leaf names an inequality that does not exist")?;
                for (key, coef) in sum {
                    *total.entry(key).or_insert(0) += coef * by;
                }
                bound += limit * by;
            }
            if total.values().any(|c| *c != 0) {
                return Err("a quantity is left in the sum of a leaf".to_string());
            }
            if bound >= 0 {
                return Err(format!("the sum of a leaf reads 0 ≤ {bound}"));
            }
            Ok(())
        }
        LinearDerivation::Split { literal, below, above } => {
            let (sum, value) = differs.get(*literal).cloned().flatten().ok_or("a split names a literal whose negation is no disequality")?;
            added.push(row(&sum, 1, value - 1));
            let first = linear(below, upper, lower, differs, added);
            added.pop();
            added.push(row(&sum, -1, -(value + 1)));
            let second = linear(above, upper, lower, differs, added);
            added.pop();
            first.and(second)
        }
    }
}

fn check_lemma(clause: &[Literal], derivation: &LinearDerivation) -> Result<(), String> {
    let mut upper = Vec::new();
    let mut lower = Vec::new();
    let mut differs = Vec::new();
    for literal in clause {
        let (sum, cmp, n) = terms(&literal.atom).ok_or_else(|| format!("{} is no numeric atom", literal.atom))?;
        // The negation of the literal of the clause is what is assumed.
        let value = !literal.positive;
        let (up, low, ne) = match (cmp, value) {
            (Cmp::Eq, true) => (Some(n), Some(n), false),
            (Cmp::Eq, false) => (None, None, true),
            (Cmp::Le, true) | (Cmp::Gt, false) => (Some(n), None, false),
            (Cmp::Lt, true) | (Cmp::Ge, false) => (Some(n - 1), None, false),
            (Cmp::Ge, true) | (Cmp::Lt, false) => (None, Some(n), false),
            (Cmp::Gt, true) | (Cmp::Le, false) => (None, Some(n + 1), false),
        };
        upper.push(up.map(|b| row(&sum, 1, b)));
        lower.push(low.map(|b| row(&sum, -1, -b)));
        differs.push(ne.then(|| (sum.clone(), n)));
    }
    linear(derivation, &upper, &lower, &differs, &mut Vec::new())
}

pub fn check_refutation(formulas: &[Formula], refutation: &Refutation) -> Result<(), String> {
    let mut clauses = Clauses { vars: HashMap::new(), next: 0, clauses: Vec::new() };
    for formula in formulas {
        let root = clauses.encode(formula);
        clauses.clauses.push(vec![root]);
    }
    let Some(last) = refutation.steps.last() else { return Err("the refutation is empty".to_string()) };
    if !last.clause.is_empty() {
        return Err("the refutation does not end with the empty clause".to_string());
    }
    for (n, step) in refutation.steps.iter().enumerate() {
        let mut lits = Vec::new();
        for literal in &step.clause {
            let v = *clauses.vars.get(&literal.atom).ok_or_else(|| format!("step {n} names {}, which is no atom of the query", literal.atom))?;
            lits.push(if literal.positive { v } else { -v });
        }
        match &step.by {
            Justification::Propagation => {
                let negated: Vec<i32> = lits.iter().map(|l| -l).collect();
                if !clauses.refutes(&negated) {
                    return Err(format!("step {n} does not follow by unit propagation"));
                }
            }
            Justification::Linear(derivation) => check_lemma(&step.clause, derivation).map_err(|e| format!("step {n}: {e}"))?,
        }
        clauses.clauses.push(lits);
    }
    Ok(())
}

/// Checks the certificate of an answer against the formulas of its query.
pub fn check(formulas: &[Formula], answer: &Answer) -> Result<(), String> {
    match (&answer.status, &answer.certificate) {
        (Status::Satisfiable, Certificate::Witness(witness)) => check_witness(formulas, witness),
        (Status::Unsatisfiable, Certificate::Refutation(refutation)) => check_refutation(formulas, refutation),
        (Status::Unknown, Certificate::None) => Ok(()),
        (status, _) => Err(format!("the status {status:?} carries the wrong kind of certificate")),
    }
}
