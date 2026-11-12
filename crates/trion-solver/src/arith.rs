//! Linear integer constraints over several variables.
//!
//! A numeric atom relates a sum of variables to a number. The search hands
//! the atoms that share variables to [`decide_certified`], which answers in
//! three values: the constraints have an integer solution (with a point),
//! they have none (with a derivation), or this procedure cannot tell.
//!
//! The procedure eliminates one variable after another (Fourier-Motzkin).
//! When that derives `0 ≤ c` with a negative `c`, no rational solution
//! exists, so no integer solution exists either. Otherwise it assigns the
//! variables in the reverse order and looks for an integer point. Difference
//! constraints (`x − y ≤ c`, `x ≤ c`) keep integer bounds throughout, so for
//! them a point is always found and the answer is exact. With other
//! coefficients a rational solution may have no integer point nearby; then
//! the answer is [`Outcome::Undecided`], never a guess.

use std::collections::BTreeMap;

/// What the procedure established for a set of constraints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    /// An integer assignment satisfies every constraint.
    Consistent,
    /// No assignment satisfies every constraint.
    Inconsistent,
    /// The search ended without either result.
    Undecided,
}

/// A sum of variables with integer coefficients.
pub(super) type Sum = Vec<(usize, i128)>;

/// `sum ≤ bound`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct AtMost {
    pub sum: Sum,
    pub bound: i128,
}

/// `sum ≠ value`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Unequal {
    pub sum: Sum,
    pub value: i128,
}

/// The most constraints one elimination may produce before the procedure gives up.
const MAX_CONSTRAINTS: usize = 4000;
/// The most assignments the search for an integer point may try.
const MAX_ATTEMPTS: usize = 4000;

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// Merges equal variables, drops zero coefficients, and divides by the common
/// factor. Dividing rounds the bound down, which is exact for integers.
fn normal(sum: &Sum, bound: i128) -> Option<(BTreeMap<usize, i128>, i128)> {
    let mut merged: BTreeMap<usize, i128> = BTreeMap::new();
    for (var, coef) in sum {
        let entry = merged.entry(*var).or_insert(0);
        *entry = entry.checked_add(*coef)?;
    }
    merged.retain(|_, coef| *coef != 0);
    let factor = merged.values().fold(0, |g, c| gcd(g, *c));
    if factor > 1 {
        for coef in merged.values_mut() {
            *coef /= factor;
        }
        return Some((merged, bound.div_euclid(factor)));
    }
    Some((merged, bound))
}

type Row = (BTreeMap<usize, i128>, i128);

fn evaluate(sum: &BTreeMap<usize, i128>, point: &BTreeMap<usize, i128>) -> Option<i128> {
    sum.iter().try_fold(0i128, |total, (var, coef)| total.checked_add(coef.checked_mul(*point.get(var)?)?))
}

/// The integers that a variable may take given the rows that mention it and
/// the values of the variables assigned so far.
fn interval(var: usize, rows: &[Row], point: &BTreeMap<usize, i128>) -> Option<(Option<i128>, Option<i128>)> {
    let (mut low, mut high): (Option<i128>, Option<i128>) = (None, None);
    for (sum, bound) in rows {
        let coef = *sum.get(&var)?;
        let mut rest = sum.clone();
        rest.remove(&var);
        let room = bound.checked_sub(evaluate(&rest, point)?)?;
        if coef > 0 {
            // coef·x ≤ room
            let limit = room.div_euclid(coef);
            high = Some(high.map_or(limit, |h| h.min(limit)));
        } else {
            // coef·x ≤ room with a negative coef: x ≥ room / coef, rounded up.
            let limit = -(room.div_euclid(-coef));
            low = Some(low.map_or(limit, |l| l.max(limit)));
        }
    }
    Some((low, high))
}

struct Search<'a> {
    /// The variables in the order of their elimination, each with the rows
    /// that mentioned it when it was eliminated.
    stages: &'a [(usize, Vec<Row>)],
    unequal: &'a [Row],
    attempts: usize,
    overflow: bool,
}

impl Search<'_> {
    /// Assigns the variables from the last eliminated to the first.
    fn assign(&mut self, at: usize, point: &mut BTreeMap<usize, i128>) -> bool {
        if at == 0 {
            return self.unequal.iter().all(|(sum, value)| evaluate(sum, point).is_some_and(|total| total != *value));
        }
        let (var, rows) = &self.stages[at - 1];
        let Some((low, high)) = interval(*var, rows, point) else {
            self.overflow = true;
            return false;
        };
        let mut candidates: Vec<i128> = match (low, high) {
            (Some(l), Some(h)) if l > h => Vec::new(),
            (Some(l), Some(h)) => [l, h, l + 1, h - 1, l + 2].into_iter().filter(|c| *c >= l && *c <= h).collect(),
            (Some(l), None) => vec![l, l + 1, l + 2],
            (None, Some(h)) => vec![h, h - 1, h - 2],
            (None, None) => vec![0, 1, -1],
        };
        candidates.dedup();
        let mut seen = Vec::new();
        for candidate in candidates {
            if seen.contains(&candidate) {
                continue;
            }
            seen.push(candidate);
            self.attempts += 1;
            if self.attempts > MAX_ATTEMPTS {
                return false;
            }
            point.insert(*var, candidate);
            if self.assign(at - 1, point) {
                return true;
            }
            point.remove(var);
        }
        false
    }
}

/// The search of [`decide_certified`]: a verdict, and the integer point when one was found.
fn search(at_most: &[AtMost], unequal: &[Unequal]) -> (Verdict, BTreeMap<usize, i128>) {
    let none = BTreeMap::new;
    let mut rows: Vec<Row> = Vec::new();
    for constraint in at_most {
        match normal(&constraint.sum, constraint.bound) {
            Some(row) => rows.push(row),
            None => return (Verdict::Undecided, none()),
        }
    }
    let mut unequal_rows: Vec<Row> = Vec::new();
    for constraint in unequal {
        let mut merged: BTreeMap<usize, i128> = BTreeMap::new();
        for (var, coef) in &constraint.sum {
            *merged.entry(*var).or_insert(0) += *coef;
        }
        merged.retain(|_, coef| *coef != 0);
        if merged.is_empty() {
            if constraint.value == 0 {
                return (Verdict::Inconsistent, none());
            }
            continue;
        }
        unequal_rows.push((merged, constraint.value));
    }
    let mut variables: Vec<usize> = rows.iter().chain(&unequal_rows).flat_map(|(sum, _)| sum.keys().copied()).collect();
    variables.sort_unstable();
    variables.dedup();

    let mut stages: Vec<(usize, Vec<Row>)> = Vec::new();
    for var in variables {
        let (with, without): (Vec<Row>, Vec<Row>) = rows.into_iter().partition(|(sum, _)| sum.contains_key(&var));
        rows = without;
        let upper: Vec<&Row> = with.iter().filter(|(sum, _)| sum[&var] > 0).collect();
        let lower: Vec<&Row> = with.iter().filter(|(sum, _)| sum[&var] < 0).collect();
        for (up, up_bound) in &upper {
            for (low, low_bound) in &lower {
                // a·x + p ≤ b and −c·x + q ≤ d give c·p + a·q ≤ c·b + a·d.
                let (a, c) = (up[&var], -low[&var]);
                let mut sum: Sum = Vec::new();
                let mut exact = true;
                for (v, coef) in up.iter().filter(|(v, _)| **v != var) {
                    match coef.checked_mul(c) {
                        Some(scaled) => sum.push((*v, scaled)),
                        None => exact = false,
                    }
                }
                for (v, coef) in low.iter().filter(|(v, _)| **v != var) {
                    match coef.checked_mul(a) {
                        Some(scaled) => sum.push((*v, scaled)),
                        None => exact = false,
                    }
                }
                let bound = up_bound.checked_mul(c).and_then(|x| low_bound.checked_mul(a).and_then(|y| x.checked_add(y)));
                let (true, Some(bound)) = (exact, bound) else { return (Verdict::Undecided, none()) };
                let Some((sum, bound)) = normal(&sum, bound) else { return (Verdict::Undecided, none()) };
                if sum.is_empty() {
                    if bound < 0 {
                        return (Verdict::Inconsistent, none());
                    }
                    continue;
                }
                if !rows.contains(&(sum.clone(), bound)) {
                    rows.push((sum, bound));
                }
                if rows.len() > MAX_CONSTRAINTS {
                    return (Verdict::Undecided, none());
                }
            }
        }
        stages.push((var, with));
    }
    if rows.iter().any(|(sum, bound)| sum.is_empty() && *bound < 0) {
        return (Verdict::Inconsistent, none());
    }
    let mut search = Search { stages: &stages, unequal: &unequal_rows, attempts: 0, overflow: false };
    let mut point = BTreeMap::new();
    if search.assign(stages.len(), &mut point) {
        return (Verdict::Consistent, point);
    }
    // A variable with no integer between its bounds, with every earlier
    // choice tried, refutes the constraints only when no choice was skipped.
    // The search tries a few values of each variable, so it proves nothing
    // here: the answer stays open, except in the one case below.
    if unequal_rows.is_empty() && stages.len() == 1 && !search.overflow {
        return (Verdict::Inconsistent, none());
    }
    (Verdict::Undecided, none())
}


/// Where an inequality of a derivation comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Source {
    /// The inequality of the given list at this index.
    Given(usize),
    /// The inequality that the split at this depth of the path added.
    Split(usize),
}

/// Why a set of inequalities and disequalities has no integer solution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Derivation {
    /// The inequalities, each multiplied by its non-negative integer, add up
    /// to `0 ≤ c` with a negative `c`.
    Leaf { multipliers: Vec<(Source, i128)> },
    /// The disequality `sum ≠ value` at this index is split: `below` refutes
    /// the rest with `sum ≤ value − 1`, `above` with `sum ≥ value + 1`.
    Split { unequal: usize, below: Box<Derivation>, above: Box<Derivation> },
}

/// What [`decide_certified`] established, with what shows it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Outcome {
    /// The point satisfies every constraint. A variable that it leaves out is 0.
    Consistent(BTreeMap<usize, i128>),
    Inconsistent(Derivation),
    Undecided,
}

/// The most inequalities one derivation step may hold.
const MAX_DERIVED: usize = 600;
/// The most nodes of a derivation that are tried.
const MAX_NODES: usize = 96;

fn merged(sum: &Sum) -> Option<BTreeMap<usize, i128>> {
    let mut out: BTreeMap<usize, i128> = BTreeMap::new();
    for (var, coef) in sum {
        let entry = out.entry(*var).or_insert(0);
        *entry = entry.checked_add(*coef)?;
    }
    out.retain(|_, coef| *coef != 0);
    Some(out)
}

/// A row of the elimination: an inequality with the multipliers that give it.
type Combined = (BTreeMap<usize, i128>, i128, BTreeMap<usize, i128>);

fn scale(row: &Combined, by: i128) -> Option<Combined> {
    let coefs = row.0.iter().map(|(v, c)| c.checked_mul(by).map(|x| (*v, x))).collect::<Option<BTreeMap<_, _>>>()?;
    let combo = row.2.iter().map(|(i, m)| m.checked_mul(by).map(|x| (*i, x))).collect::<Option<BTreeMap<_, _>>>()?;
    Some((coefs, row.1.checked_mul(by)?, combo))
}

fn add(a: Combined, b: &Combined) -> Option<Combined> {
    let (mut coefs, bound, mut combo) = a;
    for (v, c) in &b.0 {
        let entry = coefs.entry(*v).or_insert(0);
        *entry = entry.checked_add(*c)?;
    }
    coefs.retain(|_, c| *c != 0);
    for (i, m) in &b.2 {
        let entry = combo.entry(*i).or_insert(0);
        *entry = entry.checked_add(*m)?;
    }
    Some((coefs, bound.checked_add(b.1)?, combo))
}

/// Non-negative integer multipliers of the inequalities whose combination
/// reads `0 ≤ c` with a negative `c`, found by elimination without rounding.
fn farkas(rows: &[(BTreeMap<usize, i128>, i128)]) -> Option<Vec<(usize, i128)>> {
    let mut live: Vec<Combined> = rows.iter().enumerate().map(|(i, (coefs, bound))| (coefs.clone(), *bound, BTreeMap::from([(i, 1)]))).collect();
    let done = |row: &Combined| row.0.is_empty() && row.1 < 0;
    let answer = |row: &Combined| Some(row.2.iter().filter(|(_, m)| **m != 0).map(|(i, m)| (*i, *m)).collect());
    if let Some(row) = live.iter().find(|r| done(r)) {
        return answer(row);
    }
    let mut variables: Vec<usize> = live.iter().flat_map(|r| r.0.keys().copied()).collect();
    variables.sort_unstable();
    variables.dedup();
    for var in variables {
        let (with, mut rest): (Vec<Combined>, Vec<Combined>) = live.into_iter().partition(|r| r.0.contains_key(&var));
        for up in with.iter().filter(|r| r.0[&var] > 0) {
            for low in with.iter().filter(|r| r.0[&var] < 0) {
                let (a, c) = (up.0[&var], -low.0[&var]);
                let g = gcd(a, c);
                let row = add(scale(up, c / g)?, &scale(low, a / g)?)?;
                // A common factor of everything is dropped: the multipliers stay integers.
                let factor = row.0.values().chain(row.2.values()).fold(row.1.abs(), |g, x| gcd(g, *x));
                let row = if factor > 1 { (row.0.iter().map(|(v, c)| (*v, c / factor)).collect(), row.1 / factor, row.2.iter().map(|(i, m)| (*i, m / factor)).collect()) } else { row };
                if done(&row) {
                    return answer(&row);
                }
                if !row.0.is_empty() && !rest.iter().any(|r| r.0 == row.0 && r.1 <= row.1) {
                    rest.push(row);
                }
                if rest.len() > MAX_DERIVED {
                    return None;
                }
            }
        }
        live = rest;
    }
    None
}

fn derive(rows: &mut Vec<(BTreeMap<usize, i128>, i128)>, sources: &mut Vec<Source>, unequal: &[(BTreeMap<usize, i128>, i128)], split: &mut Vec<usize>, nodes: &mut usize) -> Option<Derivation> {
    *nodes += 1;
    if *nodes > MAX_NODES {
        return None;
    }
    if let Some(multipliers) = farkas(rows) {
        return Some(Derivation::Leaf { multipliers: multipliers.into_iter().map(|(i, m)| (sources[i], m)).collect() });
    }
    for (index, (sum, value)) in unequal.iter().enumerate() {
        if split.contains(&index) {
            continue;
        }
        let depth = split.len();
        split.push(index);
        let mut side = |rows: &mut Vec<(BTreeMap<usize, i128>, i128)>, sources: &mut Vec<Source>, split: &mut Vec<usize>, row: Option<(BTreeMap<usize, i128>, i128)>| {
            let row = row?;
            rows.push(row);
            sources.push(Source::Split(depth));
            let found = derive(rows, sources, unequal, split, nodes);
            rows.pop();
            sources.pop();
            found
        };
        let below = value.checked_sub(1).map(|bound| (sum.clone(), bound));
        let above = value.checked_add(1).and_then(|v| v.checked_neg()).map(|bound| (sum.iter().map(|(v, c)| (*v, -c)).collect(), bound));
        let found = side(rows, sources, split, below).and_then(|below| side(rows, sources, split, above).map(|above| Derivation::Split { unequal: index, below: Box::new(below), above: Box::new(above) }));
        split.pop();
        if found.is_some() {
            return found;
        }
    }
    None
}

/// Tells whether the derivation shows that no integers satisfy every
/// `at_most` and every `unequal`. It trusts nothing of the procedure that
/// produced the derivation.
fn check_derivation(at_most: &[AtMost], unequal: &[Unequal], derivation: &Derivation) -> bool {
    fn walk(at_most: &[AtMost], unequal: &[Unequal], added: &mut Vec<AtMost>, node: &Derivation) -> bool {
        match node {
            Derivation::Leaf { multipliers } => {
                let mut total: BTreeMap<usize, i128> = BTreeMap::new();
                let mut bound: i128 = 0;
                for (source, by) in multipliers {
                    let row = match source {
                        Source::Given(i) => at_most.get(*i),
                        Source::Split(i) => added.get(*i),
                    };
                    let Some(row) = row else { return false };
                    if *by < 0 {
                        return false;
                    }
                    for (var, coef) in &row.sum {
                        let Some(term) = coef.checked_mul(*by) else { return false };
                        let entry = total.entry(*var).or_insert(0);
                        let Some(next) = entry.checked_add(term) else { return false };
                        *entry = next;
                    }
                    let Some(next) = row.bound.checked_mul(*by).and_then(|x| bound.checked_add(x)) else { return false };
                    bound = next;
                }
                total.values().all(|c| *c == 0) && bound < 0
            }
            Derivation::Split { unequal: index, below, above } => {
                let Some(differs) = unequal.get(*index) else { return false };
                let (Some(low), Some(high)) = (differs.value.checked_sub(1), differs.value.checked_add(1)) else { return false };
                added.push(AtMost { sum: differs.sum.clone(), bound: low });
                let first = walk(at_most, unequal, added, below);
                added.pop();
                added.push(AtMost { sum: differs.sum.iter().map(|(v, c)| (*v, -c)).collect(), bound: -high });
                let second = walk(at_most, unequal, added, above);
                added.pop();
                first && second
            }
        }
    }
    walk(at_most, unequal, &mut Vec::new(), derivation)
}

/// Decides whether integers satisfy every `at_most` and every `unequal`, and
/// returns what shows the answer: a point, or a derivation that
/// [`check_derivation`] accepts. A refutation without a derivation is no
/// refutation: the answer is then `Undecided`.
pub(super) fn decide_certified(at_most: &[AtMost], unequal: &[Unequal]) -> Outcome {
    let (verdict, point) = search(at_most, unequal);
    if verdict == Verdict::Consistent {
        let value = |sum: &Sum| sum.iter().try_fold(0i128, |total, (var, coef)| total.checked_add(coef.checked_mul(point.get(var).copied().unwrap_or(0))?));
        let holds = at_most.iter().all(|c| value(&c.sum).is_some_and(|v| v <= c.bound)) && unequal.iter().all(|c| value(&c.sum).is_some_and(|v| v != c.value));
        return if holds { Outcome::Consistent(point) } else { Outcome::Undecided };
    }
    let rows: Option<Vec<(BTreeMap<usize, i128>, i128)>> = at_most.iter().map(|c| merged(&c.sum).map(|sum| (sum, c.bound))).collect();
    let differs: Option<Vec<(BTreeMap<usize, i128>, i128)>> = unequal.iter().map(|c| merged(&c.sum).map(|sum| (sum, c.value))).collect();
    let (Some(mut rows), Some(differs)) = (rows, differs) else { return Outcome::Undecided };
    let mut sources: Vec<Source> = (0..rows.len()).map(Source::Given).collect();
    match derive(&mut rows, &mut sources, &differs, &mut Vec::new(), &mut 0) {
        Some(derivation) if check_derivation(at_most, unequal, &derivation) => Outcome::Inconsistent(derivation),
        _ => Outcome::Undecided,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What the procedure establishes, without what shows it.
    fn decide(at_most: &[AtMost], unequal: &[Unequal]) -> Verdict {
        match decide_certified(at_most, unequal) {
            Outcome::Consistent(_) => Verdict::Consistent,
            Outcome::Inconsistent(_) => Verdict::Inconsistent,
            Outcome::Undecided => Verdict::Undecided,
        }
    }

    fn le(sum: &[(usize, i128)], bound: i128) -> AtMost {
        AtMost { sum: sum.to_vec(), bound }
    }

    #[test]
    fn a_chain_of_differences_is_decided() {
        // x − y ≤ −1, y ≤ 5, −x ≤ −10: x < y ≤ 5 and x ≥ 10.
        let system = [le(&[(0, 1), (1, -1)], -1), le(&[(1, 1)], 5), le(&[(0, -1)], -10)];
        assert_eq!(decide(&system, &[]), Verdict::Inconsistent);
        // With x ≥ 3 instead, x = 3 and y = 4 is a solution.
        let system = [le(&[(0, 1), (1, -1)], -1), le(&[(1, 1)], 5), le(&[(0, -1)], -3)];
        assert_eq!(decide(&system, &[]), Verdict::Consistent);
    }

    #[test]
    fn a_cycle_of_strict_differences_has_no_solution() {
        // x < y, y < z, z < x.
        let system = [le(&[(0, 1), (1, -1)], -1), le(&[(1, 1), (2, -1)], -1), le(&[(2, 1), (0, -1)], -1)];
        assert_eq!(decide(&system, &[]), Verdict::Inconsistent);
    }

    #[test]
    fn a_sum_of_two_quantities_is_bounded() {
        // x + y ≤ 30, x ≥ 20, y ≥ 15.
        let system = [le(&[(0, 1), (1, 1)], 30), le(&[(0, -1)], -20), le(&[(1, -1)], -15)];
        assert_eq!(decide(&system, &[]), Verdict::Inconsistent);
        let system = [le(&[(0, 1), (1, 1)], 30), le(&[(0, -1)], -20), le(&[(1, -1)], -10)];
        assert_eq!(decide(&system, &[]), Verdict::Consistent);
    }

    #[test]
    fn a_multiple_is_decided_when_a_point_is_found() {
        // x ≤ 2·y, y ≤ 5, x ≥ 11.
        let system = [le(&[(0, 1), (1, -2)], 0), le(&[(1, 1)], 5), le(&[(0, -1)], -11)];
        assert_eq!(decide(&system, &[]), Verdict::Inconsistent);
        let system = [le(&[(0, 1), (1, -2)], 0), le(&[(1, 1)], 5), le(&[(0, -1)], -10)];
        assert_eq!(decide(&system, &[]), Verdict::Consistent);
    }

    #[test]
    fn an_excluded_value_is_avoided_or_reported_open() {
        // 5 ≤ x ≤ 5 and x ≠ 5.
        let system = [le(&[(0, 1)], 5), le(&[(0, -1)], -5)];
        let verdict = decide(&system, &[Unequal { sum: vec![(0, 1)], value: 5 }]);
        assert_ne!(verdict, Verdict::Consistent);
        // 5 ≤ x ≤ 6 and x ≠ 5 leaves 6.
        let system = [le(&[(0, 1)], 6), le(&[(0, -1)], -5)];
        assert_eq!(decide(&system, &[Unequal { sum: vec![(0, 1)], value: 5 }]), Verdict::Consistent);
        // x − y ≠ 0 with x = y forced has no solution the search can find.
        let system = [le(&[(0, 1), (1, -1)], 0), le(&[(1, 1), (0, -1)], 0)];
        assert_ne!(decide(&system, &[Unequal { sum: vec![(0, 1), (1, -1)], value: 0 }]), Verdict::Consistent);
    }

    #[test]
    fn numbers_too_large_to_combine_leave_the_answer_open() {
        let huge = i128::MAX / 2;
        let system = [le(&[(0, huge), (1, huge - 1)], 1), le(&[(0, -(huge - 2)), (1, 5)], -1)];
        assert_eq!(decide(&system, &[]), Verdict::Undecided);
    }

    #[test]
    fn a_gap_between_integers_is_never_called_consistent() {
        // 2·x ≤ 3 and 2·x ≥ 3 has the rational solution 1.5 and no integer one.
        let system = [le(&[(0, 2)], 3), le(&[(0, -2)], -3)];
        assert_ne!(decide(&system, &[]), Verdict::Consistent);
    }
}
