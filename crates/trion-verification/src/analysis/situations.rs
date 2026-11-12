//! The situations of a specification: which conditions of its statements
//! can hold together, and whether the statements can all be kept in each.
//!
//! The statements without normative force say which situations can occur. A
//! specification is consistent only when, in each such situation, the
//! guarantees of the contracts whose assumptions hold can be kept together.
//! That a behaviour keeps every contract is less: a contract is kept
//! wherever its assumption does not hold.
//!
//! A statement with normative force can end a situation or forbid it: `When
//! the door is open, the door shall become closed` cannot be kept where the
//! door stays open. Such a statement excludes the situation alone, and it
//! is in conflict with no other statement there. A conflict is a set of
//! statements each of which can be kept in the situation alone, and which
//! cannot all be kept in it.

use crate::proof::Question;
use std::collections::{BTreeMap, BTreeSet};
use trion_language::reading::Model;
use trion_solver::{Atom, Formula, Instance, Status};

/// The truth value of a formula in a situation that a witness gives, or
/// `None` where the witness does not tell it.
fn holds(formula: &Formula, atoms: &BTreeMap<Atom, bool>, quantities: &BTreeMap<(String, String), i64>) -> Option<bool> {
    use trion_solver::Cmp;
    let compare = |value: i64, cmp: Cmp, n: i64| match cmp {
        Cmp::Eq => value == n,
        Cmp::Ge => value >= n,
        Cmp::Le => value <= n,
        Cmp::Gt => value > n,
        Cmp::Lt => value < n,
    };
    match formula {
        Formula::True => Some(true),
        Formula::Atom(atom) => atoms.get(atom).copied().or_else(|| match atom {
            Atom::Num { attr, unit, cmp, n } => quantities.get(&(attr.clone(), unit.clone())).map(|value| compare(*value, *cmp, *n)),
            Atom::Lin { terms, unit, cmp, n } => {
                let mut sum = 0i64;
                for (attr, coefficient) in terms {
                    sum = sum.checked_add(quantities.get(&(attr.clone(), unit.clone()))?.checked_mul(*coefficient)?)?;
                }
                Some(compare(sum, *cmp, *n))
            }
            _ => None,
        }),
        Formula::Not(inner) => holds(inner, atoms, quantities).map(|value| !value),
        Formula::And(items) => {
            let values: Vec<Option<bool>> = items.iter().map(|item| holds(item, atoms, quantities)).collect();
            if values.contains(&Some(false)) {
                Some(false)
            } else if values.contains(&None) {
                None
            } else {
                Some(true)
            }
        }
        Formula::Or(items) => {
            let values: Vec<Option<bool>> = items.iter().map(|item| holds(item, atoms, quantities)).collect();
            if values.contains(&Some(true)) {
                Some(true)
            } else if values.contains(&None) {
                None
            } else {
                Some(false)
            }
        }
        Formula::Implies(a, b) => match (holds(a, atoms, quantities), holds(b, atoms, quantities)) {
            (Some(false), _) | (_, Some(true)) => Some(true),
            (Some(true), Some(false)) => Some(false),
            _ => None,
        },
    }
}


/// The most largest situations that are examined.
const ROUNDS: usize = 256;
/// The most steps of the search within the largest situations.
const STEPS: usize = 4096;

/// A situation in which statements cannot all be kept.
pub(super) struct Conflict {
    /// The contracts whose conditions hold in the situation. No condition
    /// can be left out.
    pub(super) conditions: Vec<usize>,
    /// The contracts that cannot all be kept there.
    pub(super) statements: Vec<usize>,
    /// The groups of the conditions.
    forced: Vec<usize>,
}

/// What the search of the situations found.
pub(super) struct Situations {
    pub(super) conflicts: Vec<Conflict>,
    /// `true` when every situation was examined.
    pub(super) decided: bool,
    /// How far the situations were examined, for a report.
    pub(super) examined: String,
    /// The groups that say which situations can occur.
    possible: Vec<usize>,
    /// Each situation in which the statements are kept: the groups of its
    /// conditions and of the statements.
    kept: Vec<Vec<usize>>,
    /// Each statement that excludes a situation alone: the groups of the
    /// conditions, and the statement.
    excluded: Vec<(Vec<usize>, usize)>,
    /// For each largest situation: a condition outside it holds, as a formula.
    outside: Vec<usize>,
}

impl Situations {
    /// The questions that the answer rests on, each with its name. For a
    /// conflict: its conditions hold together, each of its statements can
    /// be kept under them alone, and the statements cannot all be kept
    /// under them. Without a conflict: the statements are kept in each
    /// situation that the search ended at, each statement that was left
    /// out of one excludes it alone, and every situation lies within a
    /// largest one. `None` when the solver does not give each answer that
    /// the claim needs.
    pub(super) fn questions(&self, inst: &Instance) -> Option<Vec<(String, Question)>> {
        let with = |groups: &[usize], more: &[usize]| inst.query(&groups.iter().chain(more).copied().collect::<Vec<_>>(), &[]);
        let mut out = Vec::new();
        let mut ask = |name: String, query: Vec<usize>, expected: Status| {
            let question = Question::ask(inst, query);
            let given = question.status() == expected;
            out.push((name, question));
            given
        };
        for (number, conflict) in self.conflicts.iter().enumerate() {
            let number = number + 1;
            if !ask(format!("situation {number}: the conditions hold together"), with(&self.possible, &conflict.forced), Status::Satisfiable) {
                return None;
            }
            for (member, &statement) in conflict.statements.iter().enumerate() {
                if !ask(format!("situation {number}: statement {} can be kept alone", member + 1), with(&self.possible, &[conflict.forced.as_slice(), &[statement]].concat()), Status::Satisfiable) {
                    return None;
                }
            }
            if !ask(format!("situation {number}: the statements cannot all be kept"), with(&self.possible, &[conflict.forced.as_slice(), conflict.statements.as_slice()].concat()), Status::Unsatisfiable) {
                return None;
            }
        }
        if self.conflicts.is_empty() {
            if !self.decided {
                return None;
            }
            for (number, groups) in self.kept.iter().enumerate() {
                if !ask(format!("situations: the statements are kept in the situation {}", number + 1), with(groups, &[]), Status::Satisfiable) {
                    return None;
                }
            }
            for (number, (forced, statement)) in self.excluded.iter().enumerate() {
                if !ask(format!("situations: the statement {} excludes its situation alone", number + 1), with(&self.possible, &[forced.as_slice(), &[*statement]].concat()), Status::Unsatisfiable) {
                    return None;
                }
            }
            if !self.outside.is_empty() && !ask("situations: every situation lies within a largest one".to_string(), with(&self.possible, &[]).into_iter().chain(self.outside.iter().copied()).collect(), Status::Unsatisfiable) {
                return None;
            }
        }
        Some(out)
    }
}

/// Examines the situations of a model. `standing` gives, for a contract with
/// a condition, the group that makes the condition hold while the response
/// is due. `soft` tells whether a contract is only advice, and `described`
/// whether its statement has no normative force.
///
/// A situation is a set of conditions that hold together. It can occur when
/// the statements without normative force allow it. The largest situations
/// are sought one after another: after each one the solver is asked for a
/// situation that holds a condition outside every one found so far, until
/// there is none. Only `ROUNDS` largest situations are sought.
///
/// Within a largest situation the statements are kept, or a least set of
/// its conditions is found under which they are not. When a statement
/// excludes that least situation alone, the statement is left out wherever
/// those conditions hold together; otherwise the least situation is a
/// conflict. Either way the search goes on in the situations that lack one
/// of those conditions. Only `STEPS` steps are made.
pub(super) fn search(model: &Model, inst: &Instance, standing: &BTreeMap<usize, usize>, soft: &dyn Fn(usize) -> bool, described: &dyn Fn(usize) -> bool) -> Situations {
    let count = model.constraints.len();
    let hard = |i: usize| !model.constraints[i].kind.is_axiom() && !soft(i);
    let all: Vec<usize> = (0..count).filter(|&i| model.constraints[i].kind.is_axiom() || hard(i)).collect();
    let possible: Vec<usize> = all.iter().copied().filter(|&i| model.constraints[i].kind.is_axiom() || described(i)).collect();
    // One condition for each distinct condition of a statement with normative force.
    let mut conditions: Vec<(usize, usize)> = Vec::new();
    let mut seen = BTreeSet::new();
    for (&contract, &group) in standing {
        if hard(contract) && !described(contract) && seen.insert(model.constraints[contract].assume.to_string()) {
            conditions.push((group, contract));
        }
    }
    let k = conditions.len();
    let mut found = Situations { conflicts: Vec::new(), decided: true, examined: "no statement with normative force has a condition, so one situation was examined".to_string(), possible: possible.clone(), kept: Vec::new(), excluded: Vec::new(), outside: Vec::new() };
    if k == 0 {
        return found;
    }
    let groups = |members: &[usize]| members.iter().map(|&m| conditions[m].0).collect::<Vec<_>>();
    let mut open = false;
    let formulas = inst.formulas();
    let condition = |member: usize| formulas[inst.group(conditions[member].0)].clone();
    // A situation that can occur and that holds a condition outside each
    // largest situation found so far, with the conditions that hold in the
    // witness that was found.
    let allowed = |members: &[usize], outside: &[usize], open: &mut bool| -> Option<Vec<usize>> {
        let mut active = possible.clone();
        active.extend(groups(members));
        let mut query = inst.query(&active, &[]);
        query.extend_from_slice(outside);
        let answer = inst.decide(&query);
        match answer.status {
            Status::Satisfiable => {
                let (atoms, quantities) = answer.witness().map(|w| (w.atoms(), w.quantities())).unwrap_or_default();
                Some((0..k).filter(|&member| holds(&condition(member), &atoms, &quantities) == Some(true)).collect())
            }
            Status::Unknown => {
                *open = true;
                None
            }
            Status::Unsatisfiable => None,
        }
    };
    let mut largest: Vec<Vec<usize>> = Vec::new();
    let mut outside: Vec<usize> = Vec::new();
    let mut left = false;
    loop {
        let Some(mut members) = allowed(&[], &outside, &mut open) else { break };
        if largest.len() == ROUNDS {
            left = true;
            break;
        }
        // The situation grows while one more condition can hold with it:
        // then it is a largest one.
        loop {
            let rest: Vec<usize> = (0..k).filter(|other| !members.contains(other)).collect();
            if rest.is_empty() {
                break;
            }
            let more = inst.add(&Formula::Or(rest.iter().map(|&other| condition(other)).collect()));
            let mut wanted = outside.clone();
            wanted.push(more);
            let Some(next) = allowed(&members, &wanted, &mut open) else { break };
            let size = members.len();
            members.extend(next.into_iter().filter(|member| rest.contains(member)));
            if members.len() == size {
                // The witness tells no further condition: each is asked for.
                for other in rest {
                    members.push(other);
                    if allowed(&members, &outside, &mut open).is_none() {
                        members.pop();
                    }
                }
                break;
            }
        }
        members.sort_unstable();
        let rest: Vec<Formula> = (0..k).filter(|other| !members.contains(other)).map(condition).collect();
        // A condition outside this situation holds; none is left when every condition is in it.
        outside.push(inst.add(&Formula::Or(rest.clone())));
        largest.push(members);
        // Every condition holds together: no other situation is left.
        if rest.is_empty() {
            break;
        }
    }
    found.outside = outside;
    // Within each largest situation: the statements are kept, or a least
    // set of conditions under which they are not is examined.
    let refuted = |active: &[usize], open: &mut bool| match inst.status(active, &[]) {
        Status::Unsatisfiable => true,
        Status::Unknown => {
            *open = true;
            false
        }
        Status::Satisfiable => false,
    };
    let mut steps = 0usize;
    let mut limited = false;
    let mut visited: BTreeSet<(Vec<usize>, Vec<usize>)> = BTreeSet::new();
    let mut stack: Vec<(Vec<usize>, Vec<usize>)> = largest.iter().rev().map(|members| (members.clone(), Vec::new())).collect();
    while let Some((members, removed)) = stack.pop() {
        if !visited.insert((members.clone(), removed.clone())) {
            continue;
        }
        if steps == STEPS {
            limited = true;
            break;
        }
        steps += 1;
        let statements: Vec<usize> = all.iter().copied().filter(|g| !removed.contains(g)).collect();
        let under = |members: &[usize]| [statements.as_slice(), groups(members).as_slice()].concat();
        if !refuted(&under(&members), &mut open) {
            if !open {
                found.kept.push(under(&members));
            }
            continue;
        }
        // The fewest of the conditions under which the statements are not kept.
        let mut least = members.clone();
        let mut at = 0;
        while at < least.len() {
            let mut fewer = least.clone();
            fewer.remove(at);
            if refuted(&under(&fewer), &mut open) {
                least = fewer;
            } else {
                at += 1;
            }
        }
        let forced = groups(&least);
        let (core, _) = inst.unsat_subset(&under(&least), &[]);
        let named: Vec<usize> = core.into_iter().filter(|&g| g < count && !possible.contains(&g)).collect();
        // A statement that cannot be kept under the conditions alone ends
        // the situation or forbids it: it is in conflict with nothing there.
        let alone: Vec<usize> = named.iter().copied().filter(|&statement| refuted(&[possible.as_slice(), forced.as_slice(), &[statement]].concat(), &mut open)).collect();
        if alone.is_empty() {
            if !open && !found.conflicts.iter().any(|c| c.forced == forced) {
                found.conflicts.push(Conflict { conditions: least.iter().map(|&m| conditions[m].1).collect(), statements: named, forced });
            }
        } else {
            found.excluded.extend(alone.iter().map(|&statement| (forced.clone(), statement)));
            let mut without = removed.clone();
            without.extend(alone);
            without.sort_unstable();
            without.dedup();
            stack.push((members.clone(), without));
        }
        // What lacks one of those conditions is another situation.
        for skip in 0..least.len() {
            let fewer: Vec<usize> = members.iter().copied().filter(|m| *m != least[skip]).collect();
            if !fewer.is_empty() {
                stack.push((fewer, removed.clone()));
            }
        }
    }
    found.decided = !(open || limited || left);
    let scope = if left { format!("{} largest situations of the {k} conditions were examined, which is the limit, and further ones were left", largest.len()) } else { format!("each of the {} largest situations of the {k} conditions was examined, and every situation lies within one of them", largest.len()) };
    let answer = match (found.conflicts.is_empty(), found.decided) {
        (false, _) => format!("the statements cannot all be kept in {} situation(s)", found.conflicts.len()),
        (true, true) => "the statements can all be kept in each situation".to_string(),
        (true, false) => "no conflict was found, which decides nothing about the situations that were left".to_string(),
    };
    found.examined = format!("{scope}; {answer}");
    found
}
