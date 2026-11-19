//! Independent evaluator of original Core trees. This crate knows no backend types.

use trion_core::{Expr, Problem, Question};

pub const VERSION: &str = "propositional-evaluator/1";

#[derive(Debug, PartialEq, Eq)]
pub enum Scan {
    Incomplete,
    Complete {
        assignments: u64,
        has_model: bool,
        has_candidate: bool,
    },
}

fn eval(expr: &Expr, valuation: &[bool]) -> bool {
    match expr {
        Expr::True => true,
        Expr::False => false,
        Expr::Atom(i) => valuation[*i as usize],
        Expr::Not(child) => !eval(child, valuation),
        Expr::And(left, right) => eval(left, valuation) && eval(right, valuation),
        Expr::Or(left, right) => eval(left, valuation) || eval(right, valuation),
    }
}

fn premises_hold(problem: &Problem, valuation: &[bool]) -> bool {
    problem
        .document()
        .premises()
        .iter()
        .all(|expr| eval(expr, valuation))
}

fn target_holds(problem: &Problem, valuation: &[bool]) -> bool {
    match problem.query().question() {
        Question::Satisfiable => true,
        Question::Entails(goal) => !eval(goal, valuation),
    }
}

/// Check a prospective SAT witness against the original question.
pub fn check_witness(problem: &Problem, valuation: &[bool]) -> bool {
    valuation.len() == problem.document().declarations().len()
        && premises_hold(problem, valuation)
        && target_holds(problem, valuation)
}

/// Visit every completion of a prefix, first false, then true, at each slot.
fn visit(remaining: usize, prefix: &mut Vec<bool>, f: &mut impl FnMut(&[bool])) {
    if remaining == 0 {
        f(prefix);
        return;
    }
    prefix.push(false);
    visit(remaining - 1, prefix, f);
    *prefix.last_mut().expect("prefix is nonempty") = true;
    visit(remaining - 1, prefix, f);
    prefix.pop();
}

/// Assess the premises and candidate condition over all assignments within budget.
pub fn scan(problem: &Problem, budget: u64) -> Scan {
    let slots = problem.document().declarations().len();
    let Some(assignments) = u32::try_from(slots)
        .ok()
        .and_then(|count| 1_u64.checked_shl(count))
        .filter(|count| *count <= budget)
    else {
        return Scan::Incomplete;
    };
    let mut has_model = false;
    let mut has_candidate = false;
    visit(slots, &mut Vec::with_capacity(slots), &mut |valuation| {
        if premises_hold(problem, valuation) {
            has_model = true;
            has_candidate |= target_holds(problem, valuation);
        }
    });
    Scan::Complete {
        assignments,
        has_model,
        has_candidate,
    }
}
