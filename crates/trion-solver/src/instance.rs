//! An encoded set of formulas whose queries switch groups on and off.
//!
//! An instance holds a background that every query includes, groups that a
//! query names, and conditions that a query may force. Every formula has a
//! number, and a query is a list of numbers, so that a question can be kept
//! with its answer.

use super::certificate::{Answer, Prover, Status};
use crate::formula::Formula;
use std::cell::RefCell;
use std::collections::BTreeSet;

/// A condition that a query may force, as [`Instance::guard`] names it.
pub type Lit = i32;

/// An encoded model: a background, groups that a query switches on, and the
/// conditions that a query may force. Every formula has a number, and a
/// query is a list of numbers, so a question can be kept with its answer.
pub struct Instance {
    prover: RefCell<Prover>,
    /// Every formula of the instance, by its number.
    formulas: RefCell<Vec<Formula>>,
    background: Vec<usize>,
    groups: Vec<usize>,
    /// The formula of each group's condition.
    guards: Vec<Option<usize>>,
}

impl Instance {
    /// Encodes a background and groups. The formula of a group and its guard
    /// are given apart: the formula holds whatever the guard is, and the
    /// guard is what a query may force. The search for one part of a query
    /// ends after `decisions` decisions, when a limit is given.
    pub fn new(background: &[Formula], groups: &[(Formula, Option<Formula>)], decisions: Option<u64>) -> Instance {
        let mut instance = Instance { prover: RefCell::new(Prover::new(decisions)), formulas: RefCell::new(Vec::new()), background: Vec::new(), groups: Vec::new(), guards: Vec::new() };
        instance.background = background.iter().map(|f| instance.add(f)).collect();
        instance.groups = groups.iter().map(|(formula, _)| instance.add(formula)).collect();
        instance.guards = groups.iter().map(|(_, guard)| guard.as_ref().map(|g| instance.add(g))).collect();
        instance
    }

    /// Adds a formula and returns its number.
    pub fn add(&self, formula: &Formula) -> usize {
        self.formulas.borrow_mut().push(formula.clone());
        self.prover.borrow_mut().add(formula)
    }

    /// Every formula of the instance, by its number.
    pub fn formulas(&self) -> Vec<Formula> {
        self.formulas.borrow().clone()
    }

    /// The numbers of the background formulas.
    pub fn background(&self) -> &[usize] {
        &self.background
    }

    /// The number of the formula of a group.
    pub fn group(&self, group: usize) -> usize {
        self.groups[group]
    }

    /// The condition of a group, as a query may force it.
    pub fn guard(&self, group: usize) -> Option<Lit> {
        self.guards.get(group).copied().flatten().map(|id| id as Lit)
    }

    /// `true` when a query was refused because the work limit was reached.
    #[cfg(test)]
    pub(crate) fn exhausted(&self) -> bool {
        self.prover.borrow().exhausted()
    }

    /// The most decisions that one query of this instance has needed.
    pub fn peak_decisions(&self) -> u64 {
        self.prover.borrow().peak_decisions()
    }

    /// The numbers of the formulas of a query: the background, the active
    /// groups and the assumptions.
    pub fn query(&self, active: &[usize], assumptions: &[Lit]) -> Vec<usize> {
        self.background.iter().copied().chain(active.iter().map(|&g| self.groups[g])).chain(assumptions.iter().map(|&a| a as usize)).collect()
    }

    /// What the search establishes for the formulas with these numbers,
    /// with its certificate.
    pub fn decide(&self, query: &[usize]) -> Answer {
        self.prover.borrow().decide(query)
    }

    /// What the search establishes for the active groups and the
    /// assumptions within the bounds of this instance, with its certificate.
    fn answer(&self, active: &[usize], assumptions: &[Lit]) -> Answer {
        self.decide(&self.query(active, assumptions))
    }

    /// What the search establishes for the active groups and the assumptions
    /// within the bounds of this instance.
    pub fn status(&self, active: &[usize], assumptions: &[Lit]) -> Status {
        self.answer(active, assumptions).status
    }

    /// Finds an unsatisfiable subset by deletion. `active` must be
    /// unsatisfiable. The subset is always sufficient; it is minimal only when
    /// the second value is `true`, that is, when no deletion test ended at
    /// the bounds.
    pub fn unsat_subset(&self, active: &[usize], assumptions: &[Lit]) -> (Vec<usize>, bool) {
        // The refutation rests on one part of the query: the groups of the
        // other parts cannot belong to the subset.
        let (answer, part) = self.prover.borrow().decide_with_part(&self.query(active, assumptions));
        let mut core: Vec<usize> = match (answer.status, part) {
            (Status::Unsatisfiable, Some(part)) => {
                let part: BTreeSet<usize> = part.into_iter().collect();
                active.iter().copied().filter(|&g| part.contains(&self.groups[g])).collect()
            }
            _ => active.to_vec(),
        };
        let mut minimal = true;
        let mut i = 0;
        while i < core.len() {
            let removed = core.remove(i);
            match self.status(&core, assumptions) {
                Status::Unsatisfiable => {}
                status => {
                    minimal &= status == Status::Satisfiable;
                    core.insert(i, removed);
                    i += 1;
                }
            }
        }
        (core, minimal)
    }

}

#[cfg(test)]
mod work_limit {
    use crate::certificate::WORK_LIMIT;
    use super::*;

    #[test]
    fn an_instance_without_work_left_answers_unknown() {
        let instance = Instance::new(&[], &[], None);
        assert_eq!(instance.status(&[], &[]), Status::Satisfiable);
        assert!(!instance.exhausted());
        // The queries so far have used the whole limit.
        instance.prover.borrow().work.set(WORK_LIMIT + 1);
        let fresh = Instance::new(&[], &[(Formula::True, None)], None);
        fresh.prover.borrow().work.set(WORK_LIMIT + 1);
        assert_eq!(fresh.status(&[0], &[]), Status::Unknown);
        assert!(fresh.exhausted());
        assert!(instance.exhausted());
    }
}
