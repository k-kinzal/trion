//! The situations of a specification, and whether each has a response.
//!
//! The statements without normative force say which situations can occur. A
//! specification is consistent only when, in each such situation, the
//! guarantees of the contracts whose assumptions hold can be kept together.
//! That a behaviour keeps every contract is less: a contract is kept
//! wherever its assumption does not hold.
//!
//! A situation is read at the level of the contracts: the assumption and
//! the guarantee of a statement, without the moments of a trace. Which
//! moment a response completes at, and what a deadline or an order adds,
//! belongs to one activation of a statement and is decided over the trace.
//!
//! A term is a *response term* when the guarantee of a statement with
//! normative force speaks about it: the action that the statement requires
//! or forbids, the attribute whose state it requires. Every other term is
//! named by a statement is *given*: a situation fixes it, and no response
//! changes it. Two kinds of terms go with the response by rule. The event
//! of an action is the occurrence of the action. A term that no statement
//! names is made by the reading (the time of a moment, the count of an
//! action, the time of a completion): a situation is told in the terms of
//! the statements, so it fixes none of them.
//!
//! The claim is one formula with a universal and an existential quantifier
//! ([`trion_solver::for_all_exists`]), and it is decided without listing
//! the situations: for every valuation of all terms that the descriptions
//! allow, read as what the conditions see, some valuation of the response
//! terms keeps the descriptions and the guarantee of each contract whose
//! condition holds in the first valuation. A condition can read a response
//! term, as `When the door is open` does where another statement requires
//! the door to become closed: the condition reads the term as the situation
//! shows it, and the guarantee speaks of the term as the response makes it.
//! So a response cannot escape a guarantee by making its condition false,
//! and a statement that changes what its condition reads contradicts nothing.
//!
//! A term that a declaration gives to the environment (`environment load`)
//! is given even where a guarantee speaks about it. A response may then
//! have to follow the situation: `the capacity shall be greater than the
//! load` has no constant response, and the response `capacity := load +
//! 0.001` answers every load ([`trion_solver::for_all_exists`]).

use crate::proof::Question;
use std::collections::{BTreeMap, BTreeSet};
use trion_language::reading::{ConstraintKind, Model};
use trion_solver::{for_all_exists, Atom, ForAll, Formula, Instance, Status};

/// A situation in which statements cannot all be kept.
pub(super) struct Conflict {
    /// The statements with a condition among them.
    pub(super) conditions: Vec<usize>,
    /// The contracts that cannot all be kept in the situation.
    pub(super) statements: Vec<usize>,
    /// What the situation fixes, as far as the conflict needs it.
    pub(super) facts: Vec<String>,
    /// The situation can occur: the descriptions with what it fixes.
    occurs: Vec<usize>,
    /// The statements with what it fixes.
    refuted: Vec<usize>,
}

/// What the examination of the situations found.
pub(super) struct Situations {
    pub(super) conflicts: Vec<Conflict>,
    /// `true` when each claim was decided.
    pub(super) decided: bool,
    /// How the situations were examined, for a report.
    pub(super) examined: String,
    /// The queries whose refutation shows that every situation has a response.
    answered: Vec<Vec<usize>>,
    /// The responses that are terms over what a situation fixes: `capacity := load + 0.001`.
    pub(super) symbolic: Vec<String>,
}

impl Situations {
    /// The questions that the answer rests on, each with its name. For a
    /// conflict: its situation can occur, and the statements cannot all be
    /// kept in it. Without a conflict: no situation is left that the
    /// responses found do not answer. `None` when the solver does not give
    /// each answer that the claim needs.
    pub(super) fn questions(&self, inst: &Instance) -> Option<Vec<(String, Question)>> {
        let mut out = Vec::new();
        let mut ask = |name: String, query: &[usize], expected: Status| {
            let question = Question::ask(inst, query.to_vec());
            let given = question.status() == expected;
            out.push((name, question));
            given
        };
        for (number, conflict) in self.conflicts.iter().enumerate() {
            let number = number + 1;
            if !(ask(format!("situation {number}: the situation can occur"), &conflict.occurs, Status::Satisfiable) && ask(format!("situation {number}: the statements cannot all be kept"), &conflict.refuted, Status::Unsatisfiable)) {
                return None;
            }
        }
        if self.conflicts.is_empty() {
            if !self.decided {
                return None;
            }
            for (number, query) in self.answered.iter().enumerate() {
                if !ask(format!("situations: no situation is left without a response ({})", number + 1), query, Status::Unsatisfiable) {
                    return None;
                }
            }
        }
        Some(out)
    }
}

/// The mark of a term as a condition sees it, apart from what a response makes of it.
const SEEN: char = '?';

/// A formula with each response term replaced by the term as a condition sees it.
fn seen(formula: &Formula, response: &dyn Fn(&str) -> bool) -> Formula {
    let mark = |name: String| if response(&name) { format!("{SEEN}{name}") } else { name };
    formula.clone().map_atoms(&|atom| match atom {
        Atom::Dom { attr, value } => Atom::Dom { attr: mark(attr), value },
        Atom::Val { attr, value } => Atom::Val { attr: mark(attr), value },
        Atom::Act { key } => Atom::Act { key: mark(key) },
        Atom::Forbid { key } => Atom::Forbid { key: mark(key) },
        Atom::Discouraged { key } => Atom::Discouraged { key: mark(key) },
        Atom::Event { key } => Atom::Event { key: mark(key) },
        Atom::Config { key } => Atom::Config { key: mark(key) },
        Atom::Role { subject, role } => Atom::Role { subject: mark(subject), role },
        Atom::Num { attr, unit, cmp, n } => Atom::Num { attr: mark(attr), unit, cmp, n },
        Atom::Lin { terms, unit, cmp, n } => Atom::Lin { terms: terms.into_iter().map(|(attr, coefficient)| (mark(attr), coefficient)).collect(), unit, cmp, n },
        Atom::Before { first, second } => Atom::Before { first: mark(first), second: mark(second) },
        Atom::Rel { name, args } => Atom::Rel { name: mark(name), args },
    })
}

/// Examines the situations of a model. `environment` holds what is known
/// of the events of the environment beyond the background of the model, and
/// `events` names the action behind each event. `soft` tells whether a
/// contract is only advice, and `described` whether its statement has no
/// normative force. The formulas of the contracts are added to the instance.
pub(super) fn search(model: &Model, inst: &Instance, environment: &[Formula], events: &BTreeMap<String, String>, given: &BTreeSet<String>, soft: &dyn Fn(usize) -> bool, described: &dyn Fn(usize) -> bool) -> Situations {
    let count = model.constraints.len();
    let normative = |i: usize| matches!(model.constraints[i].kind, ConstraintKind::Spec | ConstraintKind::Permission) && !soft(i) && !described(i);
    // The response terms: what a guarantee with normative force speaks
    // about, with what the reading makes of that guarantee. `The room shall
    // be archived` requires an action, and its meaning says that the room
    // is archived then: the state of the room is part of the response.
    let stated: BTreeSet<&str> = (0..count).filter(|&i| normative(i)).filter_map(|i| model.constraints[i].refs.first()).map(|r| r.id.as_str()).collect();
    let mut terms: BTreeSet<String> = BTreeSet::new();
    for (i, c) in model.constraints.iter().enumerate() {
        if normative(i) || (c.kind.is_vocabulary() && c.refs.first().is_some_and(|r| stated.contains(r.id.as_str()))) {
            c.guarantee.atoms(true, &mut |atom, _| terms.extend(atom.symbols().into_iter().map(str::to_string)));
        }
    }
    // An event is the occurrence of its action: it is a response where the action is one.
    terms.extend(events.iter().filter(|(_, action)| terms.contains(action.as_str())).map(|(event, _)| event.clone()).collect::<Vec<_>>());
    // A situation is told in the terms of the statements. A term that no
    // statement names is made by the reading, as the count of an action is:
    // it comes with the behaviour, and no situation fixes it.
    let mut named: BTreeSet<String> = BTreeSet::new();
    for c in model.constraints.iter().filter(|c| !c.kind.is_axiom()) {
        for formula in [&c.assume, &c.guarantee] {
            formula.atoms(true, &mut |atom, _| named.extend(atom.symbols().into_iter().map(str::to_string)));
        }
    }
    // A term that the environment controls is given, whatever speaks about
    // it: `The capacity shall be greater than the load.` requires a capacity
    // for each load, and no response chooses the load.
    let response = |symbol: &str| !symbol.starts_with(SEEN) && !given.contains(symbol) && (terms.contains(symbol) || !named.contains(symbol));
    // What says which situations can occur, and what a behaviour must keep besides.
    let mut contract_of: BTreeMap<usize, usize> = BTreeMap::new();
    let mut descriptions: Vec<usize> = model.background.iter().chain(environment).map(|axiom| inst.add(axiom)).collect();
    for i in (0..count).filter(|&i| !normative(i) && !soft(i) && model.constraints[i].kind != ConstraintKind::Refinement) {
        let id = inst.add(&model.constraints[i].formula());
        contract_of.insert(id, i);
        descriptions.push(id);
    }
    let premises: Vec<usize> = descriptions
        .iter()
        .map(|&id| {
            let formula = inst.formulas()[id].clone();
            let as_seen = seen(&formula, &response);
            if as_seen == formula {
                id
            } else {
                inst.add(&as_seen)
            }
        })
        .collect();
    // Each contract with its condition read apart from the response: the
    // condition is what the situation shows, and the guarantee is what the
    // response makes. `When the door is open, the door shall become closed`
    // reads an open door and requires a closed one.
    let mut applied: Vec<usize> = Vec::new();
    for i in (0..count).filter(|&i| normative(i)) {
        let c = &model.constraints[i];
        let guarantee = trion_language::reading::situation_guarantee(model, c);
        let id = inst.add(&match &c.assume {
            Formula::True => guarantee,
            condition => Formula::implies(seen(condition, &response), guarantee),
        });
        contract_of.insert(id, i);
        applied.push(id);
    }
    let mut found = Situations { conflicts: Vec::new(), decided: true, examined: String::new(), answered: Vec::new(), symbolic: Vec::new() };
    let mut open: Option<String> = None;
    {
        match for_all_exists(inst, &premises, &descriptions, &applied, &response) {
            ForAll::Holds { refuted, symbolic } => {
                found.answered.extend(refuted);
                found.symbolic = symbolic;
            }
            ForAll::Open { reason } => open = Some(reason),
            ForAll::Fails { situations } => {
                for unanswered in situations {
                    let mut statements: Vec<usize> = unanswered.conclusions.iter().filter_map(|id| contract_of.get(id).copied()).collect();
                    statements.sort_unstable();
                    statements.dedup();
                    if found.conflicts.iter().any(|c| c.statements == statements) {
                        continue;
                    }
                    let current = inst.formulas();
                    found.conflicts.push(Conflict {
                        conditions: statements.iter().copied().filter(|&i| normative(i) && model.constraints[i].has_guard()).collect(),
                        statements,
                        facts: unanswered.given.iter().map(|&id| current[id].to_string().replace(SEEN, "")).collect(),
                        occurs: premises.iter().chain(&unanswered.given).copied().collect(),
                        refuted: unanswered.conclusions.iter().chain(&unanswered.given).copied().collect(),
                    });
                }
            }
        }
    }
    found.decided = open.is_none();
    found.examined = match (&open, found.conflicts.len()) {
        (_, conflicts) if conflicts > 0 => format!("the statements cannot all be kept in {conflicts} situation(s)"),
        (Some(reason), _) => format!("not every situation was examined: {reason}"),
        (None, _) if !found.symbolic.is_empty() => format!("every situation was examined through {} questions, without listing the situations; the statements can all be kept in each situation, with a response that follows the situation: {}", found.answered.len(), found.symbolic.join("; ")),
        (None, _) => format!("every situation was examined through {} questions, without listing the situations; the statements can all be kept in each situation", found.answered.len()),
    };
    found
}
