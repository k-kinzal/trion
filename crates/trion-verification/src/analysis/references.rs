//! The proof obligations of a package: what a correct specification owes,
//! as questions over formulas that another program can decide again.
//!
//! - Consistency: each situation that the environment can bring about has a
//!   response that keeps every statement that applies in it
//!   (`formal/Trion/Document.lean`, `consistent`). It is stated as one
//!   question with a quantifier alternation, together with the questions
//!   that the statements can all be kept over the trace and that each
//!   condition that the system does not control can be met while they are.
//! - Compatibility: an environment that the statements without normative
//!   force allow meets an assumption of a statement.
//! - Correctness against a reference: for each statement that other
//!   statements detail, the details accept each environment of the
//!   statement and each behaviour that keeps the details keeps the
//!   statement (`refines`). Their equivalence is not assumed.
//!
//! Building the obligations decides nothing: the formulas are written
//! down, and [`ProofObligations::decide`] decides one of them.

use super::responsibility::{Authored, Situated};
use super::situations;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use trion_core::{Expr, Problem, Question};
use trion_language::document::PropositionalCheck;
use trion_language::reading::{ConstraintKind, Model};
use trion_language::{Diagnostic, SpecRef, SpecSet};
use trion_solver::{for_all_exists, Answer, Atom, ForAll, Formula, Instance, Status};

/// The proof obligations of a package within its bounds, over one pool of
/// formulas.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofObligations {
    /// The moments of each trace that the formulas are unrolled over.
    pub moments: usize,
    /// The individuals of each type, when a statement is read over individuals.
    pub individuals: Option<usize>,
    /// Every formula that an obligation names, by its number.
    pub pool: Vec<Formula>,
    /// The statement that each formula of a guarantee belongs to, so that a
    /// refutation names the statements that cannot all be kept.
    #[serde(default)]
    pub owners: BTreeMap<usize, String>,
    pub obligations: Vec<ProofObligation>,
    /// Checked source of each propositional obligation, by its position.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub propositional: BTreeMap<usize, PropositionalCheck>,
    /// What building the obligations found: a block that names what is not
    /// there, or a question that cannot be stated. These are findings of the
    /// conversion and no part of the form.
    #[serde(skip)]
    pub findings: Vec<Diagnostic>,
}

/// One proof obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofObligation {
    /// `consistency`, `compatibility` or `refinement/ID`.
    pub name: String,
    /// The property of a correct specification that the obligation states:
    /// `consistency`, `compatibility` or `correctness`.
    pub property: String,
    /// The proposition in words, with the bound that it is about.
    pub proposition: String,
    /// The statements that the obligation is about.
    pub statements: Vec<String>,
    pub question: ObligationQuestion,
}

/// What proves an obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum ObligationQuestion {
    /// For every valuation of the symbols that are not chosen that
    /// satisfies the premises, some valuation of the chosen symbols
    /// satisfies the standing formulas and the conclusions.
    ForAllExists { premises: Vec<usize>, standing: Vec<usize>, conclusions: Vec<usize>, chosen: Vec<String> },
    /// The formulas hold together in some valuation.
    Satisfiable { query: Vec<usize> },
    /// The formulas of the query hold together in no valuation.
    Unsatisfiable { query: Vec<usize> },
    /// Each part holds.
    All { parts: Vec<ObligationQuestion> },
    /// Some part holds.
    Any { parts: Vec<ObligationQuestion> },
    /// The part is refuted.
    Not { part: Box<ObligationQuestion> },
}

/// Lower a checked propositional problem into the questions of the MMT
/// form. These formulas have their own premises and do not use the
/// background or the contract groups of the surrounding document.
fn propositional_question(problem: &Problem, mut add: impl FnMut(&Formula) -> usize) -> (ObligationQuestion, String) {
    fn formula(expr: &Expr, names: &[String]) -> Formula {
        match expr {
            Expr::True => Formula::True,
            Expr::False => Formula::not(Formula::True),
            Expr::Atom(slot) => Formula::atom(Atom::Rel { name: names[*slot as usize].clone(), args: vec![] }),
            Expr::Not(inner) => Formula::not(formula(inner, names)),
            Expr::And(left, right) => Formula::And(vec![formula(left, names), formula(right, names)]),
            Expr::Or(left, right) => Formula::Or(vec![formula(left, names), formula(right, names)]),
        }
    }

    let document = problem.document();
    let names = document.declarations();
    let premises: Vec<Formula> = document.premises().iter().map(|expr| formula(expr, names)).collect();
    let query: Vec<usize> = premises.iter().map(&mut add).collect();
    let satisfiable = ObligationQuestion::Satisfiable { query: query.clone() };
    let (question, claim) = match problem.query().question() {
        Question::Satisfiable => (satisfiable, "the premises are satisfiable".to_string()),
        Question::Entails(target) => {
            let target = formula(target, names);
            let mut query = query;
            query.push(add(&Formula::not(target.clone())));
            let no_counterexample = ObligationQuestion::Unsatisfiable { query };
            let claim = format!("the premises are satisfiable and entail {target}");
            (ObligationQuestion::All { parts: vec![satisfiable, no_counterexample] }, claim)
        }
    };
    let premises = premises.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ");
    let proposition = format!("over the Boolean valuations of [{}] ({}), with premises [{premises}]: {claim}", names.join(", "), trion_core::SEMANTICS);
    (question, proposition)
}

pub const PROPOSITIONAL_CHECK: &str = "propositional_check";

/// The questions of this fragment, with the formula references resolved.
fn propositional_formulas(question: &ObligationQuestion, pool: &[Formula]) -> Option<Vec<Vec<Formula>>> {
    let formulas = |query: &[usize]| query.iter().map(|&id| pool.get(id).cloned()).collect::<Option<Vec<_>>>();
    match question {
        ObligationQuestion::Satisfiable { query } => Some(vec![formulas(query)?]),
        ObligationQuestion::All { parts } => match parts.as_slice() {
            [ObligationQuestion::Satisfiable { query: premises }, ObligationQuestion::Unsatisfiable { query: counterexamples }] =>
                Some(vec![formulas(premises)?, formulas(counterexamples)?]),
            _ => None,
        },
        _ => None,
    }
}

/// The verdict of an obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObligationVerdict {
    Proved,
    Refuted,
    /// Neither proved nor refuted: the decision limit ended the search.
    Unproved,
}

impl ObligationVerdict {
    pub fn as_str(self) -> &'static str {
        match self {
            ObligationVerdict::Proved => "proved",
            ObligationVerdict::Refuted => "refuted",
            ObligationVerdict::Unproved => "unproved",
        }
    }
}

/// A question that a decision rests on: its formulas and its answer with
/// what shows the answer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Asked {
    pub name: String,
    pub formulas: Vec<Formula>,
    pub answer: Answer,
}

/// A situation without a response: what the environment fixes, and the
/// statements that cannot all be kept in it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Counterexample {
    pub facts: Vec<String>,
    pub statements: Vec<String>,
}

/// The decision of one obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Decision {
    pub verdict: ObligationVerdict,
    /// Why the obligation is refuted or unproved.
    pub reason: Option<String>,
    /// Every question that the verdict rests on.
    pub asked: Vec<Asked>,
    /// For a refuted question of responses: each situation without one.
    pub counterexamples: Vec<Counterexample>,
}

impl ProofObligations {
    /// Recover the exact MMT questions bound to one original Core problem.
    pub fn propositional_questions(&self, position: usize) -> Result<Vec<Vec<Formula>>, String> {
        let obligation = &self.obligations[position];
        let input = self.propositional.get(&position).ok_or_else(|| format!("{} has no checked propositional input", obligation.name))?;
        let mut expected_pool = Vec::new();
        let (expected, proposition) = propositional_question(input.input.problem(), |formula| {
            expected_pool.push(formula.clone());
            expected_pool.len() - 1
        });
        let mismatch = || format!("{} does not match the questions of its original Core input", obligation.name);
        let formulas = propositional_formulas(&obligation.question, &self.pool).ok_or_else(mismatch)?;
        if obligation.property == PROPOSITIONAL_CHECK
            && obligation.name == format!("check/{}", input.name)
            && obligation.proposition == proposition
            && obligation.statements.is_empty()
            && Some(&formulas) == propositional_formulas(&expected, &expected_pool).as_ref()
        {
            return Ok(formulas);
        }
        Err(mismatch())
    }

    /// An instance that holds the pool, each formula under its own number.
    pub fn instance(&self, decisions: Option<u64>) -> Instance {
        let inst = Instance::new(&[], &[], decisions);
        for (number, formula) in self.pool.iter().enumerate() {
            let id = inst.add(formula);
            debug_assert_eq!(id, number);
        }
        inst
    }

    /// Decides one obligation over an instance of [`ProofObligations::instance`].
    pub fn decide(&self, inst: &Instance, obligation: &ProofObligation) -> Decision {
        let mut asked = Vec::new();
        let mut found = Vec::new();
        let (verdict, mut reason) = decide_question(inst, &obligation.question, &self.owners, &mut asked, &mut found);
        if verdict == ObligationVerdict::Refuted && obligation.property == "correctness" {
            if let Some(explanation) = refinement_counterexample(&asked) {
                reason = Some(explanation);
            }
        }
        let formulas = inst.formulas();
        let counterexamples = found
            .into_iter()
            .map(|(given, conclusions): (Vec<usize>, Vec<usize>)| {
                let mut statements: Vec<String> = conclusions.iter().filter_map(|id| self.owners.get(id)).flat_map(|owner| owner.split_whitespace().map(str::to_string)).collect();
                statements.sort();
                statements.dedup();
                Counterexample { facts: given.iter().map(|&id| formulas[id].to_string().replace('?', "")).collect(), statements }
            })
            .collect();
        Decision { verdict, reason, asked, counterexamples }
    }
}

/// A refuted refinement has either an excluded environment or a behaviour
/// that keeps the details and violates their reference.
fn refinement_counterexample(asked: &[Asked]) -> Option<String> {
    let failure = asked.last()?;
    let witness = failure.answer.witness()?;
    match asked.len() {
        1 => return Some("there is an environment accepted by the reference that its details exclude within the stated bound".into()),
        2 => {}
        _ => return None,
    }
    let mut reason = "there is a behaviour that keeps the details and violates the reference within the stated bound".to_string();
    let Some(Formula::And(comparison)) = failure.formulas.last() else { return Some(reason) };
    let [details, Formula::Not(reference)] = comparison.as_slice() else { return Some(reason) };
    let facts = witness.atoms();
    let mut action = None;
    details.atoms(true, &mut |atom, positive| {
        if action.is_none() && positive && matches!(atom, Atom::Act { .. }) && facts.get(atom) == Some(&true) {
            action = Some(atom.to_string());
        }
    });
    let mut state = None;
    reference.atoms(true, &mut |atom, positive| {
        if state.is_none() && matches!(atom, Atom::Val { .. }) && facts.get(atom) == Some(&!positive) {
            state = Some(if positive { format!("¬{atom}") } else { atom.to_string() });
        }
    });
    if let (Some(action), Some(state)) = (action, state) {
        reason.push_str(&format!(". The counterexample includes `{action}` and `{state}`. If the action must establish the state required by the reference, state that relation explicitly"));
    }
    Some(reason)
}

fn ask(inst: &Instance, name: &str, query: &[usize], asked: &mut Vec<Asked>) -> Status {
    let answer = inst.decide(query);
    let status = answer.status;
    let formulas = inst.formulas();
    asked.push(Asked { name: name.to_string(), formulas: query.iter().map(|&id| formulas[id].clone()).collect(), answer });
    status
}

/// The formulas of an unsatisfiable query that a statement owns and that
/// the refutation needs: each is left out in turn and kept only where the
/// query without it has a valuation. What no statement owns is kept.
fn owned_core(inst: &Instance, query: &[usize], owners: &BTreeMap<usize, String>) -> Vec<usize> {
    let rest: Vec<usize> = query.iter().copied().filter(|id| !owners.contains_key(id)).collect();
    let mut core: Vec<usize> = query.iter().copied().filter(|id| owners.contains_key(id)).collect();
    let mut at = 0;
    while at < core.len() {
        let removed = core.remove(at);
        let without: Vec<usize> = rest.iter().chain(&core).copied().collect();
        if inst.decide(&without).status != Status::Unsatisfiable {
            core.insert(at, removed);
            at += 1;
        }
    }
    core
}

fn decide_question(inst: &Instance, question: &ObligationQuestion, owners: &BTreeMap<usize, String>, asked: &mut Vec<Asked>, found: &mut Vec<(Vec<usize>, Vec<usize>)>) -> (ObligationVerdict, Option<String>) {
    use ObligationVerdict::*;
    match question {
        ObligationQuestion::Satisfiable { query } => match ask(inst, "satisfiable", query, asked) {
            Status::Satisfiable => (Proved, None),
            Status::Unsatisfiable => {
                // The statements whose formulas the refutation needs.
                let core = owned_core(inst, query, owners);
                if !core.is_empty() {
                    found.push((Vec::new(), core));
                }
                (Refuted, Some("the formulas hold together in no valuation".to_string()))
            }
            Status::Unknown => (Unproved, Some("the decision limit ended the search".to_string())),
        },
        ObligationQuestion::Unsatisfiable { query } => match ask(inst, "unsatisfiable", query, asked) {
            Status::Unsatisfiable => (Proved, None),
            Status::Satisfiable => (Refuted, Some("the formulas hold together in a valuation".to_string())),
            Status::Unknown => (Unproved, Some("the decision limit ended the search".to_string())),
        },
        ObligationQuestion::ForAllExists { premises, standing, conclusions, chosen } => {
            let chosen: std::collections::BTreeSet<&str> = chosen.iter().map(String::as_str).collect();
            match for_all_exists(inst, premises, standing, conclusions, &|symbol| chosen.contains(symbol)) {
                ForAll::Holds { refuted, .. } => {
                    for (number, query) in refuted.iter().enumerate() {
                        if ask(inst, &format!("no situation is left without a response ({})", number + 1), query, asked) != Status::Unsatisfiable {
                            return (Unproved, Some("a question that the answer rests on is not refuted again".to_string()));
                        }
                    }
                    (Proved, None)
                }
                ForAll::Fails { situations } => {
                    for (number, situation) in situations.iter().enumerate() {
                        let occurs: Vec<usize> = premises.iter().chain(&situation.given).copied().collect();
                        let kept: Vec<usize> = situation.conclusions.iter().chain(&situation.given).copied().collect();
                        if ask(inst, &format!("situation {}: the situation can occur", number + 1), &occurs, asked) != Status::Satisfiable || ask(inst, &format!("situation {}: the statements cannot all be kept", number + 1), &kept, asked) != Status::Unsatisfiable {
                            return (Unproved, Some("a situation without a response is not shown again".to_string()));
                        }
                    }
                    found.extend(situations.iter().map(|s| (s.given.clone(), s.conclusions.clone())));
                    (Refuted, Some(format!("{} situation(s) have no response that keeps every statement that applies", situations.len())))
                }
                ForAll::Open { reason } => (Unproved, Some(reason)),
            }
        }
        ObligationQuestion::All { parts } => {
            let mut open = None;
            for part in parts {
                match decide_question(inst, part, owners, asked, found) {
                    (Refuted, why) => return (Refuted, why),
                    (Unproved, why) => open = open.or(why),
                    (Proved, _) => {}
                }
            }
            match open {
                Some(why) => (Unproved, Some(why)),
                None => (Proved, None),
            }
        }
        ObligationQuestion::Any { parts } => {
            let (mut open, mut refuted) = (None, Vec::new());
            for part in parts {
                match decide_question(inst, part, owners, asked, found) {
                    (Proved, _) => return (Proved, None),
                    (Unproved, why) => open = open.or(why),
                    (Refuted, why) => refuted.extend(why),
                }
            }
            match open {
                Some(why) => (Unproved, Some(why)),
                None => (Refuted, Some(refuted.join("; and "))),
            }
        }
        ObligationQuestion::Not { part } => {
            // What the part finds is evidence either way; a situation that
            // refutes the part proves this question and names no fault.
            let mut kept = Vec::new();
            match decide_question(inst, part, owners, asked, &mut kept) {
                (Proved, _) => (Refuted, Some("the question that is denied holds".to_string())),
                (Refuted, _) => (Proved, None),
                (Unproved, why) => (Unproved, why),
            }
        }
    }
}

/// A package read over a trace of some moments, with its formulas in the
/// pool of the obligations.
struct Unrolled<'a> {
    model: &'a Model,
    /// The background at every moment, and what the terms mean.
    background: Vec<usize>,
    /// The formula of each contract over the trace.
    group: Vec<usize>,
    /// The assumption of each contract over the trace, where it has one.
    guard: Vec<Option<Formula>>,
    /// The formula of each contract as a response keeps it: a condition
    /// about the system is read as the response makes it.
    applied: Vec<usize>,
    normative: Vec<bool>,
    soft: Vec<bool>,
    /// A description of the environment, which is an assumption.
    environment: Vec<bool>,
    /// A description of the system, which is a guarantee.
    system: Vec<bool>,
    /// For each contract, the assumptions that a shared condition block
    /// distributes to it: the descriptions of the environment written in a
    /// block that holds the statement. An assumption outside every block
    /// is distributed to every contract of the document, and is a premise.
    scoped: Vec<Vec<usize>>,
    /// An assumption whose scope a shared condition block narrows.
    narrowed: Vec<bool>,
    /// A contract of a reference that is read beside the document: the
    /// quote of a source. It is no part of the document, and no question
    /// of the document assumes or keeps it unless it asks about it.
    reference: Vec<bool>,
    responsibility: situations::Responsibility,
}

impl<'a> Unrolled<'a> {
    fn new(set: &SpecSet, model: &'a Model, lex: &trion_language::reading::Lexicon, moments: usize, inst: &Instance) -> Self {
        let (trace, control) = super::trace_of(set, model, lex, moments);
        let count = model.constraints.len();
        let authored = Authored::new(set, lex);
        let situated = Situated::of(model, &control);
        let soft: Vec<bool> = (0..count).map(|i| authored.is_recommendation(&model.constraints[i])).collect();
        let described: Vec<bool> = (0..count).map(|i| authored.is_description(&model.constraints[i])).collect();
        // The actors of the system are those that the document declares; a
        // document that declares none has the actors whose actions its
        // normative statements speak about.
        let actors = super::environment::system_actors(model, &control, &|c| authored.is_description(c));
        // A requirement of what the environment does is an assumption.
        let assumed: Vec<bool> = (0..count).map(|i| matches!(model.constraints[i].kind, ConstraintKind::Spec | ConstraintKind::Permission) && !described[i] && super::environment::of_environment(&model.constraints[i], &actors)).collect();
        let normative: Vec<bool> = (0..count).map(|i| matches!(model.constraints[i].kind, ConstraintKind::Spec | ConstraintKind::Permission) && !soft[i] && !described[i] && !assumed[i]).collect();
        let description = |i: usize| model.constraints[i].kind == ConstraintKind::Spec && described[i];
        let system: Vec<bool> = (0..count).map(|i| {
            let constraint = &model.constraints[i];
            description(i) && situated.describes_system(model, constraint)
        }).collect();
        let environment: Vec<bool> = (0..count).map(|i| (description(i) && !system[i]) || assumed[i]).collect();
        let base: Vec<usize> = trace.background.iter().map(|f| inst.add(f)).collect();
        let group: Vec<usize> = trace.groups.iter().map(|(f, _)| inst.add(f)).collect();
        let background: Vec<usize> = base.into_iter().chain((0..count).filter(|&i| model.constraints[i].kind.is_vocabulary()).map(|i| group[i])).collect();
        // The roles of the system are the system's: a bound role and the
        // form that it requires speak about what the system is, which no
        // behaviour of the environment chooses.
        let is_normative = |i: usize| normative[i] || model.constraints[i].kind.is_form();
        let responsibility = situations::Responsibility::of(model, &situated.events, &situated.given, &situated.system, &is_normative).following(model, &inst.formulas(), &situated.events, &actors);
        let mut read = model.clone();
        for i in (0..count).filter(|&i| normative[i]) {
            let assume = read.constraints[i].assume.clone();
            read.constraints[i].assume = situations::seen(&assume, &|symbol| responsibility.seen_apart(symbol));
        }
        let (as_kept, _) = super::trace_of(set, &read, lex, moments);
        let applied = (0..count).map(|i| if normative[i] && model.constraints[i].has_guard() { inst.add(&as_kept.groups[i].0) } else { group[i] }).collect();
        // The scope of an assumption sentence is the document, unless a
        // shared condition block narrows it to the statements of the block
        // (AGENTS.md, rule 3 of responsibility; `formal/Trion/Merging.lean`).
        let blocks: BTreeMap<(String, usize), (String, Vec<usize>)> = set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.specs).map(|spec| ((spec.file.clone(), spec.line), (spec.file.clone(), spec.scope_lines.clone()))).collect();
        let block_of = |i: usize| model.constraints[i].refs.first().and_then(|r| blocks.get(&(r.file.clone(), r.line))).cloned();
        let application: Vec<Vec<&SpecRef>> = model.constraints.iter().map(|constraint| {
            constraint.refs.first().and_then(|at| authored.owner(at)).map_or_else(Vec::new, |(_, doc)| {
                doc.application_ancestors.iter().chain(doc.application_scope.iter()).collect()
            })
        }).collect();
        let narrowed: Vec<bool> = (0..count).map(|i| environment[i] && (!application[i].is_empty() || block_of(i).is_some_and(|(_, lines)| !lines.is_empty()))).collect();
        let scoped: Vec<Vec<usize>> = (0..count)
            .map(|j| {
                (0..count).filter(|&i| i != j && narrowed[i]).filter(|&i| {
                    if !application[j].starts_with(&application[i]) {
                        return false;
                    }
                    let Some((file, lines)) = block_of(i).filter(|(_, lines)| !lines.is_empty()) else {
                        return true;
                    };
                    if application[i] != application[j] {
                        return false;
                    }
                    block_of(j).is_some_and(|(scope_file, scope_lines)| scope_file == file && scope_lines.starts_with(&lines))
                }).collect()
            })
            .collect();
        let reference = vec![false; count];
        Self { model, background, group, guard: trace.groups.into_iter().map(|(_, g)| g).collect(), applied, normative, soft, environment, system, scoped, narrowed, reference, responsibility }
    }

    /// The same contracts, with those of the statements `ids` (and of their
    /// instances) read as a reference beside the document.
    fn with_reference(mut self, ids: &BTreeSet<String>) -> Self {
        for i in 0..self.group.len() {
            let id = self.id_of(i);
            let of_instance = id.split_once('/').is_some_and(|(statement, _)| ids.contains(statement));
            self.reference[i] = ids.contains(&id) || of_instance;
        }
        self
    }

    /// The formula of contract `i` as its scope gives it: the assumptions
    /// that a block distributes to it imply its formula.
    fn distributed(&self, inst: &Instance, i: usize, formula: usize) -> usize {
        if self.scoped[i].is_empty() {
            return formula;
        }
        let pool = inst.formulas();
        let assumed = Formula::And(self.scoped[i].iter().map(|&a| pool[self.group[a]].clone()).collect());
        inst.add(&Formula::implies(assumed, pool[formula].clone()))
    }

    /// The assumption of contract `i` with the assumptions that a block
    /// distributes to it.
    fn assumption(&self, inst: &Instance, i: usize) -> Formula {
        let own = self.guard[i].clone().unwrap_or(Formula::True);
        if self.scoped[i].is_empty() {
            return own;
        }
        let pool = inst.formulas();
        Formula::And(self.scoped[i].iter().map(|&a| pool[self.group[a]].clone()).chain([own]).collect())
    }

    fn id_of(&self, i: usize) -> String {
        self.model.constraints[i].refs.first().map_or(String::new(), |r| r.id.clone())
    }

    /// A contract that the system guarantees.
    fn guaranteed(&self, i: usize) -> bool {
        self.normative[i] || self.system[i]
    }

    /// The contracts that share a symbol with contract `i`, directly or
    /// through other contracts and the background: the component of `i`.
    /// Contracts of different components constrain different symbols, so a
    /// question over all of them is the conjunction of the same question
    /// over each component.
    fn component(&self, inst: &Instance, i: usize) -> Vec<bool> {
        let pool = inst.formulas();
        let untimed = |symbol: &str| -> String {
            match symbol.rsplit_once('@') {
                Some((term, moment)) if !moment.is_empty() && moment.chars().all(|c| c.is_ascii_digit()) => term.to_string(),
                _ => symbol.to_string(),
            }
        };
        let symbols_of = |id: usize| -> BTreeSet<String> {
            let mut out = BTreeSet::new();
            pool[id].atoms(true, &mut |atom, _| out.extend(atom.symbols().into_iter().map(untimed)));
            out
        };
        let own: Vec<BTreeSet<String>> = self.group.iter().map(|&g| symbols_of(g)).collect();
        let links: Vec<BTreeSet<String>> = self.background.iter().map(|&b| symbols_of(b)).collect();
        let mut reached: BTreeSet<String> = own[i].clone();
        let mut inside = vec![false; self.group.len()];
        inside[i] = true;
        loop {
            let mut grew = false;
            for link in &links {
                if !link.is_disjoint(&reached) && !link.is_subset(&reached) {
                    reached.extend(link.iter().cloned());
                    grew = true;
                }
            }
            for (j, symbols) in own.iter().enumerate() {
                if !inside[j] && !symbols.is_disjoint(&reached) {
                    inside[j] = true;
                    reached.extend(symbols.iter().cloned());
                    grew = true;
                }
            }
            if !grew {
                return inside;
            }
        }
    }

    /// The definitions that a comparison of statements is read under: the
    /// background, what the terms mean, and each enumeration that closes the
    /// domain of an attribute, as a description of the environment does
    /// (`The status is open or closed.`). The statements among `apart`, which
    /// are compared, are left out: a question does not assume what it
    /// compares, and no other description is assumed.
    fn premises_apart(&self, inst: &Instance, apart: BTreeSet<usize>) -> Vec<usize> {
        let pool = inst.formulas();
        let closes = |i: usize| {
            let mut found = false;
            pool[self.group[i]].atoms(true, &mut |atom, _| found |= matches!(atom, trion_solver::Atom::Dom { .. }));
            found
        };
        self.background.iter().copied().chain((0..self.group.len()).filter(|&i| self.environment[i] && !self.narrowed[i] && !self.reference[i] && !apart.contains(&i) && closes(i)).map(|i| self.group[i])).collect()
    }

    /// What every question of the environment holds: the background and
    /// the descriptions of the environment.
    fn premises(&self) -> Vec<usize> {
        self.premises_among(&|_| false)
    }

    /// The premises, with the descriptions of a reference among `among`.
    fn premises_among(&self, among: &dyn Fn(usize) -> bool) -> Vec<usize> {
        self.background.iter().copied().chain((0..self.group.len()).filter(|&i| self.environment[i] && !self.narrowed[i] && (!self.reference[i] || among(i))).map(|i| self.group[i])).collect()
    }

    /// For every behaviour of the environment that its assumptions allow,
    /// some behaviour of the system keeps each guarantee among `among`.
    fn consistency(&self, inst: &Instance, among: &dyn Fn(usize) -> bool, owners: &mut BTreeMap<usize, String>) -> ObligationQuestion {
        self.keeping(inst, among, &|_| false, owners)
    }

    /// As `consistency`, with the advice of the recommendations in `advised`
    /// kept as well.
    fn keeping(&self, inst: &Instance, among: &dyn Fn(usize) -> bool, advised: &dyn Fn(usize) -> bool, owners: &mut BTreeMap<usize, String>) -> ObligationQuestion {
        let count = self.group.len();
        let kinds = &self.model.constraints;
        // What the environment may do, and the laws of the terms and of time.
        // The form that a bound role requires is required of the system: it is
        // a conclusion, and no premise.
        let shaped = |i: usize| kinds[i].kind.is_form();
        let standing: Vec<usize> = self.background.iter().copied().chain((0..count).filter(|&i| !kinds[i].kind.is_axiom() && !shaped(i) && !self.normative[i] && !self.soft[i] && !self.system[i] && !self.narrowed[i] && (!self.reference[i] || among(i)) && (self.environment[i] || kinds[i].kind != ConstraintKind::Spec)).map(|i| self.group[i])).collect();
        // The situations that can occur: the standing formulas for some
        // state of the system, each term of the response a copy of its own.
        let current = inst.formulas();
        // A formula about the system alone says nothing of which situations
        // can occur: it is no premise, and the response keeps it. As a premise
        // its contradiction would leave no situation, and the question would
        // hold of nothing.
        let of_system_alone = |formula: &Formula| {
            let (mut symbols, mut chosen) = (0, true);
            formula.atoms(true, &mut |atom, _| {
                for symbol in atom.symbols() {
                    symbols += 1;
                    chosen &= self.responsibility.response(symbol);
                }
            });
            symbols > 0 && chosen
        };
        let premises: Vec<usize> = standing
            .iter()
            .filter(|&&id| !of_system_alone(&current[id]))
            .map(|&id| {
                let copy = situations::seen(&current[id], &|symbol| self.responsibility.response(symbol));
                if copy == current[id] {
                    id
                } else {
                    inst.add(&copy)
                }
            })
            .collect();
        let mut conclusions = Vec::new();
        for i in (0..count).filter(|&i| ((self.guaranteed(i) || shaped(i)) && among(i)) || (self.soft[i] && advised(i))) {
            let id = self.distributed(inst, i, if self.normative[i] { self.applied[i] } else { self.group[i] });
            // A form is owned by the role that requires it and by the statement that does not have it.
            let mut owner = if shaped(i) { self.model.constraints[i].refs.iter().map(|r| r.id.clone()).collect::<Vec<_>>().join(" ") } else { self.id_of(i) };
            // An assumption that a block distributes to it is named with it.
            for &a in &self.scoped[i] {
                owner.push(' ');
                owner.push_str(&self.id_of(a));
            }
            owners.insert(id, owner);
            conclusions.push(id);
        }
        let pool = inst.formulas();
        let mut chosen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        for &id in premises.iter().chain(&standing).chain(&conclusions) {
            pool[id].atoms(true, &mut |atom, _| chosen.extend(atom.symbols().into_iter().filter(|symbol| self.responsibility.response(symbol)).map(str::to_string)));
        }
        ObligationQuestion::ForAllExists { premises, standing, conclusions, chosen: chosen.into_iter().collect() }
    }

    /// An environment that the descriptions allow meets an assumption of a
    /// normative statement among `among`.
    fn compatibility(&self, inst: &Instance, among: &dyn Fn(usize) -> bool, owners: &mut BTreeMap<usize, String>) -> ObligationQuestion {
        let asking: Vec<usize> = (0..self.group.len()).filter(|&i| self.normative[i] && among(i)).collect();
        let assumptions: Vec<Formula> = asking.iter().map(|&i| self.assumption(inst, i)).collect();
        let met = inst.add(&if assumptions.is_empty() { Formula::True } else { Formula::Or(assumptions) });
        // The assumptions are those of the statements that ask them: a
        // refutation that needs them names those statements.
        let mut ids: Vec<String> = asking.iter().flat_map(|&i| std::iter::once(i).chain(self.scoped[i].iter().copied())).map(|i| self.id_of(i)).filter(|id| !id.is_empty()).collect();
        ids.sort();
        ids.dedup();
        if !ids.is_empty() {
            owners.entry(met).or_insert_with(|| ids.join(" "));
        }
        ObligationQuestion::Satisfiable { query: self.premises_among(among).into_iter().chain([met]).collect() }
    }

    /// The contracts of the statement `id` and of its instances.
    fn of(&self, id: &str) -> Vec<usize> {
        let nested = format!("{id}/");
        (0..self.group.len()).filter(|&i| matches!(self.model.constraints[i].kind, ConstraintKind::Spec | ConstraintKind::Permission) && self.model.constraints[i].refs.first().is_some_and(|r| r.id == id || r.id.starts_with(&nested))).collect()
    }

    fn asked(&self, inst: &Instance, contracts: &[usize]) -> Formula {
        Formula::Or(contracts.iter().map(|&i| self.assumption(inst, i)).collect())
    }

    fn kept(&self, inst: &Instance, contracts: &[usize]) -> Formula {
        let ids: Vec<usize> = contracts.iter().map(|&i| self.distributed(inst, i, self.group[i])).collect();
        let pool = inst.formulas();
        Formula::And(ids.into_iter().map(|id| pool[id].clone()).collect())
    }

    /// The details accept each environment of the statement, and each
    /// behaviour that keeps the details keeps the statement.
    fn refinement(&self, inst: &Instance, own: &[usize], parts: &[usize]) -> ObligationQuestion {
        let premises = self.premises();
        let environments = inst.add(&Formula::And(vec![self.asked(inst, own), Formula::not(self.asked(inst, parts))]));
        let behaviours = inst.add(&Formula::And(vec![self.kept(inst, parts), Formula::not(self.kept(inst, own))]));
        ObligationQuestion::All { parts: vec![ObligationQuestion::Unsatisfiable { query: premises.iter().copied().chain([environments]).collect() }, ObligationQuestion::Unsatisfiable { query: premises.into_iter().chain([behaviours]).collect() }] }
    }

    /// The conjuncts of the formulas of some contracts: one formula for
    /// each, so that each is refuted on its own.
    fn conjuncts(&self, inst: &Instance, contracts: &[usize]) -> Vec<Formula> {
        fn flatten(formula: &Formula, out: &mut Vec<Formula>) {
            match formula {
                Formula::And(items) => items.iter().for_each(|item| flatten(item, out)),
                Formula::True => {}
                other => out.push(other.clone()),
            }
        }
        let pool = inst.formulas();
        let mut out = Vec::new();
        for &i in contracts {
            flatten(&pool[self.group[i]], &mut out);
        }
        out
    }

    /// In each environment that the document allows (the background, what
    /// the terms mean and the descriptions of the environment), `left`
    /// implies each conjunct of `right`.
    fn implies(&self, inst: &Instance, left: &[usize], right: &[usize]) -> Vec<ObligationQuestion> {
        let premises = self.premises_apart(inst, left.iter().chain(right).copied().collect());
        let left: Vec<usize> = self.conjuncts(inst, left).iter().map(|f| inst.add(f)).collect();
        self.conjuncts(inst, right).into_iter().map(|c| ObligationQuestion::Unsatisfiable { query: premises.iter().chain(&left).copied().chain([inst.add(&Formula::not(c))]).collect() }).collect()
    }
}

/// Builds the proof obligations of an analysed package at a trace of
/// `moments` moments. Nothing is decided.
pub(super) fn build(set: &SpecSet, model: &Model, lex: &trion_language::reading::Lexicon, moments: usize, scope: usize, decisions: Option<u64>) -> ProofObligations {
    let inst = Instance::new(&[], &[], decisions);
    let package = Unrolled::new(set, model, lex, moments, &inst);
    let count = model.constraints.len();
    let bound = match model.instance_scope {
        Some(n) => format!("traces of {moments} moments, domains of {n} individuals"),
        // Without `individuals` each type has one individual, named by its
        // noun: the same contracts, at a bound of one.
        None => format!("traces of {moments} moments, domains of one individual of each type"),
    };
    let mut owners: BTreeMap<usize, String> = BTreeMap::new();
    // A description and what a statement says about terms are owned by their
    // statements too, so that a refutation that needs them names them.
    for i in (0..count).filter(|&i| package.environment[i] || package.system[i] || model.constraints[i].kind.is_vocabulary()) {
        let id = package.id_of(i);
        if !id.is_empty() {
            owners.entry(package.group[i]).or_insert(id);
        }
    }
    let mut obligations = Vec::new();
    let mut findings = Vec::new();
    let all = |_: usize| true;

    // Consistency: for every input of the environment, some behaviour of
    // the system keeps every guarantee, over the whole trace.
    obligations.push(ProofObligation {
        name: "consistency".to_string(),
        property: "consistency".to_string(),
        proposition: format!("within {bound}: for every behaviour of the environment that its assumptions allow, some behaviour of the system keeps every guarantee over the whole trace"),
        statements: (0..count).filter(|&i| package.guaranteed(i)).map(|i| package.id_of(i)).collect(),
        question: package.consistency(&inst, &all, &mut owners),
    });

    // Compatibility: an environment exists.
    obligations.push(ProofObligation {
        name: "compatibility".to_string(),
        property: "compatibility".to_string(),
        proposition: format!("within {bound}: an environment that the statements without normative force allow meets an assumption of a statement"),
        statements: Vec::new(),
        question: package.compatibility(&inst, &all, &mut owners),
    });

    // Realizability: a guarantee that requires a response before an event
    // of the environment is kept by no system where the environment can
    // bring that event about before the response can come: at the first
    // moment, or at the moment after the trigger of the statement. Whatever
    // moment a system chooses, the environment may act first, and no system
    // knows an input that has not happened. A response to each whole
    // behaviour of the environment exists all the same, so consistency
    // alone does not find it.
    for shape in &model.temporal {
        let Some(i) = (0..count).find(|&i| package.normative[i] && package.id_of(i) == shape.statement.id) else { continue };
        for reference in shape.responses.iter().flat_map(|r| &r.references).filter(|r| r.relation == "before" && r.related_kind == "event") {
            let Some(event) = &reference.event else { continue };
            // Free when each term of the related occurrence is the environment's,
            // and there is one: an action or an event of the system is no input.
            let (mut free, mut terms) = (true, 0);
            event.atoms(true, &mut |atom, _| {
                if let trion_solver::Atom::Event { key } | trion_solver::Atom::Act { key } = atom {
                    terms += 1;
                    free &= package.responsibility.by_actor(key) == Some(false);
                }
            });
            free &= terms > 0;
            if !free {
                continue;
            }
            let triggered = matches!(shape.activation, trion_language::reading::Activation::Occurrence { .. }) && model.constraints[i].has_guard();
            let mut early = vec![inst.add(&at_moment(event, if triggered { 1 } else { 0 }))];
            // The assumptions that a block distributes to the statement hold as well.
            early.extend(package.scoped[i].iter().map(|&a| package.group[a]));
            if triggered {
                early.push(inst.add(&at_moment(&model.constraints[i].assume, 0)));
            }
            obligations.push(ProofObligation {
                name: format!("realizability/{}/{}", shape.statement.id, reference.related),
                property: "realizability".to_string(),
                proposition: format!("within {bound}: the environment cannot bring about `{}` {}, before a response of [{}] can come", reference.related, if triggered { "at the moment after the trigger" } else { "at the first moment" }, shape.statement.id),
                statements: vec![shape.statement.id.clone()],
                question: ObligationQuestion::Unsatisfiable { query: package.premises().into_iter().chain(early).collect() },
            });
        }
    }

    // Correctness and completeness against each statement that other
    // statements detail: the statement is the reference of its details.
    for (statement, details) in detailed(model) {
        let own = package.of(&statement.id);
        let parts: Vec<usize> = details.iter().flat_map(|d| package.of(&d.id)).collect();
        if own.is_empty() || parts.is_empty() {
            continue;
        }
        let names = details.iter().map(|d| format!("`{}`", d.id)).collect::<Vec<_>>().join(", ");
        let statements: Vec<String> = std::iter::once(statement.id.clone()).chain(details.iter().map(|d| d.id.clone())).collect();
        let refines = package.refinement(&inst, &own, &parts);
        obligations.push(ProofObligation {
            name: format!("refinement/{}", statement.id),
            property: "correctness".to_string(),
            proposition: format!("within {bound}: the details {names} of `{}` accept each environment of it, and each behaviour that keeps them keeps it", statement.id),
            statements: statements.clone(),
            question: refines.clone(),
        });
        // Complete: the details refine the statement, or no consistent and
        // compatible document refines both, since together they are not
        // consistent or not compatible.
        let both = |i: usize| own.contains(&i) || parts.contains(&i);
        let mut apart = BTreeMap::new();
        obligations.push(ProofObligation {
            name: format!("completeness/{}", statement.id),
            property: "completeness".to_string(),
            proposition: format!("within {bound}: the details {names} refine `{}`, or no consistent and compatible document refines both", statement.id),
            statements,
            question: ObligationQuestion::Any { parts: vec![refines, ObligationQuestion::Not { part: Box::new(ObligationQuestion::All { parts: vec![package.consistency(&inst, &both, &mut apart), package.compatibility(&inst, &both, &mut apart)] }) }] },
        });
    }

    // Each recommendation: a system that keeps every requirement can follow
    // the advice as well. Advice that cannot be followed weighs nothing
    // against a requirement, and the document says something that it means
    // nobody to do.
    for i in (0..count).filter(|&i| package.soft[i]) {
        let id = package.id_of(i);
        obligations.push(ProofObligation {
            name: format!("recommendation/{id}"),
            property: "recommendation".to_string(),
            proposition: format!("within {bound}: where some behaviour of the system keeps every guarantee for every behaviour of the environment, some behaviour of the system keeps every guarantee and follows the advice of [{id}]"),
            statements: vec![id.clone()],
            // Where the requirements cannot be kept, consistency is refuted
            // and says so; the advice is then no fault of its own.
            question: {
                // The advice is asked within its component: a contradiction
                // among other statements is no fault of the advice, and is
                // reported by consistency.
                let near = package.component(&inst, i);
                let within = |j: usize| near[j];
                ObligationQuestion::Any {
                    parts: vec![
                        ObligationQuestion::Not { part: Box::new(package.consistency(&inst, &within, &mut BTreeMap::new())) },
                        package.keeping(&inst, &within, &|j| j == i, &mut owners),
                    ],
                }
            },
        });
    }

    // The recommendations together: each is a contract of the document, and
    // the document is their conjunction, so a system that keeps every
    // requirement can follow all of the advice at once. Advice against advice
    // is no default and no priority: conjunction is monotone, and a weight
    // decides nothing.
    let advised: Vec<usize> = (0..count).filter(|&i| package.soft[i]).collect();
    if advised.len() > 1 {
        let ids: Vec<String> = advised.iter().map(|&i| package.id_of(i)).collect();
        obligations.push(ProofObligation {
            name: "recommendation/together".to_string(),
            property: "recommendation".to_string(),
            proposition: format!("within {bound}: where some behaviour of the system keeps every guarantee for every behaviour of the environment, some behaviour of the system keeps every guarantee and follows the advice of {} together", ids.iter().map(|id| format!("[{id}]")).collect::<Vec<_>>().join(", ")),
            statements: ids,
            question: ObligationQuestion::Any {
                parts: vec![ObligationQuestion::Not { part: Box::new(package.consistency(&inst, &|_| true, &mut BTreeMap::new())) }, package.keeping(&inst, &|_| true, &|j| package.soft[j], &mut owners)],
            },
        });
    }

    // Each choice of a flow: its guards exclude each other and, without
    // `otherwise`, cover every case, at the instant of the choice.
    let bounds = super::Bounds { decisions, trace_length: moments, scope };
    for question in super::flows::choice_questions(set, model, lex, &inst, &package.group, bounds, &mut findings) {
        let named = question.guards.iter().map(|g| (g + 1).to_string()).collect::<Vec<_>>().join(" and ");
        let (name, says) = match question.kind {
            "exclusive" => (format!("choice/{}/{}/exclusive/{}", question.statement.id, question.after, named.replace(" and ", "-")), format!("the guards {named} of the choice after `{}` in [{}] do not hold together", question.after, question.statement.id)),
            _ => (format!("choice/{}/{}/covered", question.statement.id, question.after), format!("some guard of the choice after `{}` in [{}] holds", question.after, question.statement.id)),
        };
        let from = if question.premises.is_empty() { String::new() } else { format!(", from {}", question.premises.join(", ")) };
        obligations.push(ProofObligation {
            name,
            property: "choice".to_string(),
            proposition: format!("within {bound}: {says}{from}"),
            statements: vec![question.statement.id.clone()],
            // The background (one value of an attribute at a time, what the
            // terms mean) holds at the instant of the choice as everywhere.
            question: ObligationQuestion::Unsatisfiable { query: package.background.iter().copied().chain(question.query.into_iter().filter(|q| !package.background.contains(q))).collect() },
        });
    }

    // Each `check` block: its two sides are equivalent under the definitions.
    for check in set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.checks).filter(|c| !c.malformed) {
        // A side that names no statement, or one without a reading, is reported and not asked.
        let at = SpecRef::point(&check.file, check.line, &check.name);
        let side = |ids: &[String], findings: &mut Vec<Diagnostic>| match super::blocks::operand_formulas(set, model, ids) {
            Ok(_) => Some(ids.iter().flat_map(|id| package.of(id)).collect::<Vec<usize>>()),
            Err(error) => {
                findings.push(super::blocks::operand_diagnostic(&error, &format!("check {}", check.name), at.clone()));
                None
            }
        };
        let (Some(left), Some(right)) = (side(&check.left, &mut findings), side(&check.right, &mut findings)) else { continue };
        let mut parts = vec![ObligationQuestion::Satisfiable { query: package.premises_apart(&inst, left.iter().chain(&right).copied().collect()) }];
        parts.extend(package.implies(&inst, &left, &right));
        parts.extend(package.implies(&inst, &right, &left));
        obligations.push(ProofObligation {
            name: format!("check/{}", check.name),
            property: "check".to_string(),
            proposition: format!("within {bound}: the definitions and the descriptions have an interpretation, and in each of them {} and {} hold together or fail together", check.left.iter().map(|id| format!("[{id}]")).collect::<Vec<_>>().join(", "), check.right.iter().map(|id| format!("[{id}]")).collect::<Vec<_>>().join(", ")),
            statements: check.left.iter().chain(&check.right).cloned().collect(),
            question: ObligationQuestion::All { parts },
        });
    }

    let mut propositional = BTreeMap::new();
    for check in set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.propositional_checks) {
        let (question, proposition) = propositional_question(check.input.problem(), |formula| inst.add(formula));
        propositional.insert(obligations.len(), check.clone());
        obligations.push(ProofObligation {
            name: format!("check/{}", check.name),
            property: PROPOSITIONAL_CHECK.to_string(),
            proposition,
            statements: Vec::new(),
            question,
        });
    }

    // Each example of consistency: its input, read alone, is consistent or
    // is not, as the example expects.
    for (example, read) in super::blocks::consistency_examples(set, scope) {
        let at = SpecRef::point(&example.file, example.line, &example.name);
        let (isolated, lexicon, mini) = match read {
            Ok(read) => read,
            Err(message) => {
                findings.push(Diagnostic::error("example-invalid", format!("the example {} cannot run: {message}", example.name), vec![at]));
                continue;
            }
        };
        let expected = match example.expect.split_whitespace().collect::<Vec<_>>().join(" ").as_str() {
            "consistent" => "is consistent",
            "inconsistent" => "is not consistent",
            other => {
                findings.push(Diagnostic::error("example-invalid", format!("the example {} expects `{other}`: an example of consistency expects `consistent` or `inconsistent`, which a proof decides; what no proof decides is no expectation", example.name), vec![at]));
                continue;
            }
        };
        let own = Unrolled::new(&isolated, &mini, &lexicon, moments, &inst);
        let mut apart = BTreeMap::new();
        let question = own.consistency(&inst, &all, &mut apart);
        let question = if expected == "is consistent" { question } else { ObligationQuestion::Not { part: Box::new(question) } };
        obligations.push(ProofObligation {
            name: format!("example/{}", example.name),
            property: "example".to_string(),
            proposition: format!("within {bound}: the input of the example, read alone, {expected}"),
            statements: Vec::new(),
            question,
        });
    }

    // Each example of a comparison: the candidate stands to the base as the example expects.
    for example in set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.examples).filter(|e| e.kind == "comparison") {
        let at = SpecRef::point(&example.file, example.line, &example.name);
        let side = |ids: &[String], findings: &mut Vec<Diagnostic>| match super::blocks::operand_formulas(set, model, ids) {
            Ok(_) => Some(ids.iter().flat_map(|id| package.of(id)).collect::<Vec<usize>>()),
            // An example that names no statement cannot run; an operand
            // without a reading blocks it as it blocks a check.
            Err(super::blocks::OperandError::Unresolved) => {
                findings.push(Diagnostic::error("example-invalid", format!("the example {} cannot run: it names a statement that does not exist", example.name), vec![at.clone()]));
                None
            }
            Err(error) => {
                findings.push(super::blocks::operand_diagnostic(&error, &format!("comparison {}", example.name), at.clone()));
                None
            }
        };
        let (Some(base), Some(candidate)) = (side(&example.base, &mut findings), side(&example.candidate, &mut findings)) else { continue };
        let kept = |cs: &[usize]| -> Vec<usize> { package.conjuncts(&inst, cs).iter().map(|f| inst.add(f)).collect() };
        let premises = package.premises_apart(&inst, base.iter().chain(&candidate).copied().collect());
        let with = |extra: &[usize]| -> Vec<usize> { premises.iter().copied().chain(kept(&base)).chain(extra.iter().copied()).collect() };
        let denials: Vec<usize> = package.conjuncts(&inst, &candidate).into_iter().map(|c| inst.add(&Formula::not(c))).collect();
        // Consistency is that of a system that accepts every input, and not
        // the satisfiability of the formulas (AGENTS.md).
        let mut apart = BTreeMap::new();
        let consistent_base = package.consistency(&inst, &|i| base.contains(&i), &mut apart);
        let consistent_both = package.consistency(&inst, &|i| base.contains(&i) || candidate.contains(&i), &mut apart);
        let question = match example.expect.trim() {
            "base-inconsistent" => ObligationQuestion::Not { part: Box::new(consistent_base) },
            "redundant" => ObligationQuestion::All { parts: std::iter::once(consistent_base).chain(denials.iter().map(|&d| ObligationQuestion::Unsatisfiable { query: with(&[d]) })).collect() },
            "conflict" => ObligationQuestion::All { parts: vec![consistent_base, ObligationQuestion::Not { part: Box::new(consistent_both) }] },
            "extension" => ObligationQuestion::All { parts: vec![consistent_both, ObligationQuestion::Any { parts: denials.iter().map(|&d| ObligationQuestion::Satisfiable { query: with(&[d]) }).collect() }] },
            other => {
                findings.push(Diagnostic::error("example-invalid", format!("the example {} expects `{other}`: a comparison expects `base-inconsistent`, `redundant`, `conflict` or `extension`, which a proof decides", example.name), vec![at]));
                continue;
            }
        };
        obligations.push(ProofObligation {
            name: format!("example/{}", example.name),
            property: "example".to_string(),
            proposition: format!("within {bound}: the candidate {} is {} against the base {}", example.candidate.iter().map(|id| format!("[{id}]")).collect::<Vec<_>>().join(", "), example.expect.trim(), example.base.iter().map(|id| format!("[{id}]")).collect::<Vec<_>>().join(", ")),
            statements: example.base.iter().chain(&example.candidate).cloned().collect(),
            question,
        });
    }
    // Each quote of a source that reads as statements of the trion language
    // is a reference of the statements that cite it: they owe correctness
    // and completeness against it as details do against the statement they
    // detail. A quote that does not read so is traced and is no reference
    // (spec/verification.trion, `A source is a reference only if ...`).
    for quoted in quoted_references(set) {
        let mut joint = set.clone();
        let Some(root) = joint.packages.iter_mut().find(|p| p.is_root) else { continue };
        root.documents.push(quoted.document.clone());
        let lexicon = trion_language::reading::Lexicon::of(&joint);
        let mini = trion_language::reading::compile(&joint, &lexicon, scope);
        let reference: BTreeSet<String> = quoted.ids.iter().cloned().collect();
        let read = Unrolled::new(&joint, &mini, &lexicon, moments, &inst).with_reference(&reference);
        let own: Vec<usize> = quoted.ids.iter().flat_map(|id| read.of(id)).collect();
        let parts: Vec<usize> = quoted.citing.iter().flat_map(|id| read.of(id)).collect();
        if own.is_empty() || parts.is_empty() {
            continue;
        }
        for &i in &own {
            owners.entry(read.group[i]).or_insert_with(|| read.id_of(i));
        }
        let names = quoted.citing.iter().map(|id| format!("`{id}`")).collect::<Vec<_>>().join(", ");
        let statements: Vec<String> = quoted.citing.clone();
        let refines = read.refinement(&inst, &own, &parts);
        obligations.push(ProofObligation {
            name: format!("reference/{}", quoted.name),
            property: "correctness".to_string(),
            proposition: format!("within {bound}: the statements {names} that cite `{}` accept each environment of the quote, read as trion sentences, and each behaviour that keeps them keeps the quote", quoted.name),
            statements: statements.clone(),
            question: refines.clone(),
        });
        let both = |i: usize| own.contains(&i) || parts.contains(&i);
        let mut apart = BTreeMap::new();
        obligations.push(ProofObligation {
            name: format!("completeness/{}", quoted.name),
            property: "completeness".to_string(),
            proposition: format!("within {bound}: the statements {names} refine the quote `{}`, or no consistent and compatible document refines both", quoted.name),
            statements,
            question: ObligationQuestion::Any { parts: vec![refines, ObligationQuestion::Not { part: Box::new(ObligationQuestion::All { parts: vec![read.consistency(&inst, &both, &mut apart), read.compatibility(&inst, &both, &mut apart)] }) }] },
        });
    }
    ProofObligations { moments, individuals: model.instance_scope, pool: inst.formulas(), owners, obligations, propositional, findings }
}

/// A quote of a source that reads as statements of the trion language,
/// with the statements of the package that cite it.
struct QuotedReference {
    /// `SOURCE#QUOTE`.
    name: String,
    /// The quote as a document of the package that declares the source:
    /// one statement for each of its sentences.
    document: trion_language::document::Document,
    /// The identifiers of those statements.
    ids: Vec<String>,
    /// The statements of the package that cite the quote.
    citing: Vec<String>,
}

/// Each quote that some statement of the root package cites and that
/// parses, without an error, as statements of the trion language.
fn quoted_references(set: &SpecSet) -> Vec<QuotedReference> {
    use trion_language::document::Meta;
    let mut citing: BTreeMap<(String, String), Vec<String>> = BTreeMap::new();
    for spec in set.packages.iter().filter(|p| p.is_root).flat_map(|p| &p.documents).flat_map(|d| &d.specs) {
        for meta in &spec.meta {
            if let Meta::Cite { source, quote: Some(quote) } = meta {
                let ids = citing.entry((source.clone(), quote.clone())).or_default();
                if !ids.contains(&spec.display_id()) {
                    ids.push(spec.display_id());
                }
            }
        }
    }
    let mut out = Vec::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        for source in &doc.sources {
            for quote in &source.quotes {
                let Some(citing) = citing.get(&(source.name.clone(), quote.name.clone())) else { continue };
                let (mut parsed, diags) = trion_language::document::parse_statement(&quote.text);
                if diags.iter().any(|d| d.severity == trion_language::Severity::Error) || parsed.specs.is_empty() {
                    continue;
                }
                // A definition says what a term of the document means: read
                // beside the document it would change the reading of the
                // document itself, so a quote that defines is no reference.
                if parsed.specs.iter().any(|s| matches!(s.sentence.core, trion_language::syntax::ast::Core::Definition { .. })) {
                    continue;
                }
                let stem: String = format!("{}-{}", source.name, quote.name).chars().map(|c| if c.is_ascii_alphanumeric() { c.to_ascii_uppercase() } else { '-' }).collect();
                let mut ids = Vec::new();
                for (k, spec) in parsed.specs.iter_mut().enumerate() {
                    let id = format!("{stem}-Q{}", k + 1);
                    spec.id = Some(id.clone());
                    spec.file = source.file.clone();
                    spec.line = quote.line;
                    spec.meta.clear();
                    ids.push(id);
                }
                parsed.namespace = doc.namespace.clone();
                parsed.imports = doc.imports.clone();
                parsed.sources.clear();
                parsed.controls.clear();
                out.push(QuotedReference { name: format!("{}#{}", source.name, quote.name), document: parsed, ids, citing: citing.clone() });
            }
        }
    }
    out
}

/// A formula about one moment: each event, action and state of it at `moment`.
fn at_moment(formula: &Formula, moment: usize) -> Formula {
    use trion_solver::Atom;
    formula.clone().map_atoms(&|atom| match atom {
        Atom::Event { key } => Atom::Event { key: format!("{key}@{moment}") },
        Atom::Act { key } => Atom::Act { key: format!("{key}@{moment}") },
        Atom::Val { attr, value } => Atom::Val { attr: format!("{attr}@{moment}"), value },
        other => other,
    })
}

/// Each statement that other statements detail, with its details.
fn detailed(model: &Model) -> Vec<(SpecRef, Vec<SpecRef>)> {
    let mut details_of: BTreeMap<String, (SpecRef, Vec<SpecRef>)> = BTreeMap::new();
    for (detail, origins) in &model.refined {
        for origin in origins {
            let at = model.constraints.iter().flat_map(|c| c.refs.first()).find(|r| r.id == *detail).cloned().unwrap_or_else(|| SpecRef { id: detail.clone(), file: origin.file.clone(), line: origin.line, text: String::new() });
            details_of.entry(origin.id.clone()).or_insert_with(|| (origin.clone(), Vec::new())).1.push(at);
        }
    }
    details_of
        .into_values()
        .map(|(statement, mut details)| {
            details.sort_by(|a, b| a.id.cmp(&b.id));
            details.dedup_by(|a, b| a.id == b.id);
            (statement, details)
        })
        .collect()
}

/// Whether the details of a statement refine it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RefinementOutcome {
    pub statement: SpecRef,
    pub details: Vec<SpecRef>,
    /// `proved`, `refuted` or `unproved`.
    pub result: String,
    /// What fails where the result is `refuted`.
    pub reason: Option<String>,
}

