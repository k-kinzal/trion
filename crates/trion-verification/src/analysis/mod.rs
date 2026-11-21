//! Reading: the vocabulary, the model and the relations of a set, the
//! diagnostics of the language, and the proof obligations that the MMT form
//! states. Nothing here decides an obligation: `trioc` proves them.

use trion_solver::Instance;
use trion_language::{Diagnostic, Severity, SpecRef};
use trion_language::document::{parse_document, parse_statement, Document, Meta, Package, Spec, SpecSet, VocabularyMode};
use trion_solver::Formula;
use trion_language::reading::{build_table, occurrences, Constraint, ConstraintKind, Lexicon, Model, VocabEntry};
use trion_language::syntax::ast::{CompNode, Core, Modal, VpGroup};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

mod blocks;
mod responsibility;
mod environment;
mod flows;
mod isolation;
mod properties;
mod references;
mod situations;
mod structure;

pub use environment::Control;

pub use isolation::{temporal_forms, Isolation};
pub use references::{Counterexample, Asked, Decision, ObligationQuestion, ObligationVerdict, ProofObligation, ProofObligations, RefinementOutcome, PROPOSITIONAL_CHECK};
pub use properties::check as check_properties;

use blocks::{Environment, Operand};
use responsibility::Authored;
use isolation::{local_reading, relation_keys, unrolled_lines};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Default)]
pub struct RelationReport {
    /// Connected groups of specifications that share a term.
    pub components: Vec<Vec<String>>,
    /// Specifications that share no term with any other. A person reviews these.
    pub isolated: Vec<SpecRef>,
    /// Terms that appear in exactly one specification.
    pub single_use_terms: Vec<String>,
}

/// A conformance example with its expected and observed results kept apart.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ExampleOutcome {
    pub name: String,
    pub kind: String,
    pub expected: String,
    pub observed: String,
    pub file: String,
    pub line: usize,
}

/// The moments of a trace when no other length is asked for.
pub(crate) const DEFAULT_TRACE_LENGTH: usize = 3;

/// The finite limits of the proof obligations. No decision limit means that
/// a prover runs each question to its end. The trace length is always
/// finite: an obligation is about the traces of that many moments.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct Bounds {
    /// The number of branching decisions that one question may take.
    pub decisions: Option<u64>,
    /// The number of moments of each trace that is examined.
    pub trace_length: usize,
    /// The number of individuals of each carrier that statements about
    /// individuals are read over.
    pub scope: usize,
}

impl Default for Bounds {
    fn default() -> Self {
        Self { decisions: None, trace_length: DEFAULT_TRACE_LENGTH, scope: trion_language::reading::DEFAULT_SCOPE }
    }
}

/// What an analysis is run with, apart from the specifications.
#[derive(Debug, Clone, Default)]
pub struct Options {
    /// The bounds of the proof obligations.
    pub bounds: Bounds,
    /// The revision of the analysed specification, when the caller knows it.
    pub subject_revision: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Analysis {
    pub diagnostics: Vec<Diagnostic>,
    /// The bounds of the proof obligations.
    pub bounds: Bounds,
    /// The revision of the analysed specification, when the caller knows it.
    pub subject_revision: Option<String>,
    pub vocabulary: BTreeMap<String, VocabEntry>,
    pub relations: RelationReport,
    pub model: Model,
    /// The opaque readings and the ungrounded statements: what the
    /// specification says without constraining anything.
    pub silence: trion_language::reading::Silence,
    /// How names resolve, for tools that ask what a word refers to.
    #[serde(skip)]
    pub lexicon: Lexicon,
}

impl Analysis {
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.severity == Severity::Error)
    }
}

/// Runs the examples that demonstrate the conversion: each example of
/// syntax and each example of a reading. They decide nothing: an example
/// that does not observe what it expects is an error of the conversion.
pub fn demonstrations(set: &SpecSet, bounds: Bounds) -> (Vec<ExampleOutcome>, Vec<Diagnostic>) {
    let mut diagnostics = Vec::new();
    let outcomes = blocks::run_examples_of(set, bounds, &|kind| matches!(kind, "syntax" | "reading"), &mut diagnostics);
    (outcomes, diagnostics)
}

/// The contracts of a model over a trace, with what the environment controls.
fn trace_of(set: &SpecSet, model: &Model, lex: &Lexicon, length: usize) -> (trion_language::reading::Trace, crate::analysis::environment::Control) {
    let mut trace = trion_language::reading::unroll(model, length);
    // What the environment does is not the system's to decide: a statement
    // about it is an assumption, and its event occurs only when it acts.
    let control = crate::analysis::environment::control(set, model, lex);
    for axiom in crate::analysis::environment::environment_events(model, &control) {
        trace.background.extend(trion_language::reading::at_every_moment(&axiom, length));
    }
    (trace, control)
}

/// A relation between statements. It is already applied in the formulas.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Relation {
    /// `overrides`, `default`, `narrows`, `refinement` or a relation that a
    /// statement about terms or individuals states.
    pub kind: String,
    /// The statement whose formula the relation changes: the one that
    /// yields, or the one that its details stand for.
    pub subject: SpecRef,
    /// The statements that the relation rests on.
    pub rests_on: Vec<SpecRef>,
}

/// The relations between the entries of a model: each yielding, and each
/// statement that its details stand for.
pub(crate) fn relations_of(model: &Model) -> Vec<Relation> {
    let mut relations: Vec<Relation> = model.priorities.iter().map(|p| Relation { kind: p.kind.clone(), subject: p.yields.clone(), rests_on: vec![p.to.clone()] }).collect();
    let mut detailed: BTreeMap<String, (SpecRef, Vec<SpecRef>)> = BTreeMap::new();
    for (detail, parents) in &model.refined {
        let Some(at) = model.constraints.iter().flat_map(|c| &c.refs).find(|r| r.id == *detail) else { continue };
        for parent in parents {
            detailed.entry(parent.id.clone()).or_insert_with(|| (parent.clone(), Vec::new())).1.push(at.clone());
        }
    }
    relations.extend(detailed.into_values().map(|(subject, rests_on)| Relation { kind: "refinement".to_string(), subject, rests_on }));
    // What a statement about terms or individuals says about other statements.
    relations.extend(model.applied.iter().map(|a| Relation { kind: a.kind.clone(), subject: a.subject.clone(), rests_on: a.rests_on.clone() }));
    relations
}

/// The contract of one statement as the document states it: one contract
/// for each simple sentence.
///
/// A contract is schematic in its parameters. A sentence about the
/// individuals of a declared type (`individuals user`) speaks about each of
/// them: its contract names the individual by the noun of its variable
/// (`user`) and lists the variable with its type. The instances of the
/// contract over a domain of N individuals are the bounded proof
/// obligation, as the moments of a trace are; they are no contracts of
/// their own. Without the declaration a type has one individual, named by
/// its noun, and the same formulas are its one instance: the declaration
/// changes the bound, not the reading.
///
/// A contract has time: `timing` is when it applies and when its response
/// must come (the activation, the deadlines and their origins, the orders,
/// `until`, the lifetime of an activation), as the reading of time states
/// it. The bounded proof obligation unrolls the contract with its timing
/// over the moments of a trace.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StatedContract {
    pub statement: SpecRef,
    /// By responsibility: `guarantee` for what the system answers for,
    /// `assumption` for a description of what the environment does,
    /// `permission`, `recommendation`, or `axiom` for what a term means.
    pub role: String,
    /// Each variable of the schematic contract with its type: the contract
    /// holds of each individual of the type.
    pub parameters: Vec<(String, String)>,
    /// Each variable that the response chooses, with its type: the contract
    /// holds where the response picks some individual of the type.
    pub chosen: Vec<(String, String)>,
    pub assume: Formula,
    pub guarantee: Formula,
    /// The temporal shape of the contract, one line for each part.
    pub timing: Vec<String>,
    /// The scope of an assumption: the guarantees that it is distributed to.
    pub scope: Option<Scope>,
}

/// The guarantees that an assumption sentence is distributed to.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Scope {
    /// Every guarantee of the document.
    Document,
    /// The guarantees of the shared condition block with this head, and of
    /// the blocks inside it.
    Block { head: String, file: String, line: usize },
}

/// The individuals of a binding with the noun that names each in a
/// schematic contract.
fn renaming(binding: &[(String, String)]) -> Vec<(String, String)> {
    let mut pairs: Vec<(String, String)> = binding.iter().map(|(variable, individual)| (individual.clone(), variable.clone())).collect();
    // `user#12` before `user#1`: a longer name is replaced first.
    pairs.sort_by_key(|(individual, _)| std::cmp::Reverse(individual.len()));
    pairs
}

fn renamed(text: &str, pairs: &[(String, String)]) -> String {
    pairs.iter().fold(text.to_string(), |text, (individual, variable)| text.replace(individual.as_str(), variable))
}

/// The formula of an instance as the schematic contract states it: each
/// individual named by its variable, and without the facts that the
/// individuals are of their types, which the parameters state.
/// A formula without the conjunctions of one formula, without `⊤` among
/// conjuncts and without `⊤ →`: the same formula, written once.
fn simplify(formula: Formula) -> Formula {
        match formula {
            Formula::And(items) => {
                let kept: Vec<Formula> = items.into_iter().map(simplify).filter(|f| *f != Formula::True).collect();
                match kept.len() {
                    0 => Formula::True,
                    1 => kept.into_iter().next().unwrap_or(Formula::True),
                    _ => Formula::And(kept),
                }
            }
            Formula::Or(items) => Formula::Or(items.into_iter().map(simplify).collect()),
            Formula::Not(inner) => Formula::Not(Box::new(simplify(*inner))),
            Formula::Implies(a, b) => match (simplify(*a), simplify(*b)) {
                (Formula::True, b) => b,
                (a, b) => Formula::Implies(Box::new(a), Box::new(b)),
            },
            other => other,
        }
}

fn schematic(formula: &Formula, pairs: &[(String, String)], kinds: &BTreeSet<(String, String)>) -> Formula {
    use trion_solver::Atom;
    fn walk(formula: &Formula, pairs: &[(String, String)], kinds: &BTreeSet<(String, String)>) -> Formula {
        let name = |text: &String| renamed(text, pairs);
        match formula {
            Formula::Atom(Atom::Rel { name: kind, args }) if args.len() == 1 && kinds.contains(&(kind.clone(), args[0].clone())) => Formula::True,
            Formula::Atom(atom) => Formula::Atom(match atom.clone() {
                Atom::Dom { attr, value } => Atom::Dom { attr: name(&attr), value: name(&value) },
                Atom::Val { attr, value } => Atom::Val { attr: name(&attr), value: name(&value) },
                Atom::Act { key } => Atom::Act { key: name(&key) },
                Atom::Forbid { key } => Atom::Forbid { key: name(&key) },
                Atom::Discouraged { key } => Atom::Discouraged { key: name(&key) },
                Atom::Event { key } => Atom::Event { key: name(&key) },
                Atom::Config { key } => Atom::Config { key: name(&key) },
                Atom::Role { subject, role } => Atom::Role { subject: name(&subject), role },
                Atom::Num { attr, unit, cmp, n } => Atom::Num { attr: name(&attr), unit, cmp, n },
                Atom::Lin { terms, unit, cmp, n } => Atom::Lin { terms: terms.iter().map(|(t, k)| (name(t), *k)).collect(), unit, cmp, n },
                Atom::Before { first, second } => Atom::Before { first: name(&first), second: name(&second) },
                Atom::Rel { name: relation, args } => Atom::Rel { name: relation, args: args.iter().map(name).collect() },
            }),
            Formula::Not(inner) => Formula::Not(Box::new(walk(inner, pairs, kinds))),
            Formula::And(items) => Formula::And(items.iter().map(|i| walk(i, pairs, kinds)).collect()),
            Formula::Or(items) => Formula::Or(items.iter().map(|i| walk(i, pairs, kinds)).collect()),
            Formula::Implies(a, b) => Formula::Implies(Box::new(walk(a, pairs, kinds)), Box::new(walk(b, pairs, kinds))),
            Formula::True => Formula::True,
        }
    }
    simplify(walk(formula, pairs, kinds))
}

/// Whether a formula names an individual of a bounded domain.
fn names_an_individual(formula: &Formula, individuals: &BTreeSet<String>) -> bool {
    let mut found = false;
    formula.atoms(true, &mut |atom, _| {
        let text = atom.to_string();
        found |= individuals.iter().any(|individual| text.contains(individual.as_str()));
    });
    found
}

/// The formula with each choice of one individual of a type, which the
/// reading writes as a disjunction over the individuals of the domain
/// (`(user(user#1) ∧ φ(user#1)) ∨ … ∨ (user(user#3) ∧ φ(user#3))`), written
/// as one formula over a variable that the response chooses: `φ(user)`. The
/// variables are added to `chosen` with their types; a type that is also a
/// parameter is chosen as `some <type>`.
fn chosen_individuals(formula: &Formula, kinds: &BTreeSet<(String, String)>, taken: &BTreeSet<String>, fixed: &BTreeSet<String>, chosen: &mut Vec<(String, String)>) -> Formula {
    use trion_solver::Atom;
    let recurse = |f: &Formula, chosen: &mut Vec<(String, String)>| chosen_individuals(f, kinds, taken, fixed, chosen);
    // Over a domain of one individual the choice among one is written
    // without its disjunction: `user(user#1) ∧ φ(user#1)`.
    if let Formula::And(parts) = formula {
        let choice = parts.iter().any(|p| matches!(p, Formula::Atom(Atom::Rel { name, args }) if args.len() == 1 && !fixed.contains(&args[0]) && kinds.contains(&(name.clone(), args[0].clone()))));
        if choice {
            return chosen_individuals(&Formula::Or(vec![formula.clone()]), kinds, taken, fixed, chosen);
        }
    }
    match formula {
        Formula::Or(items) if !items.is_empty() => {
            let mut carrier: Option<String> = None;
            let mut bodies: Vec<(String, Formula)> = Vec::new();
            for item in items {
                let parts = match item {
                    Formula::And(parts) => parts.clone(),
                    other => vec![other.clone()],
                };
                let typed: Vec<(String, String)> = parts.iter().filter_map(|p| match p {
                    Formula::Atom(Atom::Rel { name, args }) if args.len() == 1 && kinds.contains(&(name.clone(), args[0].clone())) => Some((name.clone(), args[0].clone())),
                    _ => None,
                }).collect();
                let [(kind, individual)] = typed.as_slice() else { break };
                if carrier.get_or_insert_with(|| kind.clone()) != kind {
                    break;
                }
                let rest: Vec<Formula> = parts.iter().filter(|p| !matches!(p, Formula::Atom(Atom::Rel { name, args }) if name == kind && args.len() == 1 && &args[0] == individual)).cloned().collect();
                bodies.push((individual.clone(), Formula::And(rest)));
            }
            if let (Some(kind), true) = (&carrier, bodies.len() == items.len()) {
                let variable = if taken.contains(kind) { format!("some {kind}") } else { kind.clone() };
                let named: Vec<Formula> = bodies.iter().map(|(individual, body)| schematic(body, &[(individual.clone(), variable.clone())], kinds)).collect();
                if named.windows(2).all(|pair| pair[0] == pair[1]) {
                    if !chosen.contains(&(variable.clone(), kind.clone())) {
                        chosen.push((variable, kind.clone()));
                    }
                    return recurse(&named[0], chosen);
                }
            }
            Formula::Or(items.iter().map(|i| recurse(i, chosen)).collect())
        }
        Formula::And(items) => Formula::And(items.iter().map(|i| recurse(i, chosen)).collect()),
        Formula::Not(inner) => Formula::Not(Box::new(recurse(inner, chosen))),
        Formula::Implies(a, b) => Formula::Implies(Box::new(recurse(a, chosen)), Box::new(recurse(b, chosen))),
        other => other.clone(),
    }
}

/// The contract of each statement of an analysed set, with the actors of
/// the system and of the environment. A description of the system is a
/// guarantee; a description of the environment is an assumption, whose
/// contract assumes the description and guarantees nothing
/// (`formal/Trion/Merging.lean`).
pub fn stated_contracts(set: &SpecSet, analysis: &Analysis) -> (Vec<StatedContract>, Control) {
    let model = &analysis.model;
    let control = crate::analysis::environment::control(set, model, &analysis.lexicon);
    let situated = responsibility::Situated::of(model, &control);
    let authored = Authored::new(set, &analysis.lexicon);
    let actors = environment::system_actors(model, &control, &|c| authored.is_description(c));
    // The statements of the set, by identifier: an instance is reported as
    // the statement that it is an instance of.
    let specs: BTreeMap<String, &trion_language::Spec> = set.packages.iter().flat_map(|p| p.documents.iter().flat_map(move |d| d.specs.iter().map(move |s| (if p.is_root { s.display_id() } else { format!("{}::{}", p.name, s.display_id()) }, s)))).collect();
    let at = |id: &str, fallback: &SpecRef| specs.get(id).map_or_else(|| fallback.clone(), |s| SpecRef { id: id.to_string(), file: s.file.clone(), line: s.line, text: s.sentence.source.clone() });
    // One instance of each statement over individuals stands for the
    // statement: the first whose individuals are all different, so that no
    // two variables are named alike.
    let mut instances: BTreeMap<String, (String, Vec<(String, String)>)> = BTreeMap::new();
    let mut chosen: BTreeMap<String, String> = BTreeMap::new();
    for instance in model.individuals.iter().flat_map(|i| &i.instances) {
        instances.insert(instance.instance.clone(), (instance.statement.clone(), instance.binding.clone()));
        let distinct = instance.binding.iter().map(|(_, individual)| individual).collect::<BTreeSet<_>>().len() == instance.binding.len();
        match chosen.get(&instance.statement) {
            Some(_) if !distinct => {}
            Some(current) if instances.get(current).is_some_and(|(_, b)| b.iter().map(|(_, i)| i).collect::<BTreeSet<_>>().len() == b.len()) => {}
            _ => {
                chosen.insert(instance.statement.clone(), instance.instance.clone());
            }
        }
    }
    // Each individual of the bounded domain with its type.
    let mut kinds: BTreeSet<(String, String)> = instances.values().flat_map(|(_, binding)| binding.iter().map(|(_, individual)| (individual.split('#').next().unwrap_or(individual).to_string(), individual.clone()))).collect();
    for atom in model.individuals.iter().flat_map(|i| &i.atoms) {
        if let trion_language::reading::Fact::Kind { kind, subject } = &atom.fact {
            kinds.insert((kind.clone(), subject.clone()));
        }
    }
    let individuals: BTreeSet<String> = kinds.iter().map(|(_, individual)| individual.clone()).collect();
    let mut out = Vec::new();
    for c in &model.constraints {
        let Some(statement) = c.refs.first().cloned() else { continue };
        // An instance other than the one that stands for its statement is
        // part of the bounded obligation, and no contract.
        let (statement, pairs, parameters) = match instances.get(&statement.id) {
            Some((of, binding)) => {
                if chosen.get(of) != Some(&statement.id) {
                    continue;
                }
                let parameters = binding.iter().map(|(variable, individual)| (variable.clone(), individual.split('#').next().unwrap_or(individual).to_string())).collect();
                (at(of, &statement), renaming(binding), parameters)
            }
            None => {
                // What a statement says of the individuals of the bounded
                // domain, beside its contract, is the bounded instance of the
                // same sentence: part of the obligation, and no contract.
                if c.kind.is_vocabulary() && names_an_individual(&c.formula(), &individuals) {
                    continue;
                }
                (statement, Vec::new(), Vec::new())
            }
        };
        let timing: Vec<String> = model.temporal.iter().find(|o| c.refs.first().is_some_and(|r| r.id == o.statement.id)).map(|o| o.lines().iter().map(|line| renamed(line, &pairs)).collect()).unwrap_or_default();
        let (source, application_scope) = authored.owner(&statement)
            .map_or((None, None), |(spec, doc)| (Some(spec), doc.application_scope.as_ref()));
        let scope = source.or_else(|| specs.get(&statement.id).copied())
            .and_then(|s| Some(Scope::Block {
                head: s.scopes.last()?.clone(),
                file: s.file.clone(),
                line: *s.scope_lines.last()?,
            }))
            .or_else(|| application_scope.map(|at| Scope::Block { head: at.text.clone(), file: at.file.clone(), line: at.line }));
        let (role, assume, guarantee) = match c.kind {
            ConstraintKind::Refinement => continue,
            // The form that a bound role requires of the system.
            kind if kind.is_form() => ("form", c.assume.clone(), c.guarantee.clone()),
            kind if kind.is_vocabulary() => ("axiom", Formula::True, c.formula()),
            // A requirement of what only the environment does is an assumption .
            ConstraintKind::Spec | ConstraintKind::Permission if !authored.is_description(c) && environment::of_environment(c, &actors) => ("assumption", c.formula(), Formula::True),
            ConstraintKind::Permission => ("permission", c.assume.clone(), c.guarantee.clone()),
            _ if authored.is_recommendation(c) => ("recommendation", c.assume.clone(), c.guarantee.clone()),
            _ if authored.is_description(c) && !situated.describes_system(model, c) => ("assumption", c.formula(), Formula::True),
            _ => ("guarantee", c.assume.clone(), c.guarantee.clone()),
        };
        let (assume, guarantee) = if matches!(role, "guarantee" | "recommendation" | "permission") {
            situated.contract(assume, guarantee, &model.configured)
        } else {
            (assume, guarantee)
        };
        // An individual that the response chooses is a variable of its own.
        let taken: BTreeSet<String> = parameters.iter().map(|(_, kind): &(String, String)| kind.clone()).collect();
        // The individuals that the parameters name: each is no choice.
        let fixed: BTreeSet<String> = pairs.iter().map(|(individual, _)| individual.clone()).collect();
        let mut chosen = Vec::new();
        let schematic_instances = !individuals.is_empty() && !model.domain_contracts.contains_key(&statement.id);
        let (assume, guarantee) = if !schematic_instances { (assume, guarantee) } else { (chosen_individuals(&assume, &kinds, &taken, &fixed, &mut chosen), chosen_individuals(&guarantee, &kinds, &taken, &fixed, &mut chosen)) };
        let (assume, guarantee) = if !schematic_instances { (simplify(assume), simplify(guarantee)) } else { (schematic(&assume, &pairs, &kinds), schematic(&guarantee, &pairs, &kinds)) };
        let timing: Vec<String> = timing.iter().map(|line| renamed(line, &chosen.iter().flat_map(|(variable, kind)| kinds.iter().filter(move |(k, _)| k == kind).map(move |(_, individual)| (individual.clone(), variable.clone()))).collect::<Vec<_>>())).collect();
        // The same line for each individual that the response may choose is one line.
        let timing: Vec<String> = timing.into_iter().fold(Vec::new(), |mut kept, line| {
            if !kept.contains(&line) {
                kept.push(line);
            }
            kept
        });
        let scope = if role == "assumption" { scope.or(Some(Scope::Document)) } else { None };
        let timing = if kind_is_axiom(c) { Vec::new() } else { timing };
        out.push(StatedContract { statement, role: role.to_string(), parameters, chosen, assume, guarantee, timing, scope });
    }
    (out, control)
}

/// A contract about what a term means has no time of its own.
fn kind_is_axiom(c: &trion_language::reading::Constraint) -> bool {
    c.kind.is_vocabulary() || c.kind.is_axiom()
}

/// The actors that are taken to be the system where the document declares
/// none: the actors whose actions its normative statements speak about.
/// `None` when the document declares the system.
pub fn inferred_system(set: &SpecSet, analysis: &Analysis) -> Option<std::collections::BTreeSet<String>> {
    let control = crate::analysis::environment::control(set, &analysis.model, &analysis.lexicon);
    let authored = Authored::new(set, &analysis.lexicon);
    control.declared_system.is_empty().then(|| environment::undeclared_system(&analysis.model, &control, &|c| authored.is_description(c)))
}

/// The proof obligations of an analysed set at a trace of `length`
/// moments: the formulas of each property that a correct specification
/// has. Nothing is decided.
pub fn proof_obligations(set: &SpecSet, analysis: &Analysis, length: usize) -> ProofObligations {
    references::build(set, &analysis.model, &analysis.lexicon, length, analysis.bounds.scope, analysis.bounds.decisions)
}

/// Reads a specification set: the vocabulary, the model, the relations and
/// the diagnostics of the language. Nothing is decided.
pub fn analyze(set: &SpecSet, options: &Options) -> Analysis {
    let bounds = options.bounds;
    let mut diagnostics = Vec::new();
    let lex = Lexicon::checked(set, &mut diagnostics);
    let (vocabulary, vocabulary_diagnostics) = build_table(set, &lex);
    diagnostics.extend(vocabulary_diagnostics);
    structure::check_identifiers(set, &mut diagnostics);
    diagnostics.extend(trion_language::reading::check_refinements(set));
    let model = trion_language::reading::compile(set, &lex, bounds.scope);
    if model.individuals.is_some() {
        let control = environment::control(set, &model, &lex);
        diagnostics.extend(control.conflicting_carriers.into_iter().map(|(carrier, refs)| {
            Diagnostic::error("vocabulary-kind-conflict", format!("the carrier `{carrier}` has both system and environment responsibility for its individual actors"), refs)
        }));
    }
    diagnostics.extend(trion_language::reading::check_priorities(set, &model));
    structure::find_unsupported(set, &model, &mut diagnostics);
    // What the language requires of the form of the statements: the
    // extensions, the units, the required forms, the closed domains and the
    // temporal scopes.
    structure::check_model(set, &model, &lex, &mut diagnostics);
    diagnostics.extend(trion_language::reading::temporal_diagnostics(&model.temporal));
    let relations = structure::relate(set, &lex);
    let silence = trion_language::reading::silence(set, &model, &vocabulary, &lex);
    Analysis { diagnostics, bounds, subject_revision: options.subject_revision.clone(), vocabulary, relations, model, silence, lexicon: lex }
}
