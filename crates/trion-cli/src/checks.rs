//! The checks of a verification that stand apart from the analysis: what
//! `trion-checker` finds of the package.
//!
//! Each scenario of the package is one concrete behaviour. It is judged
//! twice: by the reference evaluator, which reads the typed meaning of the
//! statements and builds no formula, and by the formulas that the analysis
//! decides. The two judgements are one claim (`scenario_satisfiable`) when
//! they agree; when they differ, the reading and the meaning differ, and
//! that is an error of trion and no finding about the package.

use crate::project::Project;
use serde::Serialize;
use trion_checker::{scenario, Generated, Violation};
use trion_language::reading::{Constraint, ConstraintKind, Model};
use trion_language::{Diagnostic, SpecRef};
use trion_solver::{Atom, Formula};
use trion_verification::{Analysis, AnalysisRange, Claim, Verdict};

/// How one scenario was judged.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ScenarioOutcome {
    pub name: String,
    /// `allowed` or `forbidden`: what the author expects.
    pub expect: String,
    /// `allowed`, `forbidden` or `undecided`: what the reference evaluator found.
    pub reference: String,
    /// `allowed`, `forbidden`, `unknown` or `not comparable`: what the formulas say.
    pub generated: String,
    /// The statements that the behaviour fails, with the instance and the moment.
    pub violations: Vec<Violation>,
    /// The statements with a part that the reference evaluator does not evaluate.
    pub unevaluated: Vec<(String, String)>,
    /// The statements whose share has no value in the behaviour: they are
    /// neither met nor failed.
    pub undefined: Vec<(String, String)>,
    pub verdict: Verdict,
}

/// What the check of the records of the reading covered.
#[derive(Debug, Clone, Default, Serialize)]
pub(crate) struct Derivations {
    /// The typed statements whose record was derived again and agrees.
    pub statements: usize,
    /// The instances whose contract is the one that the meaning requires.
    pub contracts: usize,
    /// The instances whose contract holds a form that the check does not
    /// derive, each with the form: they rest on the reading alone.
    pub not_derived: Vec<(String, String)>,
    /// The typed statements and the instances of the reading.
    pub of_statements: usize,
    pub of_instances: usize,
    /// The statements about individuals whose tree was read again from
    /// their text by a grammar apart from the parser and agrees, and the
    /// number of those statements.
    pub texts: usize,
    pub of_texts: usize,
    /// The statements whose text holds a form outside that grammar, each
    /// with the form: their tree rests on the parser alone.
    pub not_read: Vec<(String, String)>,
}

/// The behaviour that stands for the claim that a behaviour keeps every
/// contract, and what the reference evaluator says of it.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct WitnessOutcome {
    /// `accepted`, `refused`, `not evaluated`, `none` or `unknown`.
    pub state: String,
    /// What the state rests on, in one sentence.
    pub what: String,
    /// The behaviour, when one was found.
    pub behaviour: Option<trion_checker::World>,
}

/// The behaviours next to the scenarios, and how both judgements stand on them.
#[derive(Debug, Clone, Default, Serialize)]
pub(crate) struct Variations {
    /// The behaviours that were made: each differs from a scenario in one fact.
    pub behaviours: usize,
    /// Those that the reference evaluator and the formulas judge alike.
    pub agreed: usize,
    /// Those that one of the two does not decide, each with the scenario and the change.
    pub undecided: Vec<(String, String)>,
    /// The situations of the scenarios that the statements without
    /// normative force allow: a scenario without the occurrences that the
    /// statements require, forbid or permit.
    pub situations: usize,
    /// Those to which the formulas give a response that the reference evaluator accepts.
    pub answered: usize,
    /// The scenarios whose situation has no response within its moments and one more.
    pub unanswered: Vec<String>,
    /// The scenarios whose situation was not decided.
    pub open: Vec<String>,
    /// The statements with a condition of a moment, one by one and two by
    /// two, that were asked for a situation in which they apply together.
    pub together: usize,
    /// Those that the statements without normative force keep apart.
    pub apart: usize,
    /// Those with a situation to which the formulas give a response that
    /// the reference evaluator accepts.
    pub together_answered: usize,
    /// Those whose situation has no response, each with its statements.
    pub together_unanswered: Vec<String>,
    /// Those that were not decided.
    pub together_open: Vec<String>,
}

/// What the checks found.
#[derive(Debug, Clone, Default, Serialize)]
pub(crate) struct Checked {
    pub diagnostics: Vec<Diagnostic>,
    pub derivations: Derivations,
    /// The concrete behaviour behind `contract_sat`, in a package that declares its individuals.
    pub witness: Option<WitnessOutcome>,
    /// The variations of the scenarios, when the properties of the reading are examined.
    pub variations: Option<Variations>,
    pub scenarios: Vec<ScenarioOutcome>,
    /// `true` when the package holds something that these checks examine.
    pub asked: bool,
}

/// The faults of the reading that `TRION_FAULT` seeds, so that a test can
/// show that the comparison finds them. Each breaks the formulas of the
/// reading and leaves the meaning of the statements as it is:
///
/// - `reading-binds-another`: a response speaks about another individual
///   than the one that its condition names;
/// - `reading-drops-negation`: a prohibition forbids nothing;
/// - `reading-moves-boundary`: a deadline ends one second later;
/// - `reading-swaps-quantifier`: a statement holds for one individual
///   and not for each;
/// - `reading-loosens-share`: the bound of a share is half of what the
///   statement says;
/// - `reading-chooses-any`: a response that chooses an individual may
///   choose one that is not of the named kind or not in the named relation.
///
/// A fault of a contract is seeded in the counted instances of a statement
/// that bounds a share as well: they are formulas of the reading too.
pub(crate) const FAULTS: [&str; 6] = ["reading-binds-another", "reading-drops-negation", "reading-moves-boundary", "reading-swaps-quantifier", "reading-loosens-share", "reading-chooses-any"];

/// The faults of the record of a reading: the formulas are left as they
/// are, and the record says something else than the statement.
///
/// - `record-binds-another`: a response of the record names another variable;
/// - `record-changes-unit`: a deadline of the record is a thousand times longer;
/// - `record-names-no-rule`: a step of the record names a rule that the version does not hold;
/// - `record-drops-instance`: an instance of a statement is missing.
pub(crate) const RECORD_FAULTS: [&str; 4] = ["record-binds-another", "record-changes-unit", "record-names-no-rule", "record-drops-instance"];

/// The model with the seeded fault of the reading, when one is seeded.
fn faulted(model: &Model) -> Option<Model> {
    use trion_language::reading::typed::{Response, Term};
    let fault = std::env::var("TRION_FAULT").ok().filter(|name| FAULTS.contains(&name.as_str()) || RECORD_FAULTS.contains(&name.as_str()))?;
    let mut model = model.clone();
    if let (true, Some(individuals)) = (RECORD_FAULTS.contains(&fault.as_str()), model.individuals.as_mut()) {
        match fault.as_str() {
            "record-binds-another" => {
                for meaning in individuals.meanings.iter_mut().filter(|m| m.variables.len() > 1) {
                    for response in &mut meaning.responses {
                        if let Response::Action { pattern, .. } = response {
                            if let Some(Term::Variable(id)) = &mut pattern.object {
                                *id = (*id + 1) % meaning.variables.len() as u32;
                            }
                        }
                    }
                }
            }
            "record-changes-unit" => {
                for response in individuals.meanings.iter_mut().flat_map(|m| &mut m.responses) {
                    if let Response::Action { deadline: Some(deadline), .. } = response {
                        deadline.thousandths *= 1000;
                    }
                }
            }
            "record-names-no-rule" => {
                if let Some(step) = individuals.meanings.iter_mut().flat_map(|m| &mut m.steps).next() {
                    step.rule = "variable-by-guess";
                }
            }
            _ => {
                individuals.instances.pop();
            }
        }
        return Some(model);
    }
    let contracts = |c: &Constraint| matches!(c.kind, ConstraintKind::Spec | ConstraintKind::Permission);
    // The contracts of the statements, and the counted instances of the shares.
    fn each<'a>(model: &'a mut Model, contracts: &'a dyn Fn(&Constraint) -> bool) -> impl Iterator<Item = &'a mut Constraint> {
        model.constraints.iter_mut().filter(move |c| contracts(c)).chain(model.counted.iter_mut().map(|counted| &mut counted.constraint))
    }
    match fault.as_str() {
        "reading-binds-another" => {
            let other = |name: &str| if name.contains("#1") { name.replace("#1", "#2") } else { name.replace("#2", "#1") };
            for c in each(&mut model, &contracts) {
                c.guarantee = c.guarantee.clone().map_atoms(&|atom| match atom {
                    Atom::Act { key } => Atom::Act { key: other(&key) },
                    Atom::Forbid { key } => Atom::Forbid { key: other(&key) },
                    atom => atom,
                });
            }
        }
        "reading-drops-negation" => {
            fn without(formula: Formula) -> Formula {
                match formula {
                    Formula::Not(_) => Formula::True,
                    Formula::And(items) => Formula::And(items.into_iter().map(without).collect()),
                    other => other,
                }
            }
            for c in each(&mut model, &contracts) {
                c.guarantee = without(c.guarantee.clone());
            }
        }
        "reading-moves-boundary" => {
            for c in each(&mut model, &contracts) {
                c.guarantee = c.guarantee.clone().map_atoms(&|atom| match atom {
                    Atom::Num { attr, unit, cmp, n } if unit == "ms" => Atom::Num { attr, unit, cmp, n: n + 1000 * trion_solver::NUMERIC_SCALE },
                    atom => atom,
                });
            }
        }
        "reading-chooses-any" => {
            // What makes an individual one that may be chosen stands in the guarantee as kinds and relations.
            fn any(formula: Formula) -> Formula {
                match formula {
                    Formula::Atom(Atom::Rel { .. }) => Formula::True,
                    Formula::And(items) => Formula::And(items.into_iter().map(any).collect()),
                    Formula::Or(items) => Formula::Or(items.into_iter().map(any).collect()),
                    other => other,
                }
            }
            for c in each(&mut model, &contracts) {
                c.guarantee = any(c.guarantee.clone());
            }
        }
        "reading-loosens-share" => {
            for c in model.constraints.iter_mut().filter(|c| contracts(c)) {
                c.guarantee = c.guarantee.clone().map_atoms(&|atom| match atom {
                    Atom::Num { attr, unit, cmp, n } if unit == "percent" => Atom::Num { attr, unit, cmp, n: n / 2 },
                    atom => atom,
                });
            }
        }
        _ => {
            let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
            let mut first = |c: &Constraint, counts: bool| {
                let Some(id) = c.refs.first().map(|r| r.id.clone()) else { return true };
                match id.split_once('/') {
                    Some((statement, _)) if counts => seen.insert(statement.to_string()),
                    _ => true,
                }
            };
            model.constraints.retain(|c| first(c, contracts(c)));
            model.counted.retain(|counted| first(&counted.constraint, true));
        }
    }
    Some(model)
}

/// The most variations that are made of one scenario.
const VARIATIONS: usize = 24;

/// Judges the behaviours next to each scenario: each differs from the
/// scenario in one fact. The reference evaluator and the formulas of the
/// reading agree on each of them, or the reading differs from the meaning
/// on a behaviour that no scenario states.
pub(crate) fn vary(project: &Project, analysis: &Analysis) -> (Variations, Vec<Diagnostic>) {
    let mut found = Variations::default();
    let mut diagnostics = Vec::new();
    let seeded = faulted(&analysis.model);
    let read = seeded.as_ref().unwrap_or(&analysis.model);
    let Some(individuals) = &analysis.model.individuals else { return (found, diagnostics) };
    // What the statements require, forbid or permit of something that
    // they name: the occurrences that a response is made of.
    use trion_language::reading::typed::{Force, Response, Term};
    // The actor is a named thing, or any individual where the statement speaks of a variable.
    let responses: Vec<(Option<String>, String, Option<String>)> = individuals
        .meanings
        .iter()
        .filter(|m| m.force != Force::Description)
        .flat_map(|m| &m.responses)
        .filter_map(|response| match response {
            Response::Action { pattern, .. } => Some((if let Term::Constant(actor) = &pattern.actor { Some(actor.clone()) } else { None }, pattern.verb.clone(), pattern.particle.clone())),
            _ => None,
        })
        .collect();
    let is_response = |occurrence: &trion_checker::Occurrence| responses.iter().any(|(actor, verb, particle)| actor.as_ref().is_none_or(|actor| *actor == occurrence.actor) && *verb == occurrence.verb && *particle == occurrence.particle);
    let stated = trion_checker::Stated::of(read).expect("a model over individuals");
    // One more moment after the situation, within the shortest stated deadline.
    let later = individuals.meanings.iter().flat_map(|m| &m.responses).filter_map(|response| if let Response::Action { deadline: Some(deadline), .. } = response { Some(deadline.thousandths / 1000) } else { None }).filter(|ms| *ms > 0).min().unwrap_or(1000);
    for doc in project.set.packages.iter().filter(|p| p.is_root).flat_map(|p| &p.documents) {
        let lex = analysis.lexicon.in_document(doc);
        for block in doc.scenarios.iter().filter(|block| !block.malformed) {
            let Ok(world) = scenario::world(block, individuals, &lex) else { continue };
            // The situation of the scenario: what happens in it apart from
            // what the statements require, forbid or permit. The formulas
            // give a response to it, and the reference evaluator judges the
            // behaviour with that response.
            let situation = trion_checker::situation(&world, &is_response, later);
            match trion_checker::respond(&stated, &situation, &is_response) {
                trion_checker::Responded::Excluded => {}
                trion_checker::Responded::Response { evaluation, .. } => {
                    found.situations += 1;
                    match (evaluation.accepted(), evaluation.violations.first()) {
                        (Some(false), Some(violation)) => {
                            let at = SpecRef { id: format!("scenario {}", block.name), file: block.file.clone(), line: block.line, text: format!("scenario {}", block.name) };
                            diagnostics.push(Diagnostic::error(
                                "witness-refused",
                                format!("the formulas of the reading accept a response to the situation of the scenario, and the behaviour with that response fails [{}]{}: {}; the reading of a statement differs from its meaning, and no result about the package is established", violation.statement, violation.moment.map_or(String::new(), |m| format!(" at moment {m}")), violation.what),
                                vec![at],
                            ));
                        }
                        (Some(true), _) => found.answered += 1,
                        _ => found.open.push(block.name.clone()),
                    }
                }
                trion_checker::Responded::None => {
                    found.situations += 1;
                    found.unanswered.push(block.name.clone());
                }
                trion_checker::Responded::Unknown => {
                    found.situations += 1;
                    found.open.push(block.name.clone());
                }
            }
            for variation in trion_checker::variations(&world, individuals, VARIATIONS) {
                found.behaviours += 1;
                let comparison = stated.compare(&variation.world);
                match comparison.agree() {
                    Some(true) => found.agreed += 1,
                    Some(false) => {
                        let at = SpecRef { id: format!("scenario {}", block.name), file: block.file.clone(), line: block.line, text: format!("scenario {}", block.name) };
                        let said = |generated: &Generated| if *generated == Generated::Accepted { "allowed" } else { "forbidden" };
                        diagnostics.push(Diagnostic::error(
                            "scenario-differs",
                            format!("on the behaviour of the scenario {}, the reference evaluator finds the behaviour {} and the formulas of the reading find it {}: the reading of a statement differs from its meaning, and no result about the package is established", variation.what, word(comparison.reference.accepted()), said(&comparison.generated)),
                            vec![at],
                        ));
                    }
                    None => found.undecided.push((block.name.clone(), variation.what.clone())),
                }
            }
        }
    }
    // The situations that the statements themselves give: each statement
    // with a condition, and each two of them, applying at one moment.
    let claimed = analysis.claims.claims.iter().any(|claim| claim.claim == "situation_total" && claim.verdict == Verdict::Proved);
    for (statements, outcome) in trion_checker::together(&stated, &is_response, later, TOGETHER) {
        found.together += 1;
        let names = statements.iter().map(|statement| format!("[{statement}]")).collect::<Vec<_>>().join(" and ");
        let at = || individuals.meanings.iter().find(|m| statements.first() == Some(&m.statement)).map(|m| SpecRef { id: m.statement.clone(), file: String::new(), line: 0, text: m.source.clone() }).into_iter().collect::<Vec<_>>();
        match outcome {
            trion_checker::Together::Apart => found.apart += 1,
            trion_checker::Together::Unknown => found.together_open.push(names),
            trion_checker::Together::Situation { responded, .. } => match responded {
                trion_checker::Responded::Response { evaluation, .. } => match (evaluation.violations.first(), evaluation.accepted()) {
                    (Some(violation), _) => diagnostics.push(Diagnostic::error(
                        "witness-refused",
                        format!("the formulas of the reading accept a response to a situation in which {names} apply, and the behaviour with that response fails [{}]{}: {}; the reading of a statement differs from its meaning, and no result about the package is established", violation.statement, violation.moment.map_or(String::new(), |m| format!(" at moment {m}")), violation.what),
                        at(),
                    )),
                    (None, None) => found.together_open.push(names),
                    (None, _) => found.together_answered += 1,
                },
                trion_checker::Responded::Excluded => diagnostics.push(Diagnostic::error(
                    "witness-refused",
                    format!("the formulas of the statements without normative force allow a situation in which {names} apply, and the reference evaluator finds that these statements exclude it: the reading of a statement differs from its meaning, and no result about the package is established"),
                    at(),
                )),
                trion_checker::Responded::None => {
                    if claimed {
                        diagnostics.push(Diagnostic::error(
                            "witness-refused",
                            format!("the statements without normative force allow a situation in which {names} apply, and the formulas of the reading give no response to it: the claim that each situation has a response is not confirmed, and no result about the package is established"),
                            at(),
                        ));
                    }
                    found.together_unanswered.push(names);
                }
                trion_checker::Responded::Unknown => found.together_open.push(names),
            },
        }
    }
    (found, diagnostics)
}

/// The most sets of statements that are asked for a situation in which they apply together.
const TOGETHER: usize = 120;

fn word(accepted: Option<bool>) -> &'static str {
    match accepted {
        Some(true) => "allowed",
        Some(false) => "forbidden",
        None => "undecided",
    }
}

/// Judges each scenario of the root package and states one claim for each.
pub(crate) fn run(project: &Project, analysis: &mut Analysis) -> Checked {
    let mut out = Checked { asked: analysis.model.individuals.is_some(), ..Default::default() };
    let mut claims: Vec<Claim> = Vec::new();
    let template = analysis.claims.claims.first().map(|c| c.range.clone());
    let seeded = faulted(&analysis.model);
    let read = seeded.as_ref().unwrap_or(&analysis.model);
    // The record of each reading, the instances and their contracts,
    // against the statements of the package.
    if let Some(individuals) = &read.individuals {
        let derived = trion_checker::derive::check(&project.set, read, &analysis.lexicon);
        for refusal in &derived.refusals {
            out.diagnostics.push(Diagnostic::error("derivation-refused", format!("the check of the reading refuses `{}`: {}", refusal.subject, refusal.what), Vec::new()));
        }
        out.derivations = Derivations { statements: derived.statements, contracts: derived.contracts, not_derived: derived.not_derived, of_statements: individuals.meanings.len(), of_instances: individuals.instances.len(), texts: derived.texts, of_texts: derived.of_texts, not_read: derived.not_read };
    }
    // The model behind `contract_sat`, as a concrete behaviour that the
    // reference evaluator judges.
    let kept = analysis.claims.of("contract_sat").is_some_and(|claim| claim.verdict == Verdict::Proved);
    if let (true, Some(individuals)) = (kept, &read.individuals) {
        let moments = analysis.consistency.bounds.trace_length;
        let (state, what, behaviour) = match trion_checker::witness(read, individuals, moments) {
            trion_checker::Witnessed::Behaviour { world, spacing, applies, evaluation } => {
                let shape = format!("a complete behaviour of {} moments, {spacing} ms apart, with {} occurrences, in which {}", world.moments.len(), world.moments.iter().map(|m| m.occurrences.len()).sum::<usize>(), if applies { "a statement with a condition applies at the first moment" } else { "no condition is required to hold" });
                match (evaluation.accepted(), evaluation.violations.first(), evaluation.unevaluated.first()) {
                    (Some(true), _, _) => ("accepted", format!("{shape}: the formulas of the reading accept it, and the reference evaluator finds that it fails no statement"), Some(world)),
                    (Some(false), Some(violation), _) => {
                        out.diagnostics.push(Diagnostic::error(
                            "witness-refused",
                            format!("the formulas of the reading accept {shape}, and it fails [{}]{}: {}; the reading of a statement differs from its meaning, and no result about the package is established", violation.statement, violation.moment.map_or(String::new(), |m| format!(" at moment {m}")), violation.what),
                            Vec::new(),
                        ));
                        ("refused", format!("{shape}: the formulas of the reading accept it, and it fails [{}]: {}", violation.statement, violation.what), Some(world))
                    }
                    (_, _, Some((statement, part))) => ("not evaluated", format!("{shape}: [{statement}] holds {part}, which the reference evaluator does not evaluate, so the behaviour is not confirmed"), Some(world)),
                    _ => ("not evaluated", format!("{shape}: the reference evaluator does not judge it"), Some(world)),
                }
            }
            trion_checker::Witnessed::None { tried } => ("none", format!("no complete behaviour of {moments} moments keeps every contract with the moments {} ms apart: the model of the claim rests on what happens after the trace, and no concrete behaviour confirms it", tried.iter().map(i64::to_string).collect::<Vec<_>>().join(", ")), None),
            trion_checker::Witnessed::Unknown => ("unknown", "the search for a complete behaviour was not decided within the budget".to_string(), None),
        };
        if let Some(claim) = analysis.claims.claims.iter_mut().find(|claim| claim.claim == "contract_sat") {
            claim.evidence.push(format!("as a concrete behaviour ({state}): {what}"));
            if state == "refused" {
                claim.verdict = Verdict::Error;
                claim.reason = Some("reading_differs_from_meaning".to_string());
            }
        }
        out.witness = Some(WitnessOutcome { state: state.to_string(), what, behaviour });
    }
    let stated = trion_checker::Stated::of(read);
    for doc in project.set.packages.iter().filter(|p| p.is_root).flat_map(|p| &p.documents) {
        let lex = analysis.lexicon.in_document(doc);
        for block in &doc.scenarios {
            out.asked = true;
            let at = SpecRef { id: format!("scenario {}", block.name), file: block.file.clone(), line: block.line, text: format!("scenario {}", block.name) };
            let mut outcome = ScenarioOutcome { name: block.name.clone(), expect: block.expect.clone(), reference: "undecided".to_string(), generated: "unknown".to_string(), violations: Vec::new(), unevaluated: Vec::new(), undefined: Vec::new(), verdict: Verdict::Invalid };
            let mut reason = None;
            let mut moments = 0;
            let read_block = if block.malformed { Some(Err(Vec::new())) } else { analysis.model.individuals.as_ref().map(|individuals| scenario::world(block, individuals, &lex)) };
            match read_block {
                None => {
                    outcome.verdict = Verdict::Unsupported;
                    reason = Some("no_declared_individuals".to_string());
                    out.diagnostics.push(Diagnostic::error("scenario-unsupported", "a scenario is judged over individuals of declared types, and the package declares none: declare them, as in `individuals user, room`", vec![at.clone()]));
                }
                Some(Err(problems)) => {
                    reason = Some("malformed_block".to_string());
                    for problem in problems {
                        out.diagnostics.push(Diagnostic::error("scenario-invalid", problem.what, vec![SpecRef { line: problem.line, ..at.clone() }]));
                    }
                }
                Some(Ok(world)) => {
                    moments = world.closed().moments.len();
                    let comparison = stated.as_ref().expect("a model over individuals").compare(&world);
                    outcome.reference = word(comparison.reference.accepted()).to_string();
                    outcome.violations = comparison.reference.violations.clone();
                    outcome.unevaluated = comparison.reference.unevaluated.clone();
                    outcome.undefined = comparison.reference.undefined.clone();
                    outcome.generated = match &comparison.generated {
                        Generated::Accepted => "allowed".to_string(),
                        Generated::Rejected => "forbidden".to_string(),
                        Generated::Unknown => "unknown".to_string(),
                        Generated::NotComparable { .. } => "not comparable".to_string(),
                    };
                    match (comparison.agree(), comparison.reference.accepted()) {
                        (Some(true), Some(accepted)) => {
                            outcome.verdict = if accepted { Verdict::Proved } else { Verdict::Refuted };
                            // `expect undefined`: the behaviour fails nothing, and a share has no value in it.
                            let met = match block.expect.as_str() {
                                "undefined" => accepted && !outcome.undefined.is_empty(),
                                expected => expected == word(Some(accepted)),
                            };
                            if !block.expect.is_empty() && !met {
                                let why = match outcome.violations.first() {
                                    Some(v) => format!("it fails [{}]{}: {}", v.statement, v.moment.map_or(String::new(), |m| format!(" at moment {m}")), v.what),
                                    None if outcome.undefined.is_empty() => "it fails no statement, and each share has a value in it".to_string(),
                                    None => "it fails no statement".to_string(),
                                };
                                out.diagnostics.push(Diagnostic::error("scenario-failed", format!("the scenario is expected to be {} and is {}: {why}", block.expect, word(Some(accepted))), vec![at.clone()]));
                            }
                        }
                        (Some(false), _) => {
                            outcome.verdict = Verdict::Error;
                            reason = Some("reading_differs_from_meaning".to_string());
                            out.diagnostics.push(Diagnostic::error("scenario-differs", format!("the reference evaluator finds the behaviour {} and the formulas of the reading find it {}: the reading of a statement differs from its meaning, and no result about the package is established", outcome.reference, outcome.generated), vec![at.clone()]));
                        }
                        _ => {
                            outcome.verdict = Verdict::Unsupported;
                            let why = match (&comparison.generated, outcome.unevaluated.first()) {
                                (Generated::NotComparable { atoms }, _) => {
                                    reason = Some("atoms_without_a_fact".to_string());
                                    format!("the formulas hold atoms that the behaviour does not fix ({}): a statement of the package is not read over individuals", atoms.iter().take(3).cloned().collect::<Vec<_>>().join(", "))
                                }
                                (_, Some((statement, part))) => {
                                    reason = Some("not_evaluated".to_string());
                                    format!("[{statement}] holds {part}, which the reference evaluator does not evaluate")
                                }
                                _ => {
                                    reason = Some("resource_limit".to_string());
                                    "the formulas were not decided within the budget".to_string()
                                }
                            };
                            out.diagnostics.push(Diagnostic::error("scenario-unsupported", format!("the scenario is not judged: {why}"), vec![at.clone()]));
                        }
                    }
                }
            }
            let range = template.clone().map(|range| AnalysisRange { moments, individuals: analysis.model.instance_scope, ..range }).unwrap_or(AnalysisRange { moments, individuals: analysis.model.instance_scope, individuals_requested: 0, decisions: None });
            claims.push(Claim {
                claim: "scenario_satisfiable".to_string(),
                subject: Some(format!("scenario {}", block.name)),
                verdict: outcome.verdict,
                reason,
                vacuous: false,
                // The expectation of the author decides whether the verdict is a finding.
                required: false,
                statement: "the behaviour that the scenario states satisfies each statement of the package".to_string(),
                not_claimed: "that the behaviour can be reached from an initial state, or that it ever occurs".to_string(),
                range,
                lifted: true,
                relation: "exact: the behaviour is concrete and complete, and the judgement is about it alone".to_string(),
                method: "reference evaluation of the typed meaning of each statement, and a decision of the formulas of the reading with the behaviour fixed".to_string(),
                evidence: vec![format!("reference evaluator: {}{}", outcome.reference, if outcome.undefined.is_empty() { String::new() } else { format!("; without a value in this behaviour, and not counted as met: the share of {}", outcome.undefined.iter().map(|(statement, _)| format!("[{statement}]")).collect::<Vec<_>>().join(", ")) }), format!("formulas of the reading: {}", outcome.generated), format!("expected: {}", if block.expect.is_empty() { "nothing" } else { &block.expect })],
                unresolved: outcome.unevaluated.iter().map(|(statement, _)| statement.clone()).collect(),
            });
            out.scenarios.push(outcome);
        }
    }
    if !claims.is_empty() {
        analysis.claims.claims.retain(|c| !(c.claim == "scenario_satisfiable" && c.verdict == Verdict::NotRequested));
        analysis.claims.claims.extend(claims);
    }
    out
}
