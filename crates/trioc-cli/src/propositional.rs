//! Binding and replay of propositional evidence from the MMT proof path.

use crate::{mmt::Form, prove::Subject};
use serde::{Deserialize, Serialize};
use trion_analysis::{Conclusion, Evidence, Execution, Premises};
use trion_core::{sha256, Problem, Question};
use trion_language::document::PropositionalCheck;
use trion_reference::{check_premises, check_witness, scan, Scan};
use trion_solver::{Answer, Atom, Formula, Status};
use trion_verification::ObligationVerdict;

const LOWERING: &str = "core-to-mmt-propositional";
const CHECKER: &str = "mmt-certificate-checker";
const SOLVER: &str = "trion-mmt-solver";
const REFERENCE_BUDGET: u64 = 4096;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Record {
    lowering: String,
    certificate_checker: String,
    reference_evaluator: String,
    solver: String,
    subject_id: String,
    scope: String,
    approximation: String,
    decision_limit: Option<u64>,
    reference_budget: u64,
    input: PropositionalCheck,
    questions: Vec<Vec<Formula>>,
    answers: Vec<Answer>,
    pub outcome: Outcome,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Outcome {
    execution: Execution,
    conclusion: Conclusion,
    premises: Premises,
    evidence: Evidence,
    reference_assignments: Option<u64>,
    reason: Option<String>,
}

impl Outcome {
    pub(crate) fn verdict(&self) -> ObligationVerdict {
        match (self.conclusion, self.premises) {
            (Conclusion::Entails, Premises::Contradictory)
            | (Conclusion::Unsatisfiable | Conclusion::DoesNotEntail, _) => {
                ObligationVerdict::Refuted
            }
            (Conclusion::Entails | Conclusion::Satisfiable, _) => ObligationVerdict::Proved,
            (Conclusion::None, _) => ObligationVerdict::Unproved,
        }
    }

    pub(crate) fn reason(&self) -> Option<&str> {
        self.reason.as_deref()
    }
}

impl Record {
    pub(crate) fn counterexample(&self) -> Option<Vec<String>> {
        let Evidence::CheckedCounterexample(values) = &self.outcome.evidence else {
            return None;
        };
        Some(
            self.input
                .input
                .problem()
                .document()
                .declarations()
                .iter()
                .zip(values)
                .map(|(name, value)| format!("{name}={value}"))
                .collect(),
        )
    }
}

pub(crate) fn check(
    form: &Form,
    position: usize,
    decision_limit: Option<u64>,
    answers: Vec<Answer>,
) -> Result<Record, String> {
    let questions = form.obligations.propositional_questions(position)?;
    let input = &form.obligations.propositional[&position];
    let subject = Subject::of(form);
    let obligation = &form.obligations.obligations[position];
    let binding = serde_json::to_vec(&(
        subject,
        position,
        obligation,
        input,
        &questions,
        decision_limit,
        REFERENCE_BUDGET,
    ))
    .map_err(|error| error.to_string())?;
    let outcome =
        accept(input.input.problem(), &questions, &answers).unwrap_or_else(|reason| Outcome {
            execution: Execution::EvidenceRejected,
            conclusion: Conclusion::None,
            premises: Premises::Unchecked,
            evidence: Evidence::None,
            reference_assignments: None,
            reason: Some(reason),
        });
    Ok(Record {
        lowering: LOWERING.into(),
        certificate_checker: CHECKER.into(),
        reference_evaluator: trion_reference::ID.into(),
        solver: SOLVER.into(),
        subject_id: sha256(binding),
        scope: "all_valuations".into(),
        approximation: "exact".into(),
        decision_limit,
        reference_budget: REFERENCE_BUDGET,
        input: input.clone(),
        questions,
        answers,
        outcome,
    })
}

fn valuation(problem: &Problem, answer: &Answer) -> Option<Vec<bool>> {
    let atoms = answer.witness()?.atoms();
    Some(
        problem
            .document()
            .declarations()
            .iter()
            .map(|name| {
                // An unused declaration may be completed arbitrarily.
                atoms
                    .get(&Atom::Rel {
                        name: name.clone(),
                        args: Vec::new(),
                    })
                    .copied()
                    .unwrap_or(false)
            })
            .collect(),
    )
}

fn accept(
    problem: &Problem,
    questions: &[Vec<Formula>],
    answers: &[Answer],
) -> Result<Outcome, String> {
    let entailment = matches!(problem.query().question(), Question::Entails(_));
    let first = answers
        .first()
        .ok_or("no answer for the premise question")?;
    let expected = if first.status == Status::Unsatisfiable {
        1
    } else {
        questions.len()
    };
    if answers.len() != expected {
        return Err("the answers do not match the questions of the obligation".into());
    }
    for (formulas, answer) in questions.iter().zip(answers) {
        trion_checker::certificate::check(formulas, answer)?;
    }

    let model = valuation(problem, first);
    if model
        .as_ref()
        .is_some_and(|values| !check_premises(problem, values))
    {
        return Err("the model fails the original Core premises".into());
    }
    let last = answers.get(1);
    let counterexample = last.and_then(|answer| valuation(problem, answer));
    if counterexample
        .as_ref()
        .is_some_and(|values| !check_witness(problem, values))
    {
        return Err("the counterexample fails the original Core question".into());
    }

    let agrees = |answer: &Answer, exists| match answer.status {
        Status::Unknown => true,
        Status::Satisfiable => exists,
        Status::Unsatisfiable => !exists,
    };
    let reference_assignments = match scan(problem, REFERENCE_BUDGET) {
        Scan::Complete {
            assignments,
            has_model,
            has_candidate,
        } => {
            if !agrees(first, has_model)
                || last.is_some_and(|answer| !agrees(answer, has_candidate))
            {
                return Err("the MMT answers disagree with exhaustive Core evaluation".into());
            }
            Some(assignments)
        }
        Scan::Incomplete => None,
    };
    let exclusion = if reference_assignments.is_some() {
        Evidence::Exhaustive
    } else {
        Evidence::CheckedCertificate
    };
    let execution = if answers
        .iter()
        .any(|answer| answer.status == Status::Unknown)
    {
        Execution::ResourceLimit
    } else {
        Execution::Completed
    };
    let (conclusion, premises, evidence, reason) = if first.status == Status::Unsatisfiable {
        if entailment {
            (
                Conclusion::Entails,
                Premises::Contradictory,
                exclusion,
                Some("vacuous entailment: contradictory premises"),
            )
        } else {
            (
                Conclusion::Unsatisfiable,
                Premises::Contradictory,
                exclusion,
                Some("contradictory premises"),
            )
        }
    } else if let Some(values) = counterexample {
        (
            Conclusion::DoesNotEntail,
            Premises::Consistent,
            Evidence::CheckedCounterexample(values),
            Some("checked counterexample to entailment"),
        )
    } else if let Some(values) = model {
        if !entailment {
            (
                Conclusion::Satisfiable,
                Premises::Consistent,
                Evidence::CheckedModel(values),
                None,
            )
        } else if last.is_some_and(|answer| answer.status == Status::Unsatisfiable) {
            (Conclusion::Entails, Premises::Consistent, exclusion, None)
        } else {
            (
                Conclusion::None,
                Premises::Consistent,
                Evidence::CheckedModel(values),
                Some("the decision limit ended the search"),
            )
        }
    } else {
        (
            Conclusion::None,
            Premises::Undecided,
            Evidence::None,
            Some("the decision limit ended the search"),
        )
    };
    Ok(Outcome {
        execution,
        conclusion,
        premises,
        evidence,
        reference_assignments,
        reason: reason.map(str::to_string),
    })
}

#[derive(Deserialize)]
struct SavedProof {
    subject: serde_json::Value,
    results: Vec<SavedResult>,
}

#[derive(Deserialize)]
struct SavedResult {
    obligation: String,
    property: String,
    proposition: String,
    verdict: ObligationVerdict,
    reason: Option<String>,
    questions: usize,
    counterexamples: Vec<serde_json::Value>,
    propositional: Option<Record>,
}

/// Recheck the saved answers against the original MMT form without searching.
pub(crate) fn replay(form: &Form, bytes: &[u8]) -> Result<usize, String> {
    let saved: SavedProof = serde_json::from_slice(bytes).map_err(|error| error.to_string())?;
    if !Subject::of(form).differs_from(&saved.subject).is_empty()
        || saved.results.len() != form.obligations.obligations.len()
    {
        return Err("saved proof refers to a different MMT subject".into());
    }
    for (position, (result, obligation)) in saved
        .results
        .into_iter()
        .zip(&form.obligations.obligations)
        .enumerate()
    {
        if result.obligation != obligation.name
            || result.property != obligation.property
            || result.proposition != obligation.proposition
            || result.propositional.is_some()
                != form.obligations.propositional.contains_key(&position)
        {
            return Err(format!("saved result does not match {}", obligation.name));
        }
        if let Some(record) = result.propositional {
            let rebuilt = check(
                form,
                position,
                record.decision_limit,
                record.answers.clone(),
            )?;
            if rebuilt != record
                || rebuilt.outcome.verdict() != result.verdict
                || rebuilt.outcome.reason() != result.reason.as_deref()
                || rebuilt.answers.len() != result.questions
                || !result.counterexamples.is_empty()
                || rebuilt.outcome.execution == Execution::EvidenceRejected
            {
                return Err(format!(
                    "saved evidence disagrees with replay for {}",
                    obligation.name
                ));
            }
        }
    }
    let count = form.obligations.propositional.len();
    if count == 0 {
        return Err("the MMT form has no propositional evidence to replay".into());
    }
    Ok(count)
}
