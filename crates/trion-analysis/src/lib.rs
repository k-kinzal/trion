//! Orchestrate a backend and accept only conclusions supported by original-Core checks.

mod process;

use serde::{Deserialize, Serialize};
use trion_boolean::{BackendSettings, Contract, Preparation, Reply, Request, Response, EXACT};
use trion_core::{Problem, Question};
use trion_reference::{check_witness, scan, Scan, VERSION as CHECKER};

pub use process::run_worker;

const RECORD: &str = "analysis-json/1";
const RUNNER: &str = "process-runner/1";

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Settings {
    pub backend: BackendSettings,
    pub reference_assignments: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "observation", content = "detail", rename_all = "snake_case")]
pub enum Observation {
    NotRun,
    Response(String),
    Timeout,
    BackendFailure(String),
    UnusableOutput(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Execution {
    NotRun,
    Completed,
    Undecided,
    Timeout,
    ResourceLimit,
    BackendFailure,
    EvidenceRejected,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Conclusion {
    Satisfiable,
    Unsatisfiable,
    Entails,
    DoesNotEntail,
    None,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Premises {
    Consistent,
    Contradictory,
    Unchecked,
    Undecided,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Evidence {
    CheckedCertificate,
    CheckedModel(Vec<bool>),
    CheckedCounterexample(Vec<bool>),
    Exhaustive,
    ExternalResponse,
    None,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Outcome {
    execution: Execution,
    conclusion: Conclusion,
    premises: Premises,
    evidence: Evidence,
    reference_assignments: Option<u64>,
    reason: Option<String>,
}

impl Outcome {
    fn open(execution: Execution, reason: Option<String>) -> Self {
        Self {
            execution,
            reason,
            conclusion: Conclusion::None,
            premises: Premises::Unchecked,
            evidence: Evidence::None,
            reference_assignments: None,
        }
    }

    pub fn execution(&self) -> Execution {
        self.execution
    }

    pub fn conclusion(&self) -> Conclusion {
        self.conclusion
    }

    pub fn premises(&self) -> Premises {
        self.premises
    }

    pub fn evidence(&self) -> &Evidence {
        &self.evidence
    }

    pub fn summary(&self) -> &'static str {
        match (self.conclusion, self.premises) {
            (Conclusion::Entails, Premises::Contradictory) => {
                "vacuous entailment: contradictory premises"
            }
            (Conclusion::Entails, _) => "entails",
            (Conclusion::DoesNotEntail, _) => "does not entail",
            (Conclusion::Satisfiable, _) => "satisfiable",
            (Conclusion::Unsatisfiable, _) => "unsatisfiable: contradictory premises",
            (Conclusion::None, _) => match self.execution {
                Execution::NotRun => "not run",
                Execution::Completed => "no conclusion",
                Execution::Undecided => "undecided",
                Execution::Timeout => "timed out",
                Execution::ResourceLimit => "resource limit",
                Execution::BackendFailure => "backend failure",
                Execution::EvidenceRejected => "evidence rejected",
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Saved {
    version: String,
    runner: String,
    checker: String,
    adapter: String,
    settings: Settings,
    problem: Problem,
    translation: Preparation,
    observation: Observation,
    outcome: Outcome,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Record(Saved);

impl Record {
    pub fn outcome(&self) -> &Outcome {
        &self.0.outcome
    }

    pub fn translation(&self) -> &Preparation {
        &self.0.translation
    }

    pub fn observation(&self) -> &Observation {
        &self.0.observation
    }

    pub fn problem(&self) -> &Problem {
        &self.0.problem
    }

    /// Regenerate the exact request and outcome instead of trusting the saved result.
    pub fn replay(problem: &Problem, saved: &[u8]) -> Result<Self, String> {
        let data: Saved = serde_json::from_slice(saved).map_err(|error| error.to_string())?;
        let translation = EXACT.prepare(problem, data.settings.backend);
        if data.version != RECORD
            || data.runner != RUNNER
            || data.checker != CHECKER
            || data.adapter != EXACT.id
            || &data.problem != problem
            || data.translation != translation
        {
            return Err(
                "saved analysis differs in version, subject, settings, or translation".into(),
            );
        }
        let rebuilt = analyze(problem, &EXACT, data.settings, |_| data.observation.clone());
        if rebuilt.0 != data {
            return Err("saved outcome or observation disagrees with replay".into());
        }
        Ok(rebuilt)
    }
}

pub fn analyze(
    problem: &Problem,
    contract: &Contract,
    settings: Settings,
    execute: impl FnOnce(&Request) -> Observation,
) -> Record {
    let translation = contract.prepare(problem, settings.backend);
    let (observation, outcome) = match &translation {
        Preparation::Applicable(request) => {
            let observation = execute(request);
            let outcome = accept(
                problem,
                request,
                &observation,
                settings.reference_assignments,
            );
            (observation, outcome)
        }
        Preparation::Unsupported(reason) | Preparation::PreconditionFailed(reason) => (
            Observation::NotRun,
            Outcome::open(Execution::NotRun, Some(reason.clone())),
        ),
    };
    Record(Saved {
        version: RECORD.into(),
        runner: RUNNER.into(),
        checker: CHECKER.into(),
        adapter: contract.id.into(),
        settings,
        problem: problem.clone(),
        translation,
        observation,
        outcome,
    })
}

fn reject(reason: impl Into<String>) -> Outcome {
    Outcome::open(Execution::EvidenceRejected, Some(reason.into()))
}

fn accept(problem: &Problem, request: &Request, observation: &Observation, budget: u64) -> Outcome {
    let output = match observation {
        Observation::Response(output) => output,
        Observation::NotRun => return Outcome::open(Execution::NotRun, None),
        Observation::Timeout => return Outcome::open(Execution::Timeout, None),
        Observation::BackendFailure(reason) => {
            return Outcome::open(Execution::BackendFailure, Some(reason.clone()))
        }
        Observation::UnusableOutput(reason) => return reject(reason),
    };
    let response: Response = match serde_json::from_str(output) {
        Ok(response) => response,
        Err(error) => return reject(format!("malformed backend response: {error}")),
    };
    if response.request != request.id() || response.scope != request.scope {
        return reject("response refers to a different request or scope");
    }
    let entailment = matches!(problem.query().question(), Question::Entails(_));
    match response.reply {
        Reply::Unknown => Outcome {
            evidence: Evidence::ExternalResponse,
            ..Outcome::open(
                Execution::Undecided,
                Some("backend returned unknown".into()),
            )
        },
        Reply::ResourceLimit => Outcome {
            evidence: Evidence::ExternalResponse,
            ..Outcome::open(
                Execution::ResourceLimit,
                Some("backend assignment budget exhausted".into()),
            )
        },
        Reply::Sat(values) => {
            if request.settings.max_assignments == 0 || !check_witness(problem, &values) {
                return reject("backend valuation fails the original query condition");
            }
            let reference_assignments = match scan(problem, budget) {
                Scan::Incomplete => None,
                Scan::Complete {
                    assignments,
                    has_model: true,
                    has_candidate: true,
                } => Some(assignments),
                Scan::Complete { .. } => return reject("witness and full reference scan disagree"),
            };
            let (conclusion, evidence) = if entailment {
                (
                    Conclusion::DoesNotEntail,
                    Evidence::CheckedCounterexample(values),
                )
            } else {
                (Conclusion::Satisfiable, Evidence::CheckedModel(values))
            };
            Outcome {
                execution: Execution::Completed,
                conclusion,
                evidence,
                reference_assignments,
                premises: Premises::Consistent,
                reason: None,
            }
        }
        Reply::Unsat => {
            let enough = u32::try_from(request.slots)
                .ok()
                .and_then(|slots| 1_u64.checked_shl(slots))
                .is_some_and(|count| count <= request.settings.max_assignments);
            if !enough {
                return reject("backend budget cannot cover the scope of its unsat response");
            }
            match scan(problem, budget) {
                Scan::Incomplete => Outcome {
                    premises: Premises::Undecided,
                    evidence: Evidence::ExternalResponse,
                    ..Outcome::open(
                        Execution::Undecided,
                        Some("reference assignment budget is insufficient".into()),
                    )
                },
                Scan::Complete {
                    has_candidate: true,
                    ..
                } => reject("original query has a witness"),
                Scan::Complete {
                    assignments,
                    has_model,
                    has_candidate: false,
                } => Outcome {
                    execution: Execution::Completed,
                    premises: if has_model {
                        Premises::Consistent
                    } else {
                        Premises::Contradictory
                    },
                    conclusion: if entailment {
                        Conclusion::Entails
                    } else {
                        Conclusion::Unsatisfiable
                    },
                    evidence: Evidence::Exhaustive,
                    reference_assignments: Some(assignments),
                    reason: None,
                },
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ComparisonError {
    DifferentSubject,
    InconsistentEvidence,
}

/// For already accepted records. Callers keep the two inputs as evidence.
pub fn compare(left: &Record, right: &Record) -> Result<(), ComparisonError> {
    if left.problem() != right.problem() {
        return Err(ComparisonError::DifferentSubject);
    }
    let left = left.outcome();
    let right = right.outcome();
    let conflicting_conclusions = left.conclusion != Conclusion::None
        && right.conclusion != Conclusion::None
        && left.conclusion != right.conclusion;
    let conflicting_premises = matches!(
        (left.premises, right.premises),
        (Premises::Consistent, Premises::Contradictory)
            | (Premises::Contradictory, Premises::Consistent)
    );
    if conflicting_conclusions || conflicting_premises {
        Err(ComparisonError::InconsistentEvidence)
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trion_core::{CoreDocument, Expr};

    #[test]
    fn conflicting_checked_observations_stop_comparison() {
        let subject = Problem::new(
            CoreDocument::new(vec![], vec![]).unwrap(),
            Question::Entails(Expr::True),
        )
        .unwrap();
        let settings = Settings {
            backend: BackendSettings {
                max_assignments: 1,
                timeout_ms: 5000,
            },
            reference_assignments: 1,
        };
        let left = analyze(&subject, &EXACT, settings, |request| {
            Observation::Response(
                serde_json::to_string(&trion_boolean::solve(request).unwrap()).unwrap(),
            )
        });
        assert_eq!(left.outcome().conclusion(), Conclusion::Entails);
        // Simulate an inconsistency that bypassed a verifier. Comparison must
        // preserve both records and fail rather than selecting a conclusion.
        let mut right = left.clone();
        right.0.outcome.conclusion = Conclusion::DoesNotEntail;
        right.0.outcome.evidence = Evidence::CheckedCounterexample(vec![]);
        assert_eq!(
            compare(&left, &right),
            Err(ComparisonError::InconsistentEvidence)
        );
        assert_eq!(left.outcome().conclusion(), Conclusion::Entails);
        assert_eq!(right.outcome().conclusion(), Conclusion::DoesNotEntail);
    }
}
