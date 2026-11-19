use clap::Subcommand;
use serde::{Deserialize, Serialize};
use serde_json::value::RawValue;
use std::path::PathBuf;
use trion_analysis::{analyze, compare, run_worker, Execution, Premises, Record, Settings};
use trion_boolean::{solve, BackendSettings, Request, EXACT};
use trion_cnl::Accepted;

#[derive(Subcommand)]
pub(crate) enum Command {
    /// Run the exact Boolean backend and check its answer against the original Core.
    Analyze {
        artifact: PathBuf,
        #[arg(long, default_value_t = 4096)]
        backend_assignments: u64,
        #[arg(long, default_value_t = 4096)]
        reference_assignments: u64,
        #[arg(long, default_value_t = 5000)]
        timeout_ms: u64,
    },
    /// Recheck the saved artifact, conversion, response and outcome.
    Replay { record: PathBuf },
    /// Recheck two saved records and stop if their verified conclusions conflict.
    Compare { left: PathBuf, right: PathBuf },
    #[command(name = "nnf-worker", hide = true)]
    Worker,
}

#[derive(Serialize)]
struct Envelope<'a> {
    artifact_id: String,
    artifact: &'a Accepted,
    analysis: &'a Record,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SavedEnvelope {
    artifact_id: String,
    artifact: Box<RawValue>,
    analysis: Box<RawValue>,
}

fn replay(path: PathBuf) -> Result<Record, String> {
    let bytes = std::fs::read(path).map_err(|error| error.to_string())?;
    let saved: SavedEnvelope = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    let artifact = Accepted::from_json(saved.artifact.get().as_bytes())?;
    if artifact.id() != saved.artifact_id {
        return Err("analysis refers to a different input artifact".into());
    }
    Record::replay(artifact.problem(), saved.analysis.get().as_bytes())
}

pub(crate) fn dispatch(command: Command) -> Result<bool, String> {
    match command {
        Command::Analyze {
            artifact,
            backend_assignments,
            reference_assignments,
            timeout_ms,
        } => {
            let artifact =
                Accepted::from_json(&std::fs::read(artifact).map_err(|error| error.to_string())?)?;
            let settings = Settings {
                backend: BackendSettings {
                    max_assignments: backend_assignments,
                    timeout_ms,
                },
                reference_assignments,
            };
            let executable = std::env::current_exe().map_err(|error| error.to_string())?;
            let record = analyze(artifact.problem(), &EXACT, settings, |request| {
                run_worker(
                    std::process::Command::new(executable).arg("nnf-worker"),
                    request,
                )
            });
            let envelope = Envelope {
                artifact_id: artifact.id(),
                artifact: &artifact,
                analysis: &record,
            };
            println!(
                "{}",
                serde_json::to_string(&envelope).map_err(|error| error.to_string())?
            );
            eprintln!("{}", record.outcome().summary());
            Ok(record.outcome().execution() == Execution::Completed
                && record.outcome().premises() != Premises::Contradictory)
        }
        Command::Replay { record } => {
            println!("{}", replay(record)?.outcome().summary());
            Ok(true)
        }
        Command::Compare { left, right } => {
            compare(&replay(left)?, &replay(right)?).map_err(|error| format!("{error:?}"))?;
            println!("No conflict between checked conclusions for this query.");
            Ok(true)
        }
        Command::Worker => {
            let request: Request = serde_json::from_reader(std::io::stdin().lock())
                .map_err(|error| error.to_string())?;
            let response = solve(&request)?;
            println!(
                "{}",
                serde_json::to_string(&response).map_err(|error| error.to_string())?
            );
            Ok(true)
        }
    }
}
