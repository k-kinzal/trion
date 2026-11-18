//! The command `trioc`: `prove` reads the MMT form that `trion` wrote,
//! proves each proof obligation that it states, reports one result for
//! each, and writes the certificates of each proved obligation.
//!
//! The exit code tells whether every obligation is proved.

use crate::check::written;
use crate::mmt::Form;
use clap::{Parser, Subcommand};
use std::path::PathBuf;
use std::process::ExitCode;

#[derive(Parser)]
#[command(name = "trioc", version, about = "Prove the obligations of the MMT form that trion writes, and issue their certificates")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Prove each proof obligation of an MMT form that `trion --format mmt`
    /// wrote. Each obligation gets one result: proved, refuted or unproved,
    /// with the bound that it is about. trioc proves with trion's own solver
    /// and runs no other program; the certificates are for other checkers:
    /// Carcara reads the Alethe proofs, Ethos the CPC documents, with the
    /// CPC signature of cvc5 1.4.2 (proofs/eo/cpc) placed in cpc/signature.
    Prove {
        /// The MMT form: a file, or the directory of the archive that holds `source/specification.mmt`.
        form: PathBuf,
        /// Print the results as JSON instead of text.
        #[arg(long)]
        json: bool,
        /// Write the certificates of each proved obligation into this directory.
        #[arg(long, value_name = "DIR")]
        certificates: Option<PathBuf>,
        /// The formats of the certificates: smt2, alethe, cpc, moxi.
        #[arg(long, value_name = "FORMAT", value_delimiter = ',', default_value = "smt2")]
        format: Vec<String>,
        /// Stop each solver query after this many decisions; an obligation
        /// that the limit leaves open is unproved.
        #[arg(long, value_name = "N")]
        decision_limit: Option<u64>,
        /// A result that `trioc prove --json` saved: it is compared with
        /// this one, and a result about another subject is refused.
        #[arg(long, value_name = "FILE")]
        against: Option<PathBuf>,
    },
}

fn dispatch(cli: Cli) -> Result<bool, String> {
    match cli.command {
        Command::Prove { form, json, certificates, format, decision_limit, against } => {
            let path = if form.is_dir() { form.join(crate::mmt::FILE) } else { form };
            let text = std::fs::read_to_string(&path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
            let form = Form::read(&text).map_err(|e| format!("{} is no MMT form of trion: {e}", path.display()))?;
            let mut proved = crate::prove::prove(&form, decision_limit, certificates.as_deref(), &format)?;
            // A saved result is about its own subject: where it names other
            // texts, another semantics, another program or other bounds, it
            // says nothing about this one.
            if let Some(path) = &against {
                let saved = std::fs::read_to_string(path).map_err(|e| format!("cannot read {}: {e}", path.display())).and_then(|text| serde_json::from_str::<serde_json::Value>(&text).map_err(|e| format!("{} is no result: {e}", path.display())));
                let problem = match saved {
                    Err(message) => Some(format!("the saved result cannot be compared: {message}")),
                    Ok(saved) => {
                        let fields = proved.subject.differs_from(&saved["subject"]);
                        (!fields.is_empty()).then(|| format!("the saved result at {} is about another subject, and nothing of it holds here: it differs in {}", path.display(), fields.join(", ")))
                    }
                };
                if let Some(problem) = problem {
                    proved.diagnostics.push(trion_language::Diagnostic::error("result-stale", problem, Vec::new()));
                }
            }
            if json {
                println!("{}", serde_json::to_string_pretty(&proved).map_err(|e| e.to_string())?);
            } else {
                for diagnostic in &proved.diagnostics {
                    print!("{}", written(diagnostic));
                }
                for result in &proved.results {
                    let reason = result.reason.as_ref().map_or(String::new(), |why| format!(": {why}"));
                    println!("obligation {} ({}): {}{reason}", result.obligation, result.property, result.verdict.as_str());
                    println!("  {}", result.proposition);
                    for counterexample in &result.counterexamples {
                        let named = counterexample.statements.iter().map(|id| format!("[{id}]")).collect::<Vec<_>>().join(", ");
                        // A situation without a response is what consistency
                        // and its kin refute; elsewhere the statements have
                        // no valuation together.
                        if matches!(result.property.as_str(), "consistency" | "recommendation" | "realizability") {
                            println!("  no response keeps {named} where {}", if counterexample.facts.is_empty() { "nothing is fixed".to_string() } else { counterexample.facts.join(", ") });
                        } else {
                            println!("  {named} hold together in no valuation");
                        }
                    }
                    if !result.certificates.is_empty() {
                        println!("  certificates: {}", result.certificates.join(", "));
                    }
                }
                for note in &proved.notes {
                    let about = note.obligation.as_ref().map_or(String::new(), |o| format!(" ({o})"));
                    println!("{}[certificate-{}]{about}: {}", note.severity, note.format, note.message);
                }
                if let Some(signature) = proved.certification.cpc_signature {
                    println!("certificates: the CPC documents include {signature} from cpc/{}/, which is not written", crate::prove::CPC_SIGNATURE);
                }
                let count = |verdict: trion_verification::ObligationVerdict| proved.results.iter().filter(|r| r.verdict == verdict).count();
                use trion_verification::ObligationVerdict::*;
                println!("{} obligations: {} proved, {} refuted, {} unproved; no result holds beyond its bound", proved.results.len(), count(Proved), count(Refuted), count(Unproved));
                println!("{}", if proved.failed() { "not proved" } else { "proved" });
            }
            Ok(proved.failed())
        }
    }
}

/// Runs the command that the arguments of the process name.
pub fn run() -> ExitCode {
    match dispatch(Cli::parse()) {
        Ok(false) => ExitCode::SUCCESS,
        Ok(true) => ExitCode::from(1),
        Err(message) => {
            eprintln!("error: {message}");
            ExitCode::from(2)
        }
    }
}
