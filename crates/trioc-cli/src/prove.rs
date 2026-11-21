//! `trioc prove`: the proof of each obligation that an MMT form states.
//!
//! Each obligation gets exactly one result: `proved`, `refuted` or
//! `unproved`, with the bounded proposition that the result is about. A
//! result is `proved` or `refuted` only when
//!
//! 1. the solver of trion decided each question that it rests on; and
//! 2. the checker of `trion-checker`, which shares no code with the search,
//!    accepts the witness or the refutation of each of those questions.
//!
//! Anything else is `unproved`, with the reason. A certificate is issued
//! only for a proved obligation, in each requested format that can express
//! it; a format that cannot is reported with an error or a warning.
//!
//! trioc is a prover of its own and runs no other program. Every
//! certificate is made from the answers of trion's solver and printed from
//! the syntax of its format's crate: SMT-LIB 2.7 with `smtlib`, MoXI with
//! `moxi`, Alethe with `alethe`, CPC with `eunoia` and `cpc`; the proofs of
//! Alethe and CPC restate the solver's refutations
//! ([`trion_verification::proof::derive`]). Whether a certificate is right is
//! for the checker of its format to say from the certificate alone (Carcara
//! for Alethe, Ethos for CPC, any SMT-LIB solver for the smt2 form, a model
//! checker for MoXI), and trion's tests run them on its certificates. What
//! each format holds is said at `certify`.

use crate::mmt::Form;
use serde::Serialize;
use std::path::{Path, PathBuf};
use trion_language::{Diagnostic, SpecRef};
use trion_solver::{Formula, Status};
use trion_verification::proof::{self, Derivation, Names};
use trion_verification::{Asked, ObligationVerdict, PROPOSITIONAL_CHECK};

/// The formats of a certificate.
pub const FORMATS: [&str; 4] = ["smt2", "alethe", "cpc", "moxi"];

/// The result of one obligation.
#[derive(Debug, Clone, Serialize)]
pub struct Result {
    pub obligation: String,
    pub property: String,
    /// The proposition that the result is about, with its bound.
    pub proposition: String,
    pub verdict: ObligationVerdict,
    pub reason: Option<String>,
    /// The questions that the verdict rests on.
    pub questions: usize,
    /// The certificates that were written, by format.
    pub certificates: Vec<String>,
    /// For a refuted obligation of responses: each situation without one,
    /// with the statements that cannot all be kept in it.
    pub counterexamples: Vec<trion_verification::Counterexample>,
    /// Original checked input, answers and result for propositional obligations.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) propositional: Option<crate::propositional::Record>,
}

/// A problem of a certificate format, as an error or a warning.
#[derive(Debug, Clone, Serialize)]
pub struct FormatNote {
    pub format: String,
    pub severity: &'static str,
    pub obligation: Option<String>,
    pub message: String,
}

/// What a result is about: the package inputs, its obligations and their bounds. A
/// result says nothing about another subject.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Subject {
    pub package: String,
    pub input_digest: String,
    pub obligations_digest: String,
    pub moments: usize,
    pub individuals: Option<usize>,
}

impl Subject {
    pub fn of(form: &Form) -> Self {
        let obligations_digest = crate::digest::hex(serde_json::to_vec(&form.obligations).expect("serializable proof obligations"));
        Subject { package: form.package.clone(), input_digest: form.input_digest.clone(), obligations_digest, moments: form.obligations.moments, individuals: form.obligations.individuals }
    }

    /// The fields in which a saved subject differs from this one.
    pub fn differs_from(&self, saved: &serde_json::Value) -> Vec<String> {
        let mine = serde_json::to_value(self).unwrap_or_default();
        ["package", "input_digest", "obligations_digest", "moments", "individuals"].iter().filter(|field| saved.get(**field) != mine.get(**field)).map(|field| format!("{field} (`{}` here, `{}` saved)", mine[*field], saved.get(*field).cloned().unwrap_or_default())).collect()
    }
}

/// What proving a form found.
#[derive(Debug, Clone, Serialize)]
pub struct Proved {
    pub subject: Subject,
    pub package: String,
    pub input_digest: String,
    pub results: Vec<Result>,
    pub notes: Vec<FormatNote>,
    /// What the certificates need beside them to be checked.
    pub certification: Certification,
    /// What keeps each obligation that is not proved from being proved, as
    /// a finding about the statements of the package.
    pub diagnostics: Vec<Diagnostic>,
}

impl Proved {
    /// `true` unless each obligation is proved and no format reported an error.
    pub fn failed(&self) -> bool {
        self.results.iter().any(|r| r.verdict != ObligationVerdict::Proved) || self.notes.iter().any(|n| n.severity == "error") || !self.diagnostics.is_empty()
    }
}

/// The formulas of each question.
fn formulas(asked: &[Asked]) -> Vec<&[Formula]> {
    asked.iter().map(|a| a.formulas.as_slice()).collect()
}

/// The stem of the certificate files of an obligation: its name, with each
/// character other than an ASCII letter, a digit, `-` and `.` written `_`.
/// Distinct names can have the same stem, so [`same_files`] finds them.
fn file_name(obligation: &str) -> String {
    obligation.chars().map(|c| if c.is_ascii_alphanumeric() || c == '-' || c == '.' { c } else { '_' }).collect()
}

/// For each obligation whose certificate files would be those of another
/// obligation, the others. Stems are compared without case, because a file
/// system may not tell `A` from `a`. The stems of the problems of an
/// obligation (`<stem>-q<k>`, `<stem>-q<k>-witness`) are distinct whenever
/// the stems of the obligations are, so comparing these suffices.
fn same_files<'a>(obligations: impl IntoIterator<Item = &'a str>) -> std::collections::HashMap<&'a str, Vec<&'a str>> {
    let mut by_stem: std::collections::HashMap<String, Vec<&str>> = std::collections::HashMap::new();
    for obligation in obligations {
        by_stem.entry(file_name(obligation).to_lowercase()).or_default().push(obligation);
    }
    let mut out = std::collections::HashMap::new();
    for group in by_stem.values().filter(|group| group.len() > 1) {
        for (k, obligation) in group.iter().enumerate() {
            let others = group.iter().enumerate().filter(|(j, _)| *j != k).map(|(_, other)| *other).collect();
            out.insert(*obligation, others);
        }
    }
    out
}

/// The problem of each question that a proof format of refutations
/// proves, with the refutation of its assertions: an unsatisfiable
/// question itself, refuted by the solver's answer, and for a satisfiable
/// one the check of its witness ([`Names::assertions`]), which the solver
/// refutes here and the checker of `trion-checker` accepts. Each problem
/// comes with its file stem: `<obligation>-q<k>` and
/// `<obligation>-q<k>-witness`.
fn refutations(names: &Names, asked: &[Asked], stem: &str) -> std::result::Result<Vec<Refuted>, String> {
    let mut out = Vec::new();
    for (k, question) in asked.iter().enumerate() {
        let number = k + 1;
        let (stem, witness, refutation) = match question.answer.status {
            Status::Unsatisfiable => {
                let refutation = question.answer.refutation().cloned().ok_or_else(|| format!("question {number} is unsatisfiable without a refutation"))?;
                (format!("{stem}-q{number}"), None, refutation)
            }
            Status::Satisfiable => {
                let witness = question.answer.witness().ok_or_else(|| format!("question {number} is satisfiable without a witness, so no refutation shows it"))?;
                let check = names.assertions(&question.formulas, Some(witness));
                let answer = trion_solver::decide(&check);
                trion_checker::certificate::check(&check, &answer).map_err(|problem| format!("the checker rejects the refutation of the witness check of question {number}: {problem}"))?;
                let refutation = answer.refutation().cloned().ok_or_else(|| format!("the solver does not refute the witness check of question {number}"))?;
                (format!("{stem}-q{number}-witness"), Some(witness), refutation)
            }
            Status::Unknown => return Err(format!("question {number} has no answer")),
        };
        let script = proof::problem(names, &question.formulas, witness)?;
        let derivation = proof::derive(names, &names.assertions(&question.formulas, witness), &refutation).map_err(|problem| format!("the refutation of {stem} cannot be stated over its problem: {problem}"))?;
        out.push(Refuted { stem, script, derivation });
    }
    Ok(out)
}

/// The problem of a question, with its file stem, and the derivation of its refutation.
#[derive(Debug, Clone)]
struct Refuted {
    stem: String,
    script: smtlib::Script,
    derivation: Derivation,
}

/// The directory of the CPC signature, relative to the CPC documents,
/// which include `signature/Cpc.eo`.
pub const CPC_SIGNATURE: &str = "signature";

/// The signature that the CPC documents are written for.
pub const CPC_CALCULUS: &str = "proofs/eo/cpc of the sources of cvc5 1.4.2";

/// What the certificates of a run need beside them to be checked.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct Certification {
    /// When a CPC document was written: the signature that the documents
    /// include from `cpc/signature/`, which trioc does not hold, and which
    /// whoever checks them places there.
    pub cpc_signature: Option<&'static str>,
}

/// Writes, for each problem, its Alethe pair into `target`: the problem
/// `<stem>.smt2` and its proof `<stem>.smt2.alethe`, for Carcara.
fn alethe_pairs(problems: &[Refuted], target: &Path, files: &mut Vec<PathBuf>) -> std::result::Result<(), String> {
    for Refuted { stem, script, derivation } in problems {
        let proof = derivation.alethe().map_err(|problem| format!("the Alethe proof of {stem} cannot be written: {problem}"))?;
        let problem = target.join(format!("{stem}.smt2"));
        write(&problem, &script.to_string())?;
        files.push(problem);
        let proof_file = target.join(format!("{stem}.smt2.alethe"));
        write(&proof_file, &proof.to_text())?;
        files.push(proof_file);
    }
    Ok(())
}

/// Writes, for each problem, its CPC document into `target`, for Ethos:
/// the problem `<stem>.smt2`, and `<stem>.cpc`, which includes the CPC
/// signature from `signature/` ([`CPC_CALCULUS`]) and names the problem as
/// its `reference`, so that Ethos checks that its assumptions are the
/// problem's assertions.
fn cpc_documents(problems: &[Refuted], target: &Path, files: &mut Vec<PathBuf>) -> std::result::Result<(), String> {
    for Refuted { stem, script, derivation } in problems {
        let body = derivation.cpc().map_err(|problem| format!("the CPC proof of {stem} cannot be written: {problem}"))?;
        let document = cpc::ProofDocument::new(CPC_SIGNATURE, cpc::Variant::Cpc, body).and_then(|d| d.with_reference(&format!("{stem}.smt2"))).map_err(|e| format!("the CPC proof of {stem} cannot reference its problem: {e}"))?;
        let problem = target.join(format!("{stem}.smt2"));
        files.push(problem);
        let path = document.write(target, &format!("{stem}.cpc"), Some(&script.to_string())).map_err(|e| format!("cannot write the CPC document {stem}: {e}"))?;
        files.push(path);
    }
    Ok(())
}

fn write(path: &Path, text: &str) -> std::result::Result<(), String> {
    std::fs::write(path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))
}

fn create(dir: &Path) -> std::result::Result<(), String> {
    std::fs::create_dir_all(dir).map_err(|e| format!("cannot create {}: {e}", dir.display()))
}

/// Writes the certificates of a proved obligation in each format and
/// returns the formats written.
///
/// - `smt2`: `<obligation>.smt2`, one SMT-LIB 2.7 script in QF_LIA: each
///   question with the answer it is expected to have, and for each
///   satisfiable question the check of its witness (the values of the
///   witness asserted with the negation of the question's formulas,
///   expected `unsat`), which any SMT-LIB solver decides again.
/// - `alethe`: in `alethe/`, one problem and proof pair per question
///   (`<stem>.smt2`, `<stem>.smt2.alethe`), for Carcara; a satisfiable
///   question is proved by the refutation of its witness check.
/// - `cpc`: in `cpc/`, one problem and proof document per question
///   (`<stem>.smt2`, `<stem>.cpc`), for Ethos. The documents include the CPC
///   signature from `cpc/signature/` ([`CPC_CALCULUS`]), which is not
///   written: whoever checks them places it there.
/// - `moxi`: `<obligation>.moxi`, each question as a system and a
///   reachability query.
///
/// Every form is syntax that its format's crate prints; no certificate is
/// checked here. A format that cannot state the proof of the obligation
/// keeps nothing for it and reports an error.
fn certify(dir: &Path, obligation: &str, asked: &[Asked], formats: &[String], notes: &mut Vec<FormatNote>, certification: &mut Certification) -> Vec<String> {
    let mut written = Vec::new();
    let name = file_name(obligation);
    let note = |format: &str, severity: &'static str, message: String| FormatNote { format: format.to_string(), severity, obligation: Some(obligation.to_string()), message };
    if let Err(problem) = create(dir) {
        notes.extend(formats.iter().map(|format| note(format, "error", format!("no {format} certificate is issued: {problem}"))));
        return written;
    }
    let questions = formulas(asked);
    let names = Names::of(&questions);
    // The refutations of the questions, made once for both proof formats.
    let mut refuted: Option<std::result::Result<Vec<Refuted>, String>> = None;
    for format in formats {
        match format.as_str() {
            "smt2" => {
                let expected: Vec<Option<bool>> = asked.iter().map(|a| matches!(a.answer.status, Status::Satisfiable | Status::Unsatisfiable).then_some(a.answer.status == Status::Satisfiable)).collect();
                let witnesses: Vec<_> = asked.iter().map(|a| if a.answer.status == Status::Satisfiable { a.answer.witness() } else { None }).collect();
                for (k, _) in asked.iter().enumerate().filter(|(k, a)| a.answer.status == Status::Satisfiable && witnesses[*k].is_none()) {
                    notes.push(note(format, "warning", format!("question {} is satisfiable without a witness: the smt2 form states it, and nothing in it shows the answer", k + 1)));
                }
                let issued = proof::questions(&questions, &expected, &witnesses).and_then(|script| {
                    write(&dir.join(format!("{name}.smt2")), &script.text(&format!("the questions of the obligation {obligation}")))
                });
                match issued {
                    Ok(()) => written.push(format.clone()),
                    Err(problem) => notes.push(note(format, "error", format!("no smt2 certificate is issued: {problem}"))),
                }
            }
            "alethe" | "cpc" if asked.is_empty() => notes.push(note(format, "warning", format!("the obligation rests on no question, so {format} has no proof to state for it, and nothing is written"))),
            "alethe" | "cpc" => {
                let target = dir.join(format.as_str());
                let mut files = Vec::new();
                let problems = refuted.get_or_insert_with(|| refutations(&names, asked, &name));
                let issued = problems.clone().and_then(|problems| {
                    create(&target)?;
                    if format == "alethe" {
                        alethe_pairs(&problems, &target, &mut files)
                    } else {
                        cpc_documents(&problems, &target, &mut files)
                    }
                });
                match issued {
                    Ok(()) => {
                        if format == "cpc" {
                            certification.cpc_signature = Some(CPC_CALCULUS);
                        }
                        written.push(format.clone());
                    }
                    Err(problem) => {
                        // Nothing of an obligation whose proof cannot be
                        // stated stays: no certificate without a proof.
                        for file in files {
                            let _ = std::fs::remove_file(file);
                        }
                        // A directory that holds no certificate goes too.
                        let _ = std::fs::remove_dir(&target);
                        notes.push(note(format, "error", format!("no {format} certificate is issued: {problem}")));
                    }
                }
            }
            "moxi" => {
                let issued = proof::moxi_script(&questions).and_then(|(names, script)| {
                    let expected: Vec<bool> = asked.iter().map(|a| a.answer.status == Status::Satisfiable).collect();
                    write(&dir.join(format!("{name}.moxi")), &proof::moxi_text(&names, &script, &expected, &format!("the questions of the obligation {obligation}")))
                });
                match issued {
                    Ok(()) => written.push(format.clone()),
                    Err(problem) => notes.push(note(format, "error", format!("no moxi certificate is issued: {problem}"))),
                }
            }
            other => notes.push(note(other, "error", format!("`{other}` is no certificate format; the formats are {}", FORMATS.join(", ")))),
        }
    }
    written
}

/// Proves each obligation of a form. With `certificates`, the certificates
/// of each proved obligation are written there in each of `formats`.
pub fn prove(form: &Form, decisions: Option<u64>, certificates: Option<&Path>, formats: &[String]) -> std::result::Result<Proved, String> {
    let stated = &form.obligations;
    let inst = stated.instance(decisions);
    let mut results = Vec::new();
    let mut notes = Vec::new();
    let mut certification = Certification::default();
    let same = same_files(stated.obligations.iter().map(|o| o.name.as_str()));
    for (position, obligation) in stated.obligations.iter().enumerate() {
        let decision = stated.decide(&inst, obligation);
        let (mut verdict, mut reason) = (decision.verdict, decision.reason.clone());
        let propositional = if obligation.property == PROPOSITIONAL_CHECK || stated.propositional.contains_key(&position) {
            let answers = decision.asked.iter().map(|question| question.answer.clone()).collect();
            let record = crate::propositional::check(form, position, decisions, answers)?;
            verdict = record.outcome.verdict();
            reason = record.outcome.reason().map(str::to_string);
            Some(record)
        } else {
            None
        };
        if propositional.is_none() && verdict != ObligationVerdict::Unproved {
            // The independent checker accepts each answer.
            for question in &decision.asked {
                if let Err(problem) = trion_checker::certificate::check(&question.formulas, &question.answer) {
                    verdict = ObligationVerdict::Unproved;
                    reason = Some(format!("the checker rejects the answer of `{}`: {problem}", question.name));
                    break;
                }
            }
        }
        let written = match (verdict, certificates, same.get(obligation.name.as_str())) {
            // A certificate written under the name of another obligation's
            // would replace it, or be replaced by it: neither is written.
            (ObligationVerdict::Proved, Some(_), Some(others)) => {
                for format in formats {
                    let message = format!("no {format} certificate is issued: its files would be named `{}`, as those of {}", file_name(&obligation.name), others.iter().map(|o| format!("`{o}`")).collect::<Vec<_>>().join(", "));
                    notes.push(FormatNote { format: format.clone(), severity: "error", obligation: Some(obligation.name.clone()), message });
                }
                Vec::new()
            }
            (ObligationVerdict::Proved, Some(dir), None) => certify(dir, &obligation.name, &decision.asked, formats, &mut notes, &mut certification),
            _ => Vec::new(),
        };
        let counterexamples = if verdict == ObligationVerdict::Refuted { decision.counterexamples } else { Vec::new() };
        results.push(Result { obligation: obligation.name.clone(), property: obligation.property.clone(), proposition: obligation.proposition.clone(), verdict, reason, questions: decision.asked.len(), certificates: written, counterexamples, propositional });
    }
    let diagnostics = findings(form, &results);
    Ok(Proved { subject: Subject::of(form), package: form.package.clone(), input_digest: form.input_digest.clone(), results, notes, certification, diagnostics })
}

/// The finding of each obligation that is not proved: what is refuted, with
/// the statements that it is about, and what is left unproved.
fn findings(form: &Form, results: &[Result]) -> Vec<Diagnostic> {
    let at = |id: &str| -> SpecRef {
        match form.contracts.iter().find(|c| c.id == id) {
            Some(c) => SpecRef { id: c.id.clone(), file: c.file.clone(), line: c.line, text: c.text.clone() },
            None => SpecRef { id: id.to_string(), file: String::new(), line: 0, text: String::new() },
        }
    };
    let statements = |ids: &[String]| -> Vec<SpecRef> { ids.iter().map(|id| at(id)).collect() };
    let mut out = Vec::new();
    for (position, result) in results.iter().enumerate() {
        let why = result.reason.clone().unwrap_or_default();
        let named = result.obligation.split_once('/').map_or("", |(_, name)| name);
        let of = form.obligations.obligations.iter().find(|o| o.name == result.obligation);
        let refs = form.obligations.propositional.get(&position).map_or_else(
            || of.map_or_else(Vec::new, |o| statements(&o.statements)),
            |input| vec![SpecRef::point(&input.file, input.line, &result.obligation)],
        );
        match result.verdict {
            ObligationVerdict::Proved => {}
            ObligationVerdict::Unproved => out.push(Diagnostic::error("obligation-unproved", format!("the obligation {} is neither proved nor refuted: {why}; {}", result.obligation, result.proposition), if result.propositional.is_some() { refs } else { Vec::new() })),
            ObligationVerdict::Refuted => match result.property.as_str() {
                "consistency" if !result.counterexamples.is_empty() => {
                    for counterexample in &result.counterexamples {
                        let situation = if counterexample.facts.is_empty() { "in every situation".to_string() } else { format!("where {}, and the environment can bring that about", counterexample.facts.join(", ")) };
                        // A form that a bound role requires, which the statements do not have.
                        let shaped: Vec<&str> = counterexample.statements.iter().filter(|id| form.contracts.iter().any(|c| &c.id == *id && c.role == "form")).map(String::as_str).collect();
                        if shaped.is_empty() {
                            out.push(Diagnostic::error("contradiction", format!("these statements cannot all be kept {situation}: no system that accepts every input keeps them"), statements(&counterexample.statements)));
                        } else {
                            out.push(Diagnostic::error("shape-violation", format!("these statements do not have the form that {} requires of its role, {situation}: no system keeps them", shaped.join(", ")), statements(&counterexample.statements)));
                        }
                    }
                }
                "consistency" => out.push(Diagnostic::error("contradiction", format!("no system that accepts every input keeps every guarantee: {why}"), refs)),
                "compatibility" => {
                    let named = result.counterexamples.first().map_or_else(Vec::new, |c| statements(&c.statements));
                    out.push(Diagnostic::error("incompatible", format!("no environment that the descriptions allow meets an assumption of a statement: {why}"), if named.is_empty() { refs } else { named }));
                }
                "correctness" => out.push(Diagnostic::error("detail-not-refining", format!("the details of `{named}` do not refine it: {why}; the statement is the reference of its details, and they must accept each of its environments and keep it in each behaviour"), refs)),
                "completeness" => out.push(Diagnostic::error("detail-incomplete", format!("the details of `{named}` do not refine it, and together with it they are consistent and compatible: a requirement of `{named}` is missing from its details"), refs)),
                "realizability" => out.push(Diagnostic::error("unrealizable", format!("no system keeps the guarantee: {}; the environment can act before the response can come, and no system knows an input that has not happened", result.proposition.split_once(": ").map_or(result.proposition.as_str(), |(_, p)| p).replace("cannot bring", "can bring")), refs)),
                "recommendation" => out.push(Diagnostic::error("recommendation-violation", format!("the advice of `{named}` cannot be followed together with the requirements: {}", result.counterexamples.first().map_or(why.clone(), |c| if c.facts.is_empty() { format!("no response keeps {} in any situation", c.statements.join(", ")) } else { format!("no response keeps {} where {}", c.statements.join(", "), c.facts.join(", ")) })), result.counterexamples.first().map_or(refs.clone(), |c| statements(&c.statements)))),
                "choice" if result.obligation.contains("/exclusive/") => out.push(Diagnostic::error("OVERLAPPING_FLOW_GUARDS", format!("two guards of a choice can hold together: {}", result.proposition), refs)),
                "choice" => out.push(Diagnostic::error("INCOMPLETE_FLOW_CHOICE", format!("the guards of a choice can all be false; add `otherwise`: {}", result.proposition), refs)),
                "check" | PROPOSITIONAL_CHECK => out.push(Diagnostic::error("check-refuted", format!("the check {named} is refuted: {why}"), refs)),
                "example" => out.push(Diagnostic::error("example-failed", format!("the example {named} does not observe what it expects: {}", result.proposition), refs)),
                "scenario" => out.push(Diagnostic::error("scenario-failed", format!("the scenario {named} is not judged as its author expects: {}", result.proposition), refs)),
                // The reader refuses a form with any other property.
                other => unreachable!("the property `{other}` is not read"),
            },
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::same_files;

    #[test]
    fn obligations_whose_certificates_would_share_files_are_found() {
        // `/` and `_` are both written `_`; a file system may not tell case.
        let names = ["x/realizability/A/B_C", "x/realizability/A_B/C", "x/check/a", "x/check/A", "x/consistency", "x/compatibility"];
        let same = same_files(names);
        assert_eq!(same.get("x/realizability/A/B_C"), Some(&vec!["x/realizability/A_B/C"]));
        assert_eq!(same.get("x/realizability/A_B/C"), Some(&vec!["x/realizability/A/B_C"]));
        assert_eq!(same.get("x/check/a"), Some(&vec!["x/check/A"]));
        assert_eq!(same.get("x/check/A"), Some(&vec!["x/check/a"]));
        assert!(!same.contains_key("x/consistency") && !same.contains_key("x/compatibility"));
        // An obligation named twice shares its files with itself.
        assert_eq!(same_files(["x/a", "x/a"]).get("x/a"), Some(&vec!["x/a"]));
    }
}
