//! The output of a solver that prints Alethe proofs, split into its
//! responses.
//!
//! A solver prints its responses one after another: `sat`, `unsat` or
//! `unknown` for each `check-sat`, `(error "…")` for an error, and, for each
//! proof, the proof's commands between a pair of parentheses. cvc5 1.4.2
//! with `--dump-proofs --proof-format-mode=alethe` (with `--incremental`
//! when the script uses `push`) prints
//!
//! ```text
//! unsat
//! (
//! (assume a0 p)
//! (assume a1 (! (not p) :named @p_1))
//! (step t0 (cl) :rule resolution :premises (a0 a1))
//! )
//! ```
//!
//! once per `unsat`, and again for each `get-proof`; names such as `@p_1`
//! and indices such as `t0` start over in each proof. A proof printed with
//! [`crate::Proof::to_text`] holds the commands alone, without `unsat` or
//! the surrounding parentheses; Carcara reads that form, and skips a
//! leading `unsat` and one extra pair of parentheses when they are there
//! (`src/parser/mod.rs`, `parse_proof`).
//!
//! The output is read with `smtlib`'s reader in the Alethe dialect
//! ([`crate::term::dialect`]), since a proof can contain number literals
//! that SMT-LIB lacks. Proofs are read as in [`crate::proof`], keeping the
//! positions in the output.
//!
//! # How a response is recognised
//!
//! Responses are not self-describing: "the grammar of responses is
//! ambiguous without the command that was sent" (the `smtlib` crate's
//! `response` module, after SMT-LIB 2.7 §3.11.1, whose `get-proof`
//! response is any S-expression). This reader does not take the commands,
//! because cvc5 prints a proof after every `unsat` under `--dump-proofs`,
//! with no command asking for it; it classifies each response by its
//! shape:
//!
//! - `sat`, `unsat`, `unknown`: [`SolverResponse::CheckSat`];
//! - another symbol: [`SolverResponse::Atom`];
//! - `(error ⟨string⟩)`: [`SolverResponse::Error`];
//! - a non-empty list whose every item is a list headed by the symbol
//!   `assume`, `step` or `anchor` or by `define-fun`, at least one headed
//!   by `assume` or `step`: [`SolverResponse::Proof`] (a list of
//!   `define-fun`s alone is a model);
//! - anything else: [`SolverResponse::Other`].
//!
//! The one misreading: an answer to `get-value`, `get-assignment` or
//! `get-assertions` of that shape, that is, whose every item is headed by
//! a user symbol named `assume`, `step` or `anchor` (at least one of the
//! first two). It is read as a proof, and that fails with a syntax error
//! when its items are not proof commands (`((assume true))`, the value of
//! a constant named `assume`), or gives a proof when they happen to be
//! (`((assume a0 p))`, the assertion `(assume a0 p)` of a function named
//! `assume`). A caller that sends those commands about such symbols reads
//! their answers with `smtlib`'s command-driven response reader instead,
//! and the proofs with [`crate::Proof::parse`].

use crate::error::{Error, ErrorKind, Result};
use crate::proof::Command;
use crate::term::output_dialect;
use smtlib::lexicon::{Reserved, SpecConstant, Symbol};
use smtlib::response::CheckSatResponse;
use smtlib::sexpr::{read_all, Atom, SExpr, Spanned, SpannedKind};
use smtlib::Position;

/// One response of a solver, classified by its shape (see the module
/// documentation).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SolverResponse {
    /// `sat`, `unsat` or `unknown`.
    CheckSat(CheckSatResponse),
    /// Another symbol alone: `success`, `unsupported`, …
    Atom(Symbol),
    /// A proof, with the position of each command in the output.
    Proof(Vec<(Position, Command)>),
    /// `(error "message")`.
    Error(String),
    /// Any other response, such as a model or the value of `get-info`.
    Other(SExpr),
}

fn command_head(node: &Spanned) -> Option<&'static str> {
    let head = node.as_list()?.first()?;
    if head.as_reserved() == Some(Reserved::DefineFun) {
        return Some("define-fun");
    }
    match head.as_symbol()?.as_str() {
        "assume" => Some("assume"),
        "step" => Some("step"),
        "anchor" => Some("anchor"),
        _ => None,
    }
}

fn is_proof(items: &[Spanned]) -> bool {
    items.iter().all(|i| command_head(i).is_some()) && items.iter().any(|i| matches!(command_head(i), Some("assume" | "step")))
}

fn check_sat(symbol: &Symbol) -> Option<CheckSatResponse> {
    match symbol.as_str() {
        "sat" => Some(CheckSatResponse::Sat),
        "unsat" => Some(CheckSatResponse::Unsat),
        "unknown" => Some(CheckSatResponse::Unknown),
        _ => None,
    }
}

/// Reads the responses in `text`, with the position where each starts.
///
/// ```
/// use alethe::SolverResponse;
/// use smtlib::response::CheckSatResponse;
/// let responses = alethe::read_output("unsat\n(\n(assume a0 false)\n(step t0 (cl) :rule false :premises (a0))\n)\n").unwrap();
/// assert_eq!(responses[0].1, SolverResponse::CheckSat(CheckSatResponse::Unsat));
/// assert!(matches!(&responses[1].1, SolverResponse::Proof(commands) if commands.len() == 2));
/// ```
pub fn read_output(text: &str) -> Result<Vec<(Position, SolverResponse)>> {
    // A proof in the output is one parenthesis deeper than on its own; its
    // commands may nest as deep as the limit of `dialect()` themselves.
    read_all(text, output_dialect())?
        .into_iter()
        .map(|node| {
            let response = match node.kind() {
                SpannedKind::Atom(Atom::Symbol(s)) => check_sat(s).map_or_else(|| SolverResponse::Atom(s.clone()), SolverResponse::CheckSat),
                SpannedKind::List(items) if is_proof(items) => SolverResponse::Proof(items.iter().map(|c| Ok((c.position(), Command::from_spanned(c)?))).collect::<Result<_>>()?),
                SpannedKind::List(items) if items.len() == 2 && items[0].as_symbol().is_some_and(|s| s.as_str() == "error") => match items[1].as_constant() {
                    Some(SpecConstant::String(s)) => SolverResponse::Error(s.as_str().to_string()),
                    _ => SolverResponse::Other(node.to_sexpr()),
                },
                _ => SolverResponse::Other(node.to_sexpr()),
            };
            Ok((node.position(), response))
        })
        .collect()
}

/// The proofs in `text`, in order; an error if the solver reported one.
pub fn read_proofs(text: &str) -> Result<Vec<Vec<(Position, Command)>>> {
    let mut out = Vec::new();
    for (position, response) in read_output(text)? {
        match response {
            SolverResponse::Proof(p) => out.push(p),
            SolverResponse::Error(message) => return Err(Error::at(ErrorKind::Output, position, format!("the solver reported an error: {message}"))),
            _ => {}
        }
    }
    Ok(out)
}
