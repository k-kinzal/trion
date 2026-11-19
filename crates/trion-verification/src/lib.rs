//! trion-verification: the contracts of a specification and the proof
//! obligations of a correct specification, and their decision.
//!
//! [`analyze`] reads a set with `trion-language`: its [`Analysis`] holds
//! every diagnostic of the language, the vocabulary and the model.
//! [`proof_obligations`] states the obligations of a correct specification
//! over a trace of moments within [`Bounds`], and
//! [`ProofObligations::decide`] decides one of them with the built-in
//! solver, for `trioc`; nothing in `trion` decides an obligation.
//!
//! This crate reads no file and runs no process.

#![warn(unreachable_pub)]

mod analysis;
pub mod proof;

// The helpers of `tests/` are compiled into the unit tests as well: they
// name this crate as its users do.
#[cfg(test)]
extern crate self as trion_verification;
#[cfg(test)]
mod tests;

pub use analysis::{analyze, check_properties, temporal_forms, Analysis, Bounds, Control, ExampleOutcome, RefinementOutcome, proof_obligations, demonstrations, inferred_system, stated_contracts, Counterexample, Scope, StatedContract, Asked, Decision, ObligationQuestion, ObligationVerdict, ProofObligation, ProofObligations, Isolation, Options, RelationReport, PROPOSITIONAL_CHECK};
