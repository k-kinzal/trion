//! trion-verification: whether the contracts of a specification can all
//! hold, and what each result rests on.
//!
//! [`analyze`] reads a set with `trion-language`, states its contracts over
//! a trace of moments and decides, within [`Bounds`], whether they can all
//! hold. Its [`Analysis`] holds every diagnostic, the vocabulary, the model
//! and the consistency result. [`Proof`] is what a decided result rests on:
//! every question with the certificate of its answer; [`Proof::query_groups`]
//! gives the questions as another solver can be asked them.
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

pub use analysis::{analyze, check_properties, check_stability, smt2, temporal_forms, Analysis, Bounds, CheckOutcome, ConflictElement, ConflictExplanation, ConsistencyResult, Control, CoverageExplanation, DerivationStep, EnvironmentFindings, ExampleOutcome, GuardObligation, Isolation, Options, RelationReport, Unrealizable, VacuousCondition};
pub use proof::{Proof, Query, QueryGroup, UsedBounds};
