//! trion-checker: what a result about individuals rests on, checked apart
//! from the reading that produced it.
//!
//! The reading of a set (`trion-language`) turns statements into formulas,
//! and the verification (`trion-verification`) decides the formulas. This
//! crate holds the checks that share neither: it evaluates the typed
//! meaning of the statements on a concrete behaviour ([`eval`]), compares
//! that judgement with what the formulas say of the same behaviour
//! ([`compare`]), and checks the record of how a statement was read against
//! the statement ([`derive`]).
//!
//! What this crate shares with the reading: the parser of sentences, the
//! data types of the typed meaning, and the names of the atoms at the
//! moments of a trace. What it does not share: the rules that read a
//! sentence over individuals, the keys of atoms, the placement of a
//! contract over a trace and the search.

#![warn(unreachable_pub)]

pub mod certificate;
pub mod compare;
pub mod derive;
pub mod eval;
pub mod scenario;
pub mod surface;
pub mod vary;
pub mod witness;
pub mod world;

pub use compare::{compare, generated, Comparison, Generated, Stated};
pub use eval::{evaluate, Evaluation, Violation};
pub use vary::{variations, Variation};
pub use witness::{respond, situation, together, witness, Responded, Together, Witnessed};
pub use world::{Moment, Occurrence, World};
