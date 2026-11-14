//! trion-solver: formulas, and whether a set of them has an interpretation.
//!
//! A [`Formula`] is a propositional combination of atoms; an atom is a fact
//! at one moment or a linear comparison of integer quantities. [`Instance`]
//! holds formulas and answers queries over them, and [`Prover`] is the
//! search below it. An [`Answer`] is `satisfiable`, `unsatisfiable` or
//! `unknown`, and the first two carry a [`Certificate`] that another program
//! can check without trusting the search: a witness, or a refutation whose
//! every clause follows by unit propagation or is a linear lemma with its
//! derivation.
//!
//! The search (DPLL over atoms with learned clauses), the encoding and the
//! linear integer arithmetic are private to this crate. The crate knows
//! nothing of sentences: it is given formulas and returns answers.

#![warn(unreachable_pub)]

mod arith;
mod certificate;
mod formula;
mod instance;
mod quantified;

pub use certificate::{decide, Answer, Certificate, Connective, Definition, Justification, Operand, LinearDerivation, LinearSource, Literal, Prover, Quantity, Refutation, Side, Status, Step, Witness, WitnessPart};
pub use formula::{Atom, Cmp, Formula, NUMERIC_SCALE};
pub use instance::{Instance, Lit};
pub use quantified::{for_all_exists, ForAll, Unanswered};
