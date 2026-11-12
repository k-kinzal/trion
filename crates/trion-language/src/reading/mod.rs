//! Reading: the statements of a set become contracts.
//!
//! This module is the interface between the language and a verifier.
//!
//! [`compile`] reads every statement of a set as assume-guarantee contracts
//! over the terms that the [`Lexicon`] of the set resolves, and returns them
//! as a [`Model`] together with what each statement says about time, about
//! terms and about other statements. [`unroll`] states the contracts of a
//! model over a trace of moments, which is what a decision is made over.
//!
//! Beside the model stand the accounts of the reading: the vocabulary of the
//! set ([`build_table`], [`glossary`]), the reading rules that read a
//! sentence ([`rules()`]) and what the set says without constraining anything
//! ([`silence`]).

mod grounding;
mod instances;
mod key;
mod lexicon;
mod meaning;
mod model;
mod priority;
mod rules;
mod temporal;
mod vocabulary;

pub use grounding::Silence;
pub use lexicon::Lexicon;
pub use model::{Applied, Constraint, ConstraintKind, Extent, Model};
pub use priority::{Preference, Priority, ReaderQuery};
pub use rules::rules;
pub use temporal::Obligation;
pub use vocabulary::{glossary, occurrences, Derivation as VocabDerivation, GlossaryDerivation, GlossaryEntry, VocabEntry};

pub use grounding::silence;
pub use instances::DEFAULT_SCOPE;
pub use meaning::check as check_refinements;
pub use model::{compile, group_formula, match_core, np_key, role_prefix, subject_key, SUBJECT_VARIABLE};
pub use priority::{authored_condition, check as check_priorities};
pub use rules::entry_lines;
pub use temporal::{at_each_moment, at_every_moment, at_first_moment, diagnostics as temporal_diagnostics, activations, unroll, unroll_axiom, unroll_background, Activation, Trace};
pub use vocabulary::build_table;
