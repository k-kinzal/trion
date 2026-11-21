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

mod ground;
mod grounding;
mod instances;
mod key;
mod lexicon;
mod meaning;
mod model;
mod nominal;
mod normal;
mod priority;
mod rules;
mod signatures;
mod temporal;
pub mod typed;
mod vocabulary;

pub use ground::{AtomOf, Fact, Individuals, InstanceOf, OutsideOf, ShareOf};
pub use grounding::Silence;
pub use lexicon::Lexicon;
pub use model::{Applied, Constraint, ConstraintKind, Extent, Model};
pub use priority::{Preference, Priority, ReaderQuery};
pub use rules::rules;
pub use temporal::Obligation;
pub use vocabulary::{glossary, occurrences, Derivation as VocabDerivation, GlossaryDerivation, GlossaryEntry, ResolvedSymbol, VocabEntry};
pub use nominal::mappable_nominal;

/// The sentences that the declarations of individuals generate: the set
/// with each statement about declared types replaced by its instances, each
/// a sentence about named individuals. `None` when the set declares no
/// type. A declaration of individuals is no part of a sentence: it stands
/// in a file and writes sentences, and each of them is read alone.
pub fn generated(set: &crate::SpecSet, lex: &Lexicon, scope: usize) -> Option<crate::SpecSet> {
    ground::apply(set, &lex.without_aliases(), scope).map(|grounded| grounded.set)
}

pub use grounding::silence;
pub use instances::DEFAULT_SCOPE;
pub use meaning::check as check_refinements;
pub use model::{compile, explicit_enumeration, group_formula, match_core, np_key, read_sentence, role_prefix, subject_key, Reading, SUBJECT_VARIABLE};
pub use priority::{authored_condition, check as check_priorities};
pub use rules::entry_lines;
pub use temporal::{continues, is_count, moment_atom, moment_time, at_each_moment, at_every_moment, at_first_moment, diagnostics as temporal_diagnostics, situation_guarantee, unroll, unroll_complete, unroll_complete_in, unroll_axiom, unroll_background, Activation, Trace};
pub use vocabulary::build_table;
