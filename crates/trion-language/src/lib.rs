//! trion-language: the trion specification language.
//!
//! A specification is a set of statements in controlled English, and each
//! statement is read as assume-guarantee contracts. This crate turns text
//! into statements and statements into contracts:
//!
//! - [`parse_document`] reads a file into the namespace blocks of a
//!   [`SpecSet`]; [`syntax`] holds the tree of one sentence.
//! - [`expand`] writes a statement out as the controlled English that it
//!   stands for.
//! - [`reading`] reads the statements of a set as a [`Model`] of contracts
//!   over the terms that its [`Lexicon`] resolves, and states the contracts
//!   over a trace of moments.
//!
//! Whether the contracts can all hold is decided by `trion-verification`.
//! This crate reads no file and runs no process.

#![warn(unreachable_pub)]

mod diagnostic;
pub mod document;
pub mod expand;
pub mod reading;
pub mod syntax;

pub use diagnostic::{Diagnostic, Severity, SpecRef, CODES};
pub use document::{parse_document, parse_sentence, parse_statement, scan_imports, Document, Meta, Package, ParsedFile, Spec, SpecSet, VocabularyMode};
pub use reading::{glossary, occurrences, rules, Applied, Constraint, ConstraintKind, Extent, GlossaryDerivation, GlossaryEntry, Lexicon, Model, Obligation, Preference, Priority, Silence, VocabDerivation, VocabEntry};
