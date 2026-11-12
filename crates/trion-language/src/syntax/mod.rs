//! The constrained-English surface layer.
//!
//! `ast` and `parse` are taken from spec-oracle's `so_lang`: a total recognizer
//! for EARS-shaped sentences with a lossless syntax tree. The one extension is
//! `Predicate::Enumeration`, which declares the closed set of an attribute.

pub mod ast;
mod forms;
pub(crate) mod parse;
mod reference;
pub mod words;

pub use forms::syntax_forms;
pub use parse::{parse, ParseError};
