//! smtlib: the syntax of the SMT-LIB language, version 2.7.
//!
//! This crate models the grammar of **The SMT-LIB Standard, Version 2.7**
//! (Clark Barrett, Pascal Fontaine, Cesare Tinelli; release 2026-09-09),
//! <https://smt-lib.org/papers/smt-lib-reference-v2.7-r2026-09-09.pdf>:
//! its lexicon, S-expressions, terms, scripts and responses, as values that
//! are read from text and printed back. It knows nothing of any program
//! that produces or consumes SMT-LIB.
//!
//! | Module | Reference |
//! | - | - |
//! | [`lexicon`] | §3.1 Lexicon: tokens, symbols (`abc` = `|abc|`), keywords, literals, reserved words; dialects |
//! | [`sexpr`] | §3.2 S-expressions: the generic tree, its reader with positions, and its printer |
//! | [`term`] | §3.3 Identifiers, §3.4 Attributes, §3.5 Sorts, §3.6 Terms (with `lambda` and `_` patterns) |
//! | [`command`] | §3.11 Scripts: Figure 3.7 commands, Figure 3.8 options, Figure 3.9 info flags |
//! | [`response`] | §3.11.1 Command responses (Figure 3.10), read by the command they answer |
//!
//! ```
//! use smtlib::{Script, Term};
//!
//! let script: Script = "(declare-fun f (Int) Int) (assert (= (f 1) 2)) (check-sat)".parse().unwrap();
//! let text = script.to_string();
//! assert_eq!(text.parse::<Script>().unwrap(), script);
//!
//! let error = "(assert (f 1)".parse::<Script>().unwrap_err();
//! assert_eq!(error.to_string(), "1:1: syntax error: unbalanced (: the text ends before the matching )");
//! ```
//!
//! # What is modelled
//!
//! Every production of Appendix B is read and printed, with the additions
//! of 2.7 that §1.1.2 lists: `declare-sort-parameter`, `lambda`,
//! `define-const`, the `_` wildcard in match patterns, and
//! `check-sat-assuming` and `get-unsat-assumptions` with terms. Every
//! syntactic category has a type whose values print as text that the
//! reader reads back to an equal value (`to_sexpr`, `to_text`, `write`,
//! `Display`; `from_spanned`, `parse`, `FromStr`), and every `+` of the
//! grammar is a [`NonEmpty`], so a value built through the public API
//! prints as text the grammar accepts. Errors are [`Error`] values with an
//! [`ErrorKind`] and, for text, a line and column; no function panics on
//! any input.
//!
//! # What is not modelled
//!
//! The crate is the grammar and nothing more. It does not check:
//!
//! - whether a term is well sorted, a symbol is declared before use, or an
//!   application matches the rank of a theory symbol (§3.6, §4.2);
//! - whether a script stays in its logic (§3.10, §5.5), or what theories
//!   and logics declare (§3.7–§3.9); no theory or logic is known;
//! - the order of the definitions of a `get-model` answer (§4.2.6);
//! - the values of predefined options and info flags beyond their form
//!   ([`command::SolverOption::classify`] reads the form);
//! - the meaning of a command in a session (§4.1).
//!
//! # Limits
//!
//! - The reader rejects nesting deeper than [`Dialect::max_depth`]
//!   ([`Dialect::DEFAULT_MAX_DEPTH`], 1000, by default) with an error of
//!   kind [`ErrorKind::Depth`]. Reading, printing, traversal and dropping
//!   are iterative and handle any depth; the derived `Clone`, `PartialEq`,
//!   `Hash`, `Ord` and `Debug` recurse, and a value deeper than the reader
//!   admits, built through the API, may exhaust the stack in those.
//! - Response reading assumes, with `:print-success` false, that a command
//!   answered only by `success` succeeded (§4.1.7).
//! - The version is 2.7 only. A 2.6 text is read as far as 2.7 reads it:
//!   the differences of §1.1.2 (new reserved words, terms in
//!   `get-unsat-assumptions`, `lambda`) are not switched off.
//! - Reading and printing are linear in the size of the text, except that
//!   a symbol is checked against the reserved words once per occurrence.
//!
//! # Dialects
//!
//! The default [`Dialect`] is strict SMT-LIB 2.7. A format built on
//! SMT-LIB declares what it adds, and every addition is a dialect
//! extension, not SMT-LIB: characters in simple symbols
//! ([`Dialect::with_symbol_char`]; MoXI writes `x'`), literals `-1`,
//! `-1.5`, `1/2` ([`Dialect::with_extended_literals`], read as
//! [`SpecConstant::Extended`]; Alethe writes them), binders named by a
//! symbol such as `choice` ([`Dialect::with_binder`]), and the nesting
//! limit ([`Dialect::with_max_depth`]). The strict printer writes an
//! extended symbol quoted and an extended literal as the term it
//! abbreviates (`-1` as `(- 1)`).
//!
//! ```
//! use smtlib::{Dialect, Symbol, Term};
//!
//! let dialect = Dialect::strict().with_extended_literals().with_binder(Symbol::new("choice").unwrap()).unwrap();
//! let term = Term::parse_in("(choice ((x Int)) (> x -1))", &dialect).unwrap();
//! assert!(matches!(term, Term::Binder(..)));
//! assert_eq!(term.to_text(&dialect), "(choice ((x Int)) (> x -1))");
//! assert!(Term::parse("(choice ((x Int)) (> x -1))").is_err());
//! ```
//!
//! # Evidence
//!
//! `tests/reference_examples.rs` reads the examples of the reference
//! section by section, the 2.7 examples verbatim, and prints them back;
//! `tests/properties.rs` checks `parse(print(x)) == x` on generated values
//! of every syntax type, deep and large ones included, that the reader
//! never panics on random or mangled text, and that values at the depth
//! limit are read, printed and dropped on a 2 MiB stack;
//! `tests/differential.rs` compares the reader's parse verdict with cvc5
//! and z3 run in parse-only mode, and is ignored, never passed, when a tool
//! is missing.

#![warn(unreachable_pub, missing_docs)]

pub mod command;
mod error;
pub mod lexicon;
mod read;
pub mod response;
pub mod sexpr;
pub mod term;

pub use command::{Command, Script};
pub use error::{Error, ErrorKind, Position, Result};
pub use lexicon::{Dialect, ExtendedConstant, Keyword, Numeral, Reserved, SpecConstant, Symbol};
pub use response::GeneralResponse;
pub use sexpr::{SExpr, Spanned};
pub use term::{Attribute, AttributeValue, Identifier, NonEmpty, Pattern, QualIdentifier, Sort, SortedVar, Term};

/// The examples of the README, run as doctests.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
struct ReadmeExamples;
