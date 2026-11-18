//! moxi: reading and writing MoXI, the model checking intermediate language.
//!
//! This crate models the grammar of **MoXI — A Model Checking Intermediate
//! Language (Draft)** (Cesare Tinelli et al.; front matter dated
//! 2024-03-16), `description.md` of <https://github.com/ModelChecker/IL> at
//! commit `b5156d5ead225fceb37a40b1ec337968ea2c767b` (2025-03-31, the last
//! commit that changed the file when it was downloaded on 2026-11-16).
//! Section names below are the headings of that document. MoXI extends
//! SMT-LIB; its lexicon, S-expressions, sorts and terms are those of the
//! `smtlib` crate (The SMT-LIB Standard Version 2.7), read in a dialect that
//! admits `'` in simple symbols ([`dialect`]).
//!
//! | Module | Reference |
//! | - | - |
//! | [`syntax`] | "Supported SMT-LIB Commands", "MoXI-specific Commands", "System Definition Command" (atomic and composite systems), "System Checking Command" |
//! | [`response`] | "Check-system Response", "Verbose Response", "Compact Response" |
//!
//! Each module gives the abstract syntax, a reader (`FromStr`: text to
//! syntax; errors are [`Error`] values with an [`ErrorKind`] and a line and
//! column) and a printer (`Display`; total, and its text reads back to an
//! equal value). The syntax types have private fields; their constructors
//! reject what the reader could not have produced, so that the printer's
//! text always reads back.
//!
//! ```
//! use moxi::{Command, Script};
//!
//! let script: Script = "(set-logic QF_LIA)
//! (define-system Delay :input ((i Int)) :output ((o Int))
//!   :init (= o 0)
//!   :trans (= o' i))
//! (check-system Delay :input ((i Int)) :output ((o Int))
//!   :reachable (r (> o 3))
//!   :query (q (r)))".parse()?;
//! let Command::DefineSystem(delay) = &script.commands()[1] else { unreachable!() };
//! assert_eq!(delay.trans().map(|t| t.to_text(&moxi::dialect())), Some("(= o' i)".to_string()));
//! assert_eq!(script.to_string().parse::<Script>()?, script);
//! # Ok::<(), moxi::Error>(())
//! ```
//!
//! # Scope: the grammar only
//!
//! The crate reads and writes MoXI; it does not check its static semantics.
//! A script it reads may still be rejected by a MoXI tool because a name is
//! undeclared or declared twice, a formula is not of sort Bool, a primed
//! variable occurs where the attribute does not admit it, a subsystem does
//! not match the system it instantiates, a query names a formula that does
//! not exist, an operator has the wrong number of arguments (`(and x)`), or
//! a term is outside the logic of `set-logic`. A program that produces
//! MoXI should run its output through such a tool (the reference is the
//! sort checker of moxi-mc-flow) in its own tests.
//!
//! What the reader does enforce is what the grammar of the document states:
//!
//! - Commands: the five SMT-LIB commands MoXI adopts (`set-logic`,
//!   `declare-sort`, `define-sort`, `declare-const`, `define-fun`) and
//!   `declare-enum-sort`, `define-system`, `check-system`. Any other SMT-LIB
//!   command (including `declare-fun`, `declare-datatype`, `assert`, and the
//!   2.7 commands `define-const` and `declare-sort-parameter`) is rejected
//!   as [`ErrorKind::Unsupported`], because "Supported SMT-LIB Commands"
//!   lists the commands MoXI adopts and they are not among them; any other
//!   head is a [`ErrorKind::Syntax`] error.
//! - Attributes: each attribute of `define-system` and `check-system` the
//!   document defines, with the value shape it gives; at most once where
//!   the document says so; `:input`, `:output` and `:local` before the
//!   other attributes, and in `define-system` every `:subsys` before
//!   `:init`, `:trans` and `:inv`; `:queries` with at least one query.
//! - Terms and sorts: those of SMT-LIB 2.6, read by `smtlib`. The
//!   productions SMT-LIB 2.7 added to the term grammar — `lambda` and the
//!   `_` wildcard pattern of `match` — are rejected as
//!   [`ErrorKind::Unsupported`]: the document builds on "the SMT-LIB
//!   language" with "many-sorted first-order logic with equality and let
//!   binders" as its base logic ("Technical Preliminaries"). `@` and `->`
//!   are symbols in the grammar of both versions and are read; that 2.7
//!   gives them a higher-order meaning is theory, not grammar. `match` and
//!   annotations such as `:named` are SMT-LIB 2.6 terms and are read;
//!   whether a script may use them (MoXI adopts no datatype command) is
//!   static semantics.
//! - Responses: the shape of the document's example (see [`response`]).
//! - Nesting: at most the limit of the [`dialect`] (`smtlib`'s default);
//!   deeper text is an [`ErrorKind::Depth`] error.
//!
//! # Lexical interpretations
//!
//! A quoted symbol followed by `'` (`|x|'`) is two tokens, as in the SMT-LIB
//! lexicon (the next-state copy of `|x|` is `|x'|` or `x'`); the typographic
//! quote `’` that some examples of the document use is not the prime `'`
//! and is a lexical error; command names such as `reset` are reserved
//! words of SMT-LIB (§3.1) and cannot be variable names.
//!
//! # Evidence
//!
//! `tests/description_examples.rs` reads the examples of the document,
//! verbatim, section by section, and states for each whether it is read
//! and, if not, which rule of the grammar it breaks; `tests/reader.rs`
//! takes the reader's rules one by one; `tests/properties.rs` checks
//! `parse(print(x)) == x` on generated syntax (including deep and large
//! values) and that the reader returns an error, never panics, on random
//! and mangled text; `tests/differential.rs` compares the reader and the
//! printer with the reference tool moxi-mc-flow
//! (<https://github.com/ModelChecker/moxi-mc-flow>, commit
//! `b61c98188d246e157a6f5f759b012749855b8fbc`) on its corpus and on
//! generated scripts. The differential tests are ignored by default; they
//! run with `cargo test -- --include-ignored` and read the tool from
//! `.tools/moxi-mc-flow` in the repository or from the directory the
//! environment variable `MOXI_MC_FLOW` names (it is GPLv3; none of its files
//! is copied into the crate).

#![warn(missing_docs, unreachable_pub)]

mod error;
pub mod response;
pub mod syntax;
mod validate;

pub use error::{Error, ErrorKind, Result};
pub use response::CheckSystemResponse;
pub use smtlib::Position;
pub use syntax::{dialect, parse_term, CheckAttribute, CheckSystem, Command, Condition, ConditionKind, DeclareConst, DefineFun, DefineSort, DefineSystem, Query, Script, Subsystem};

/// The example of the README, as a doctest.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
struct ReadmeDoctests;
