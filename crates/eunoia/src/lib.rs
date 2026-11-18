//! eunoia: the Eunoia language of the Ethos proof checker, as abstract syntax,
//! a parser and a printer.
//!
//! # Specification
//!
//! *The Ethos user manual* (`user_manual.md`) at Ethos commit
//! `08e4aa40c4f8a6e00833f10e8d8985777e424027` (Ethos 0.2.5), the version that
//! cvc5 1.4.2 pins in `contrib/get-ethos-checker`;
//! <https://github.com/cvc5/ethos/blob/08e4aa40c4f8a6e00833f10e8d8985777e424027/user_manual.md>.
//! The manual describes Eunoia "as implemented by Ethos" and says that it is
//! not an independent standard; where it leaves a reading open, the Ethos
//! sources at the same commit decide, and each such place cites its file.
//!
//! | Module | Implements |
//! | - | - |
//! | `lexer` (private) | the lexicon (manual "Literal types"; Ethos `src/lexer.cpp`) |
//! | `ast` | the abstract syntax of "Full syntax for Eunoia commands", including binders, `let`/`eo::define` and qualified heads: [`Term`], [`Command`], [`Script`] |
//! | `parser` | text to abstract syntax, errors with line:column: [`parse_script`], [`parse_script_at`], [`parse_term`] |
//! | printer (`Display`) | abstract syntax to text; total, and read back to an equal value |
//!
//! # Supported subset
//!
//! Every command of the manual's grammar `<eo-command>` and `<common-command>`
//! is parsed and printed: `assume`, `assume-push`, `step`, `step-pop`,
//! `declare-const`, `declare-parameterized-const`, `declare-consts`,
//! `declare-datatype`, `declare-datatypes`, `declare-sort`, `declare-rule`,
//! `define`, `program`, `include`, `reference`, `echo`, `exit`, `reset`,
//! `set-option`. The commands of reference files (`<smtlib2-command>`, which
//! are SMT-LIB) are not part of this crate.
//!
//! Not supported, with an error that says so: quoted symbols that spell a
//! builtin word (`|Bool|`, `|let|`, ...) and the literals `-.5` and `-/5`.
//! The commands `declare-type`, `define-type` and `declare-oracle-fun` and the
//! `oracle` construct of earlier Ethos versions were removed in Ethos 0.2.1
//! (`NEWS.md`) and are not part of this version of the language.
//!
//! `set-option` follows the manual's grammar, `(set-option <attr>)` with
//! `<attr> ::= <keyword> <term>?`; Ethos's own reader
//! (`src/cmd_parser.cpp`, `SET_OPTION`) accepts any s-expression after the
//! keyword, which this crate refuses where it is not a term.
//!
//! # Grammar only
//!
//! The crate reads and writes the language; it gives no meaning to a script.
//! Nothing it does depends on declarations: a symbol that is used before it
//! is declared, a step that names no rule of the signature, a premise that is
//! not in scope, an `include` of a missing file all read and print as written.
//! What is in the types is what the grammar states (for instance, a symbol
//! is never empty and a literal is one of its category). Whether a script is
//! well formed and valid is for Ethos to say: the tests run Ethos on the
//! printed form of Ethos's own regression tests (see below).
//!
//! # Example
//!
//! ```
//! use eunoia::{parse_script, Command, ParseErrorKind, Position};
//!
//! let text = "(declare-const p Bool)\n(assume @p1 p)\n(step @p2 p :rule refl :premises (@p1))";
//! let script = parse_script(text)?;
//! assert!(matches!(&script.commands()[2], Command::Step(s) if s.rule.as_str() == "refl"));
//! assert_eq!(script.position(2), Some(Position::new(3, 1)));
//! // printing reads back to an equal script
//! assert_eq!(parse_script(&script.to_string())?, script);
//!
//! let err = parse_script("(assume @p1 (and p q)").unwrap_err();
//! assert!(matches!(err.kind, ParseErrorKind::UnexpectedEnd { .. }));
//! assert_eq!(err.to_string(), "1:22: unexpected end of input, expected `)`");
//! # Ok::<(), eunoia::ParseError>(())
//! ```
//!
//! # Robustness
//!
//! Terms nest without limit: the parser, the printer and the traits of
//! [`Term`] (`Clone`, `PartialEq`, `Hash`, `Debug`, `Display`, `Drop`) work
//! with explicit stacks, as Ethos's parser does (`src/expr_parser.cpp`). No
//! input makes a function of this crate panic; a property test feeds random
//! and mangled text to the parser to back that claim. Reading is linear in
//! the length of the text.
//!
//! # Inputs of the tests
//!
//! The crate contains no file of Ethos. The conformance tests read the
//! manual's examples and Ethos's regression tests from the Ethos sources at
//! the pinned commit, and run the Ethos binary of that commit; they look for
//! the sources in `$EUNOIA_ETHOS_SOURCES`, else in the repository's
//! `.tools/ethos-08e4aa40c4f8a6e00833f10e8d8985777e424027` (`user_manual.md`,
//! `tests/`), and for `ethos` in the repository's `.tools/bin`, then on
//! `PATH`. Without them, those tests print what they need and pass without
//! checking; with `EUNOIA_REQUIRE_INPUTS=1` they fail instead, and an Ethos
//! of another version always fails them.
#![warn(unreachable_pub)]

/// The examples of `README.md`, compiled and run as doctests.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
struct ReadmeDoctests;

mod ast;
mod error;
mod lexer;
mod parser;

pub use ast::{Annotation, Application, Attribute, Command, ConstructorDec, DatatypeDec, Keyword, LetForm, LetTerm, Literal, LiteralCategory, NonEmpty, ProgramDecl, RuleConclusion, RuleDecl, RulePremises, Script, Step, StrLit, Symbol, Term, TypedParam};
pub use error::{AstError, AstErrorKind, Found, LiteralProblem, ParseError, ParseErrorKind, Position, SyntaxProblem, UnsupportedConstruct};
pub use parser::{parse_script, parse_script_at, parse_term};
