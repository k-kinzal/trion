//! Command responses (§3.11.1, Figure 3.10), so that a client can read
//! what a solver answers.
//!
//! The grammar of responses is ambiguous without the command that was sent:
//! `(a b)` is an unsat core, unsat assumptions, or a proof. A response is
//! therefore read for a given [`Command`] with [`GeneralResponse::parse`]:
//! `success`, `unsupported` and `(error ⟨string⟩)` are accepted for every
//! command, and the specific success response of Figure 3.10 for the
//! commands that have one (§3.11.1, "Specific Responses").
//!
//! SMT-LIB 2.7 changed two responses (§1.1.2): `get-unsat-assumptions`
//! answers with terms, since `check-sat-assuming` takes terms, and a
//! `get-model` answer may not refer forward (§4.2.6). The reader follows
//! the grammar of Figure 3.10, which does not express the second rule, and
//! leaves it to the reader of the model.
//!
//! The terms of a response are read in the dialect given to the reader
//! ([`GeneralResponse::parse_kind`], [`GeneralResponse::from_spanned_in`],
//! [`GeneralResponse::parse_session`]).
//!
//! ```
//! use smtlib::{Command, Dialect, GeneralResponse, Script};
//! use smtlib::response::{CheckSatResponse, SpecificSuccessResponse};
//!
//! let script = Script::parse("(declare-const x Int) (check-sat) (get-value (x))").unwrap();
//! let answers = GeneralResponse::parse_session("sat ((x 1))", script.commands(), false, &Dialect::strict()).unwrap();
//! assert_eq!(answers[0], GeneralResponse::Specific(SpecificSuccessResponse::CheckSat(CheckSatResponse::Sat)));
//! assert_eq!(answers[1].to_string(), "((x 1))");
//! ```
//!
//! As with options, the predefined `⟨info_response⟩` alternatives are
//! attributes of particular forms, so an info response is kept as an
//! [`Attribute`] and [`InfoResponse::classify`] gives the typed view.

use crate::command::{Command, FunctionDec, FunctionDef};
use crate::error::{Error, ErrorKind, Position, Result};
use crate::lexicon::{Dialect, Numeral, Reserved, SpecConstant, StringLiteral, Symbol};
use crate::read;
use crate::sexpr::{read as read_one, Atom, SExpr, Spanned, SpannedKind};
use crate::term::{Attribute, AttributeValue, NonEmpty, Term};
use std::fmt;

/// `sat | unsat | unknown`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CheckSatResponse {
    /// `sat`
    Sat,
    /// `unsat`
    Unsat,
    /// `unknown`
    Unknown,
}

impl CheckSatResponse {
    fn as_str(self) -> &'static str {
        match self {
            CheckSatResponse::Sat => "sat",
            CheckSatResponse::Unsat => "unsat",
            CheckSatResponse::Unknown => "unknown",
        }
    }
}

/// `⟨model_response⟩`: one definition of a `get-model` response.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ModelResponse {
    /// `(define-fun ⟨function_def⟩)`
    DefineFun(FunctionDef),
    /// `(define-fun-rec ⟨function_def⟩)`
    DefineFunRec(FunctionDef),
    /// `(define-funs-rec (⟨function_dec⟩…) (⟨term⟩…))`
    DefineFunsRec(NonEmpty<(FunctionDec, Term)>),
}

/// A `⟨specific_success_response⟩` of Figure 3.10.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SpecificSuccessResponse {
    /// For `check-sat` and `check-sat-assuming`.
    CheckSat(CheckSatResponse),
    /// For `echo`.
    Echo(StringLiteral),
    /// For `get-assertions`: `( ⟨term⟩* )`.
    GetAssertions(Vec<Term>),
    /// For `get-assignment`: `( ( ⟨symbol⟩ ⟨b_value⟩ )* )`.
    GetAssignment(Vec<(Symbol, bool)>),
    /// For `get-info`: `( ⟨info_response⟩+ )`.
    GetInfo(NonEmpty<Attribute>),
    /// For `get-model`: `( ⟨model_response⟩* )`.
    GetModel(Vec<ModelResponse>),
    /// For `get-option`: `⟨attribute_value⟩`.
    GetOption(AttributeValue),
    /// For `get-proof`: `⟨s_expr⟩`.
    GetProof(SExpr),
    /// For `get-unsat-assumptions`: `( ⟨term⟩* )` (SMT-LIB 2.7).
    GetUnsatAssumptions(Vec<Term>),
    /// For `get-unsat-core`: `( ⟨symbol⟩* )`.
    GetUnsatCore(Vec<Symbol>),
    /// For `get-value`: `( ( ⟨term⟩ ⟨term⟩ )+ )`.
    GetValue(NonEmpty<(Term, Term)>),
}

/// A `⟨general_response⟩` of Figure 3.10.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GeneralResponse {
    /// `success`
    Success,
    /// A command-specific response.
    Specific(SpecificSuccessResponse),
    /// `unsupported`
    Unsupported,
    /// `(error ⟨string⟩)`
    Error(StringLiteral),
}

/// The kind of specific response a command expects (§3.11.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ResponseKind {
    /// Only `success`, `unsupported` or `(error …)`.
    General,
    /// `check-sat`, `check-sat-assuming`.
    CheckSat,
    /// `echo`.
    Echo,
    /// `get-assertions`.
    GetAssertions,
    /// `get-assignment`.
    GetAssignment,
    /// `get-info`.
    GetInfo,
    /// `get-model`.
    GetModel,
    /// `get-option`.
    GetOption,
    /// `get-proof`.
    GetProof,
    /// `get-unsat-assumptions`.
    GetUnsatAssumptions,
    /// `get-unsat-core`.
    GetUnsatCore,
    /// `get-value`.
    GetValue,
}

impl ResponseKind {
    /// The response kind of `command`.
    pub fn of(command: &Command) -> ResponseKind {
        match command {
            Command::CheckSat | Command::CheckSatAssuming(_) => ResponseKind::CheckSat,
            Command::Echo(_) => ResponseKind::Echo,
            Command::GetAssertions => ResponseKind::GetAssertions,
            Command::GetAssignment => ResponseKind::GetAssignment,
            Command::GetInfo(_) => ResponseKind::GetInfo,
            Command::GetModel => ResponseKind::GetModel,
            Command::GetOption(_) => ResponseKind::GetOption,
            Command::GetProof => ResponseKind::GetProof,
            Command::GetUnsatAssumptions => ResponseKind::GetUnsatAssumptions,
            Command::GetUnsatCore => ResponseKind::GetUnsatCore,
            Command::GetValue(_) => ResponseKind::GetValue,
            _ => ResponseKind::General,
        }
    }
}

fn symbol_sexpr(name: &str) -> SExpr {
    SExpr::symbol(Symbol::new(name).unwrap_or_else(|_| unreachable!("{name} is a symbol")))
}

impl ModelResponse {
    /// The S-expression of this definition.
    pub fn to_sexpr(&self) -> SExpr {
        match self {
            ModelResponse::DefineFun(def) => {
                let mut items = vec![SExpr::reserved(Reserved::DefineFun)];
                def.push_sexprs(&mut items);
                SExpr::List(items)
            }
            ModelResponse::DefineFunRec(def) => {
                let mut items = vec![SExpr::reserved(Reserved::DefineFunRec)];
                def.push_sexprs(&mut items);
                SExpr::List(items)
            }
            ModelResponse::DefineFunsRec(pairs) => SExpr::List(vec![
                SExpr::reserved(Reserved::DefineFunsRec),
                SExpr::List(pairs.iter().map(|(d, _)| d.to_sexpr()).collect()),
                SExpr::List(pairs.iter().map(|(_, t)| t.to_sexpr()).collect()),
            ]),
        }
    }

    /// Reads one definition of a model in `dialect`.
    pub fn from_spanned_in(node: &Spanned, dialect: &Dialect) -> Result<ModelResponse> {
        let items = node.expect_list("a model response ( define-fun … )")?;
        let Some((head, rest)) = items.split_first() else {
            return Err(node.expected("a model response"));
        };
        match head.as_reserved() {
            Some(Reserved::DefineFun) => Ok(ModelResponse::DefineFun(FunctionDef::from_spanned_items(node, rest, dialect)?)),
            Some(Reserved::DefineFunRec) => Ok(ModelResponse::DefineFunRec(FunctionDef::from_spanned_items(node, rest, dialect)?)),
            Some(Reserved::DefineFunsRec) => {
                read::arity(node, rest, 2, "define-funs-rec")?;
                let decs = rest[0].expect_list("a list of function declarations")?.iter().map(FunctionDec::from_spanned).collect::<Result<Vec<_>>>()?;
                let bodies = rest[1].expect_list("a list of terms")?.iter().map(|t| Term::from_spanned_in(t, dialect)).collect::<Result<Vec<_>>>()?;
                if decs.len() != bodies.len() || decs.is_empty() {
                    return Err(node.error("define-funs-rec needs as many bodies as declarations, at least one"));
                }
                Ok(ModelResponse::DefineFunsRec(NonEmpty::try_from(decs.into_iter().zip(bodies).collect::<Vec<_>>()).map_err(|e| e.or_at(node.position()))?))
            }
            _ => Err(head.expected("define-fun, define-fun-rec or define-funs-rec")),
        }
    }
}

impl SpecificSuccessResponse {
    /// The S-expression of this response.
    pub fn to_sexpr(&self) -> SExpr {
        match self {
            SpecificSuccessResponse::CheckSat(r) => symbol_sexpr(r.as_str()),
            SpecificSuccessResponse::Echo(s) => SExpr::constant(SpecConstant::String(s.clone())),
            SpecificSuccessResponse::GetAssertions(terms) => SExpr::List(terms.iter().map(Term::to_sexpr).collect()),
            SpecificSuccessResponse::GetAssignment(pairs) => SExpr::List(pairs.iter().map(|(s, b)| SExpr::List(vec![SExpr::symbol(s.clone()), symbol_sexpr(if *b { "true" } else { "false" })])).collect()),
            SpecificSuccessResponse::GetInfo(attributes) => {
                let mut items = Vec::new();
                for attribute in attributes {
                    attribute.push_sexprs(&mut items);
                }
                SExpr::List(items)
            }
            SpecificSuccessResponse::GetModel(definitions) => SExpr::List(definitions.iter().map(ModelResponse::to_sexpr).collect()),
            SpecificSuccessResponse::GetOption(value) => value.to_sexpr(),
            SpecificSuccessResponse::GetProof(proof) => proof.clone(),
            SpecificSuccessResponse::GetUnsatAssumptions(terms) => SExpr::List(terms.iter().map(Term::to_sexpr).collect()),
            SpecificSuccessResponse::GetUnsatCore(symbols) => SExpr::List(symbols.iter().cloned().map(SExpr::symbol).collect()),
            SpecificSuccessResponse::GetValue(pairs) => SExpr::List(pairs.iter().map(|(t, v)| SExpr::List(vec![t.to_sexpr(), v.to_sexpr()])).collect()),
        }
    }

    /// The kind of this response.
    pub fn kind(&self) -> ResponseKind {
        match self {
            SpecificSuccessResponse::CheckSat(_) => ResponseKind::CheckSat,
            SpecificSuccessResponse::Echo(_) => ResponseKind::Echo,
            SpecificSuccessResponse::GetAssertions(_) => ResponseKind::GetAssertions,
            SpecificSuccessResponse::GetAssignment(_) => ResponseKind::GetAssignment,
            SpecificSuccessResponse::GetInfo(_) => ResponseKind::GetInfo,
            SpecificSuccessResponse::GetModel(_) => ResponseKind::GetModel,
            SpecificSuccessResponse::GetOption(_) => ResponseKind::GetOption,
            SpecificSuccessResponse::GetProof(_) => ResponseKind::GetProof,
            SpecificSuccessResponse::GetUnsatAssumptions(_) => ResponseKind::GetUnsatAssumptions,
            SpecificSuccessResponse::GetUnsatCore(_) => ResponseKind::GetUnsatCore,
            SpecificSuccessResponse::GetValue(_) => ResponseKind::GetValue,
        }
    }

    fn from_spanned_in(node: &Spanned, kind: ResponseKind, dialect: &Dialect) -> Result<SpecificSuccessResponse> {
        let term = |t: &Spanned| Term::from_spanned_in(t, dialect);
        let symbols = |node: &Spanned| -> Result<Vec<Symbol>> { node.expect_list("a list of symbols")?.iter().map(|s| s.expect_symbol("a symbol").cloned()).collect() };
        Ok(match kind {
            ResponseKind::General => return Err(node.expected("success, unsupported or (error ⟨string⟩)")),
            ResponseKind::CheckSat => match node.as_symbol().map(Symbol::as_str) {
                Some("sat") => SpecificSuccessResponse::CheckSat(CheckSatResponse::Sat),
                Some("unsat") => SpecificSuccessResponse::CheckSat(CheckSatResponse::Unsat),
                Some("unknown") => SpecificSuccessResponse::CheckSat(CheckSatResponse::Unknown),
                _ => return Err(node.expected("sat, unsat or unknown")),
            },
            ResponseKind::Echo => SpecificSuccessResponse::Echo(node.expect_string("a string literal")?.clone()),
            ResponseKind::GetAssertions => SpecificSuccessResponse::GetAssertions(node.expect_list("a list of terms")?.iter().map(term).collect::<Result<_>>()?),
            ResponseKind::GetAssignment => SpecificSuccessResponse::GetAssignment(
                node.expect_list("a list of truth assignments")?
                    .iter()
                    .map(|pair| match pair.as_list() {
                        Some([s, b]) => {
                            let value = AttributeValue::from_spanned(b).as_ref().and_then(AttributeValue::as_bool).ok_or_else(|| b.expected("true or false"))?;
                            Ok((s.expect_symbol("a label")?.clone(), value))
                        }
                        _ => Err(pair.expected("( ⟨symbol⟩ ⟨b_value⟩ )")),
                    })
                    .collect::<Result<_>>()?,
            ),
            ResponseKind::GetInfo => {
                let items = node.expect_list("a list of info responses")?;
                let attributes = Attribute::sequence_from_spanned(items)?;
                SpecificSuccessResponse::GetInfo(NonEmpty::new(attributes).ok_or_else(|| node.error("a get-info response has at least one info response"))?)
            }
            ResponseKind::GetModel => SpecificSuccessResponse::GetModel(node.expect_list("a list of model responses")?.iter().map(|m| ModelResponse::from_spanned_in(m, dialect)).collect::<Result<_>>()?),
            ResponseKind::GetOption => SpecificSuccessResponse::GetOption(AttributeValue::from_spanned(node).ok_or_else(|| node.expected("an attribute value"))?),
            ResponseKind::GetProof => SpecificSuccessResponse::GetProof(node.to_sexpr()),
            ResponseKind::GetUnsatAssumptions => SpecificSuccessResponse::GetUnsatAssumptions(node.expect_list("a list of terms")?.iter().map(term).collect::<Result<_>>()?),
            ResponseKind::GetUnsatCore => SpecificSuccessResponse::GetUnsatCore(symbols(node)?),
            ResponseKind::GetValue => {
                let pairs = node.expect_list("a list of valuation pairs")?
                    .iter()
                    .map(|pair| match pair.as_list() {
                        Some([t, v]) => Ok((term(t)?, term(v)?)),
                        _ => Err(pair.expected("a valuation pair ( ⟨term⟩ ⟨term⟩ )")),
                    })
                    .collect::<Result<Vec<_>>>()?;
                SpecificSuccessResponse::GetValue(NonEmpty::new(pairs).ok_or_else(|| node.error("a get-value response has at least one pair"))?)
            }
        })
    }
}

impl GeneralResponse {
    /// The S-expression of this response.
    pub fn to_sexpr(&self) -> SExpr {
        match self {
            GeneralResponse::Success => symbol_sexpr("success"),
            GeneralResponse::Unsupported => symbol_sexpr("unsupported"),
            GeneralResponse::Error(message) => SExpr::List(vec![symbol_sexpr("error"), SExpr::constant(SpecConstant::String(message.clone()))]),
            GeneralResponse::Specific(specific) => specific.to_sexpr(),
        }
    }

    /// The text of this response in `dialect`.
    pub fn to_text(&self, dialect: &Dialect) -> String {
        self.to_sexpr().to_text(dialect)
    }

    /// Reads the response to `command` from `text` (one S-expression) in
    /// strict SMT-LIB 2.7.
    pub fn parse(text: &str, command: &Command) -> Result<GeneralResponse> {
        GeneralResponse::parse_kind(text, ResponseKind::of(command), &Dialect::strict())
    }

    /// Reads a response of `kind` from `text` in `dialect`.
    pub fn parse_kind(text: &str, kind: ResponseKind, dialect: &Dialect) -> Result<GeneralResponse> {
        GeneralResponse::from_spanned_in(&read_one(text, dialect)?, kind, dialect)
    }

    /// Reads a response of `kind` from a spanned tree in strict SMT-LIB 2.7.
    pub fn from_spanned(node: &Spanned, kind: ResponseKind) -> Result<GeneralResponse> {
        GeneralResponse::from_spanned_in(node, kind, &Dialect::strict())
    }

    /// Reads a response of `kind` from a spanned tree, with its terms in
    /// `dialect`.
    ///
    /// `success`, `unsupported` and `(error s)` are read as the general
    /// responses even where the specific grammar would also admit them (a
    /// get-proof response is any S-expression), because §4.1.2 gives these
    /// three their general meaning for every command.
    pub fn from_spanned_in(node: &Spanned, kind: ResponseKind, dialect: &Dialect) -> Result<GeneralResponse> {
        match node.kind() {
            SpannedKind::Atom(Atom::Symbol(s)) if s.as_str() == "success" => return Ok(GeneralResponse::Success),
            SpannedKind::Atom(Atom::Symbol(s)) if s.as_str() == "unsupported" => return Ok(GeneralResponse::Unsupported),
            SpannedKind::List(items) if items.first().and_then(Spanned::as_symbol).is_some_and(|s| s.as_str() == "error") => {
                return match items.as_slice() {
                    [_, message] => Ok(GeneralResponse::Error(message.expect_string("an error message (a string literal)")?.clone())),
                    _ => Err(node.expected("( error ⟨string⟩ )")),
                };
            }
            _ => {}
        }
        SpecificSuccessResponse::from_spanned_in(node, kind, dialect).map(GeneralResponse::Specific)
    }

    /// Reads the responses a solver printed for `commands`, in order, with
    /// their terms in `dialect`.
    ///
    /// With `print_success` true every command has exactly one response.
    /// With it false (§4.1.7), a command whose only successful response is
    /// `success` prints nothing when it succeeds; this reader then assumes
    /// that each such command succeeded, so an `(error …)` printed for one of
    /// them is reported as a mismatch rather than attributed to it.
    pub fn parse_session(text: &str, commands: &[Command], print_success: bool, dialect: &Dialect) -> Result<Vec<GeneralResponse>> {
        let nodes = crate::sexpr::read_all(text, dialect)?;
        let mut next = nodes.iter();
        let mut out = Vec::new();
        for command in commands {
            let kind = ResponseKind::of(command);
            if kind == ResponseKind::General && !print_success {
                continue;
            }
            let Some(node) = next.next() else {
                return Err(Error::at(ErrorKind::Syntax, Position::START.advance(text), format!("the responses end before the response to {}", command.name())));
            };
            out.push(GeneralResponse::from_spanned_in(node, kind, dialect)?);
        }
        if let Some(extra) = next.next() {
            return Err(Error::at(ErrorKind::Syntax, extra.position(), "more responses than commands"));
        }
        Ok(out)
    }
}

impl fmt::Display for GeneralResponse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_sexpr().fmt(f)
    }
}

/// `immediate-exit | continued-execution`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorBehavior {
    /// `immediate-exit`
    ImmediateExit,
    /// `continued-execution`
    ContinuedExecution,
}

/// `memout | incomplete | ⟨s_expr⟩`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ReasonUnknown {
    /// `memout`
    Memout,
    /// `incomplete`
    Incomplete,
    /// A solver-defined reason.
    Other(SExpr),
}

/// The typed view of an `⟨info_response⟩` (Figure 3.10).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum InfoResponse {
    /// `:assertion-stack-levels ⟨numeral⟩`
    AssertionStackLevels(Numeral),
    /// `:authors ⟨string⟩`
    Authors(StringLiteral),
    /// `:error-behavior ⟨error-behavior⟩`
    ErrorBehavior(ErrorBehavior),
    /// `:name ⟨string⟩`
    Name(StringLiteral),
    /// `:reason-unknown ⟨reason-unknown⟩`
    ReasonUnknown(ReasonUnknown),
    /// `:version ⟨string⟩`
    Version(StringLiteral),
    /// Any other attribute (solver-specific information, statistics).
    Other(Attribute),
}

impl InfoResponse {
    /// The typed view of `attribute`.
    pub fn classify(attribute: &Attribute) -> InfoResponse {
        let value = attribute.value();
        let string = match value {
            Some(AttributeValue::Constant(SpecConstant::String(s))) => Some(s.clone()),
            _ => None,
        };
        let symbol = match value {
            Some(AttributeValue::Symbol(s)) => Some(s.as_str()),
            _ => None,
        };
        let typed = match attribute.keyword().name() {
            "assertion-stack-levels" => match value {
                Some(AttributeValue::Constant(SpecConstant::Numeral(n))) => Some(InfoResponse::AssertionStackLevels(n.clone())),
                _ => None,
            },
            "authors" => string.map(InfoResponse::Authors),
            "name" => string.map(InfoResponse::Name),
            "version" => string.map(InfoResponse::Version),
            "error-behavior" => match symbol {
                Some("immediate-exit") => Some(InfoResponse::ErrorBehavior(ErrorBehavior::ImmediateExit)),
                Some("continued-execution") => Some(InfoResponse::ErrorBehavior(ErrorBehavior::ContinuedExecution)),
                _ => None,
            },
            "reason-unknown" => value.map(|v| {
                InfoResponse::ReasonUnknown(match symbol {
                    Some("memout") => ReasonUnknown::Memout,
                    Some("incomplete") => ReasonUnknown::Incomplete,
                    _ => ReasonUnknown::Other(v.to_sexpr()),
                })
            }),
            _ => None,
        };
        typed.unwrap_or_else(|| InfoResponse::Other(attribute.clone()))
    }
}
