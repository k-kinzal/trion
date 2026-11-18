//! Errors: values that say what is wrong and where.
//!
//! Two kinds of failure are kept apart: an [`AstError`] is a value that no
//! Eunoia text can denote (refused by a constructor of the abstract syntax),
//! and a [`ParseError`] is a text that is not in the grammar of the manual
//! ("Full syntax for Eunoia commands").

use std::fmt;

use crate::ast::{Keyword, LiteralCategory};

/// A position in a text: line and column, both counted from 1, the column in
/// characters (Unicode scalar values).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Position {
    /// The line, from 1.
    pub line: u32,
    /// The column in characters, from 1.
    pub column: u32,
}

impl Position {
    /// The first character of a text.
    pub const START: Position = Position { line: 1, column: 1 };

    /// The position at `line` and `column`.
    pub fn new(line: u32, column: u32) -> Position {
        Position { line, column }
    }
}

impl Default for Position {
    fn default() -> Self {
        Position::START
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// Why a value is refused by a constructor of the abstract syntax: no text in
/// the grammar denotes it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum AstErrorKind {
    /// No element where the grammar has `<x>+`.
    Empty,
    /// A symbol that contains `|`, which no quoting can write.
    SymbolWithBar,
    /// A symbol that is a reserved word of Eunoia.
    ReservedWord(&'static str),
    /// A keyword whose name is not a simple symbol.
    NotAKeyword,
    /// A rational literal with denominator zero.
    ZeroDenominator,
    /// A string literal with a character outside ASCII (write it as an escape
    /// sequence).
    NonAsciiString,
    /// `true` and `false` are symbols, not literals.
    BooleanLiteral,
    /// A text that is not a literal of the category.
    NotALiteral(LiteralCategory),
    /// The head of an application is neither a symbol nor an application of
    /// `_` or `as`.
    ApplicationHead,
    /// An application without arguments.
    NoArguments,
    /// An empty variable list.
    EmptyVariableList,
    /// A variable list whose first variable is `_` or `as`, which would read
    /// as a qualified head.
    QualifierVariable,
}

impl fmt::Display for AstErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AstErrorKind::Empty => f.write_str("the grammar requires at least one element here"),
            AstErrorKind::SymbolWithBar => f.write_str("a symbol cannot contain `|`"),
            AstErrorKind::ReservedWord(w) => write!(f, "`{w}` is a reserved word"),
            AstErrorKind::NotAKeyword => f.write_str("the name of a keyword must be a simple symbol"),
            AstErrorKind::ZeroDenominator => f.write_str("a rational literal cannot have denominator zero"),
            AstErrorKind::NonAsciiString => f.write_str("a string literal holds ASCII characters only; write others as escape sequences"),
            AstErrorKind::BooleanLiteral => f.write_str("`true` and `false` are symbols, not literals"),
            AstErrorKind::NotALiteral(c) => write!(f, "not a {} literal", c.name()),
            AstErrorKind::ApplicationHead => f.write_str("the head of an application is a symbol or an application of `_` or `as`"),
            AstErrorKind::NoArguments => f.write_str("an application needs at least one argument"),
            AstErrorKind::EmptyVariableList => f.write_str("a variable list cannot be empty"),
            AstErrorKind::QualifierVariable => f.write_str("the first variable of a variable list cannot be named `_` or `as`"),
        }
    }
}

/// A value refused by a constructor of the abstract syntax, because no text in
/// the grammar denotes it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AstError {
    kind: AstErrorKind,
}

impl AstError {
    pub(crate) fn new(kind: AstErrorKind) -> AstError {
        AstError { kind }
    }

    /// What is wrong.
    pub fn kind(&self) -> AstErrorKind {
        self.kind
    }
}

impl fmt::Display for AstError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid Eunoia syntax: {}", self.kind)
    }
}

impl std::error::Error for AstError {}

/// A token, as an error reports what was found.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Found {
    /// `(`.
    LParen,
    /// `)`.
    RParen,
    /// A symbol, by its name (without the bars of a quoted symbol).
    Symbol(String),
    /// A reserved word (`!`, `let`, `par`, `eo::define`, ...).
    Reserved(&'static str),
    /// A keyword, by its name without the colon.
    Keyword(String),
    /// A literal, by its category and its text as written.
    Literal(LiteralCategory, String),
}

impl fmt::Display for Found {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Found::LParen => f.write_str("`(`"),
            Found::RParen => f.write_str("`)`"),
            Found::Symbol(s) => write!(f, "symbol `{s}`"),
            Found::Reserved(s) => write!(f, "reserved word `{s}`"),
            Found::Keyword(s) => write!(f, "keyword `:{s}`"),
            Found::Literal(LiteralCategory::String, _) => f.write_str("string literal"),
            Found::Literal(_, s) => write!(f, "literal `{s}`"),
        }
    }
}

/// Why a literal is not well formed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LiteralProblem {
    /// No digits where the category needs some: after `#b`, `#x`, or after
    /// the `.` or `/` of a decimal or rational.
    MissingDigits(LiteralCategory),
    /// `#` followed by neither `b` nor `x`.
    UnknownRadix,
    /// A character outside ASCII in a string literal (write it as an escape
    /// sequence).
    NonAsciiString,
    /// A rational with denominator zero.
    ZeroDenominator,
    /// A numeral with a leading zero where an arity or index is expected.
    LeadingZero,
    /// A numeral that does not fit an unsigned 32-bit integer where an arity
    /// or index is expected.
    TooLarge,
}

impl fmt::Display for LiteralProblem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LiteralProblem::MissingDigits(LiteralCategory::Binary) => f.write_str("expected binary digits after `#b`"),
            LiteralProblem::MissingDigits(LiteralCategory::Hexadecimal) => f.write_str("expected hexadecimal digits after `#x`"),
            LiteralProblem::MissingDigits(LiteralCategory::Rational) => f.write_str("expected digits after `/`"),
            LiteralProblem::MissingDigits(_) => f.write_str("expected digits after `.`"),
            LiteralProblem::UnknownRadix => f.write_str("expected `b` or `x` after `#`"),
            LiteralProblem::NonAsciiString => f.write_str("a character outside ASCII in a string literal must be written as an escape sequence"),
            LiteralProblem::ZeroDenominator => f.write_str("a rational literal cannot have denominator zero"),
            LiteralProblem::LeadingZero => f.write_str("numerals with leading zeroes are forbidden here"),
            LiteralProblem::TooLarge => f.write_str("numerals must fit into 32-bit unsigned integers here"),
        }
    }
}

/// A violation of the grammar that is not a single unexpected token.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SyntaxProblem {
    /// A character that begins no token.
    UnexpectedCharacter(char),
    /// `:` without a name.
    EmptyKeyword,
    /// `((x ...) ...)` where `x` is neither `_` nor `as` and the list is not
    /// a variable list.
    QualifierHead,
    /// An element of a variable list that is not a pair `(x T)`, e.g. `(x)`.
    VariablePair,
    /// An element of a `let` binding list that is not a pair `(x t)`, e.g. `(x)`.
    BindingPair,
    /// `()`: an application without a head.
    MissingHead,
    /// `(!)`: an annotation without a term.
    AnnotationWithoutTerm,
    /// `(! t)` with no attribute (the manual's `(! <term> <attr>+)`).
    AnnotationWithoutAttribute,
    /// `(par () ...)` (the manual's `(par (<symbol>+) ...)`).
    EmptyParameterList,
    /// A datatype without constructors (the manual's `(<cons-dec>+)`).
    DatatypeWithoutConstructor,
    /// `declare-datatypes` with as many sort declarations as datatype
    /// declarations, which it does not have.
    DatatypeCount {
        /// The sort declarations.
        sorts: usize,
        /// The datatype declarations.
        datatypes: usize,
    },
    /// A step without `:rule`.
    StepWithoutRule,
    /// A field of `declare-rule` out of the manual's order (`:assumption`,
    /// `:premises` or `:premise-list`, `:args`, `:requires`, `:conclusion`),
    /// or unknown, where `:conclusion` is expected.
    RuleField(Keyword),
    /// A keyword other than `:signature` after the parameters of a program.
    ProgramWithoutSignature(Keyword),
    /// A program signature without argument types (the manual's
    /// `:signature (<type>+)`).
    ProgramWithoutArgumentType,
    /// `declare-consts` with a symbol that names no literal category.
    UnknownLiteralCategory(String),
    /// A term that the abstract syntax refuses, for the reason its
    /// constructor gives.
    Invalid(AstErrorKind),
}

impl fmt::Display for SyntaxProblem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SyntaxProblem::UnexpectedCharacter(c) => write!(f, "unexpected character `{c}`"),
            SyntaxProblem::EmptyKeyword => f.write_str("expected a symbol after `:`"),
            SyntaxProblem::QualifierHead => f.write_str("expected `_` or `as` as the head of a qualified operator"),
            SyntaxProblem::VariablePair => f.write_str("a variable list holds pairs `(x T)`"),
            SyntaxProblem::BindingPair => f.write_str("a binding list holds pairs `(x t)`"),
            SyntaxProblem::MissingHead => f.write_str("an application needs a head"),
            SyntaxProblem::AnnotationWithoutTerm => f.write_str("a term annotation needs a term"),
            SyntaxProblem::AnnotationWithoutAttribute => f.write_str("a term annotation needs an attribute"),
            SyntaxProblem::EmptyParameterList => f.write_str("expected a non-empty parameter list after `par`"),
            SyntaxProblem::DatatypeWithoutConstructor => f.write_str("a datatype needs a constructor"),
            SyntaxProblem::DatatypeCount { sorts, datatypes } => write!(f, "{sorts} datatype(s) declared but {datatypes} defined"),
            SyntaxProblem::StepWithoutRule => f.write_str("expected `:rule` in a step"),
            SyntaxProblem::RuleField(k) => write!(f, "expected `:conclusion` in declare-rule, found `{k}` (the fields come in the order :assumption, :premises or :premise-list, :args, :requires, :conclusion)"),
            SyntaxProblem::ProgramWithoutSignature(k) => write!(f, "expected `:signature` in program, found `{k}`"),
            SyntaxProblem::ProgramWithoutArgumentType => f.write_str("a program signature needs an argument type"),
            SyntaxProblem::UnknownLiteralCategory(c) => write!(f, "unknown literal category `{c}`"),
            SyntaxProblem::Invalid(k) => write!(f, "{k}"),
        }
    }
}

/// A construct that Ethos reads but this crate does not.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UnsupportedConstruct {
    /// A quoted symbol that spells a builtin word (`|Bool|`, `|let|`, ...),
    /// which Ethos distinguishes from the word and the abstract syntax does not.
    QuotedBuiltinWord(&'static str),
    /// `-.5` or `-/5`: a decimal or rational without digits before its
    /// separator, by its text.
    LiteralWithoutLeadingDigits(String),
}

impl fmt::Display for UnsupportedConstruct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnsupportedConstruct::QuotedBuiltinWord(w) => write!(f, "the quoted symbol `|{w}|`, which Ethos distinguishes from the builtin word `{w}`"),
            UnsupportedConstruct::LiteralWithoutLeadingDigits(t) => write!(f, "the literal `{t}` without digits before its separator"),
        }
    }
}

/// Why a text is not a Eunoia script.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParseErrorKind {
    /// A string literal without its closing quote.
    UnterminatedString,
    /// A quoted symbol without its closing bar.
    UnterminatedQuotedSymbol,
    /// A literal that is not well formed.
    InvalidLiteral(LiteralProblem),
    /// The text ended where more was expected.
    UnexpectedEnd {
        /// What was expected.
        expected: &'static str,
    },
    /// A token that the grammar does not allow here.
    UnexpectedToken {
        /// What was expected.
        expected: &'static str,
        /// The token that was found.
        found: Found,
    },
    /// Any other violation of the grammar.
    Syntax(SyntaxProblem),
    /// A construct that Ethos accepts but this crate does not support; see the
    /// crate documentation for the supported subset.
    Unsupported(UnsupportedConstruct),
}

/// A text that is not a Eunoia script, with the position of the offending token.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ParseError {
    /// Where the error was found.
    pub position: Position,
    /// What is wrong.
    pub kind: ParseErrorKind,
}

impl ParseError {
    pub(crate) fn new(position: Position, kind: ParseErrorKind) -> ParseError {
        ParseError { position, kind }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.position, self.kind)
    }
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseErrorKind::UnterminatedString => write!(f, "unterminated string literal"),
            ParseErrorKind::UnterminatedQuotedSymbol => write!(f, "unterminated quoted symbol"),
            ParseErrorKind::InvalidLiteral(p) => write!(f, "invalid literal: {p}"),
            ParseErrorKind::UnexpectedEnd { expected } => write!(f, "unexpected end of input, expected {expected}"),
            ParseErrorKind::UnexpectedToken { expected, found } => write!(f, "expected {expected}, found {found}"),
            ParseErrorKind::Syntax(p) => write!(f, "{p}"),
            ParseErrorKind::Unsupported(c) => write!(f, "unsupported: {c}"),
        }
    }
}

impl std::error::Error for ParseError {}
