//! Errors of reading text, building syntax and reading solver output.
//!
//! An [`Error`] is a value: no function of this crate panics on bad input.
//! Its [`ErrorKind`] says which part of the grammar was broken; its
//! position, when the error comes from text, is the line and column (both
//! counted from 1, columns in characters) of the token or command where the
//! rule broke. An error of the SMT-LIB layer is wrapped once, by
//! `From<smtlib::Error>`: it keeps its position and message, its kind is
//! mapped, and the `smtlib` error itself, with its own kind, is the
//! [`std::error::Error::source`] and [`Error::smtlib`].

use smtlib::Position;
use std::fmt;

/// Which part of the grammar an [`Error`] reports as broken.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ErrorKind {
    /// The text is not a sequence of tokens: the SMT-LIB lexicon extended
    /// with the number literals of Figure 2.
    Lexical,
    /// The tokens do not form the production of Figure 2 (or of the SMT-LIB
    /// grammar it builds on) that was expected, or a ⟨symbol⟩ spells a
    /// number literal.
    Syntax,
    /// The text nests parentheses deeper than the reader's limit
    /// ([`crate::dialect`]), or a value built in code would print to such
    /// text.
    Depth,
    /// The input is legal SMT-LIB but outside what this crate reads: the
    /// SMT-LIB 2.7 additions in proof terms.
    Unsupported,
    /// A value given to a constructor is not one the grammar admits.
    Construction,
    /// The output of a solver cannot be split into responses, or reports
    /// an error.
    Output,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            ErrorKind::Lexical => "lexical error",
            ErrorKind::Syntax => "syntax error",
            ErrorKind::Depth => "nesting too deep",
            ErrorKind::Unsupported => "unsupported",
            ErrorKind::Construction => "construction error",
            ErrorKind::Output => "output error",
        };
        f.write_str(name)
    }
}

/// An error of this crate: its kind, where it was found, and what it says.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    kind: ErrorKind,
    position: Option<Position>,
    message: String,
    source: Option<smtlib::Error>,
}

impl Error {
    pub(crate) fn new(kind: ErrorKind, message: impl Into<String>) -> Error {
        Error { kind, position: None, message: message.into(), source: None }
    }

    pub(crate) fn at(kind: ErrorKind, position: Position, message: impl Into<String>) -> Error {
        Error { kind, position: Some(position), message: message.into(), source: None }
    }

    pub(crate) fn syntax(position: Position, message: impl Into<String>) -> Error {
        Error::at(ErrorKind::Syntax, position, message)
    }

    /// This error, given `position` if it has none yet.
    pub(crate) fn or_at(mut self, position: Position) -> Error {
        if self.position.is_none() {
            self.position = Some(position);
        }
        self
    }

    /// Which rule was broken.
    pub fn kind(&self) -> ErrorKind {
        self.kind
    }

    /// Where, when the input came from text.
    pub fn position(&self) -> Option<Position> {
        self.position
    }

    /// A sentence that says what was found and what was expected.
    pub fn message(&self) -> &str {
        &self.message
    }

    /// The error of the `smtlib` crate this error wraps, with its own kind.
    pub fn smtlib(&self) -> Option<&smtlib::Error> {
        self.source.as_ref()
    }
}

impl From<smtlib::Error> for Error {
    /// An error of the SMT-LIB layer. Lexical, syntax, depth and
    /// construction errors keep their kind; a kind that `smtlib` adds later
    /// is a syntax error.
    fn from(error: smtlib::Error) -> Error {
        let kind = match error.kind() {
            smtlib::ErrorKind::Lexical => ErrorKind::Lexical,
            smtlib::ErrorKind::Syntax => ErrorKind::Syntax,
            smtlib::ErrorKind::Depth => ErrorKind::Depth,
            smtlib::ErrorKind::Construction => ErrorKind::Construction,
            _ => ErrorKind::Syntax,
        };
        Error { kind, position: error.position(), message: error.message().to_string(), source: Some(error) }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.position {
            Some(position) => write!(f, "{position}: {}: {}", self.kind, self.message),
            None => write!(f, "{}: {}", self.kind, self.message),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.source.as_ref().map(|e| e as &(dyn std::error::Error + 'static))
    }
}

/// The result type of this crate.
pub type Result<T> = std::result::Result<T, Error>;
