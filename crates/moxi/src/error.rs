//! Errors of reading text and building syntax.
//!
//! An [`Error`] is a value: no function of this crate panics on any input.
//! Its [`ErrorKind`] says which part of the grammar was broken; its
//! position, when the error comes from text, is the line and column (both
//! counted from 1, columns in characters) of the token or S-expression at
//! which the text stopped being MoXI. An error of the SMT-LIB layer is
//! wrapped once, by `From<smtlib::Error>`: it keeps its position and
//! message, its kind is mapped, and the `smtlib` error itself, with its own
//! kind, is the [`std::error::Error::source`] and [`Error::smtlib`].

use smtlib::Position;
use std::fmt;

/// Which part of the grammar an [`Error`] reports as broken.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ErrorKind {
    /// The text is not a sequence of SMT-LIB tokens (SMT-LIB §3.1, with `'`
    /// admitted in simple symbols).
    Lexical,
    /// The tokens do not form the expected production of MoXI or of
    /// SMT-LIB: a missing or misplaced attribute, an unknown command, a list
    /// where a symbol is expected, and so on.
    Syntax,
    /// The input is legal SMT-LIB but outside what this crate reads: an
    /// SMT-LIB command that MoXI does not adopt, or what SMT-LIB 2.7 added to
    /// the term grammar of SMT-LIB 2.6 (`lambda`, the `_` pattern).
    Unsupported,
    /// The text nests parentheses deeper than the reader accepts (the limit
    /// of the [`crate::dialect`], `smtlib`'s
    /// [`Dialect::DEFAULT_MAX_DEPTH`](smtlib::Dialect::DEFAULT_MAX_DEPTH)),
    /// or a value given to a constructor would print as such text.
    Depth,
    /// A value given to a constructor is not one the reader could produce,
    /// so its text would not read back to it (a constant or binder of
    /// another dialect).
    Construction,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ErrorKind::Lexical => "lexical error",
            ErrorKind::Syntax => "syntax error",
            ErrorKind::Unsupported => "unsupported",
            ErrorKind::Depth => "nesting too deep",
            ErrorKind::Construction => "construction error",
        })
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

    /// This error, given `position` if it has none yet.
    pub(crate) fn or_at(mut self, position: Position) -> Error {
        if self.position.is_none() {
            self.position = Some(position);
        }
        self
    }

    /// Which part of the grammar was broken.
    pub fn kind(&self) -> ErrorKind {
        self.kind
    }

    /// Where, when the input came from text: line and column, both counted
    /// from 1. Every error of reading text has one; an error of a
    /// constructor has none.
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
    /// construction errors keep their kind; this crate calls the SMT-LIB
    /// layer only to read and to build syntax, so a kind added to it later
    /// is taken for a malformed production, a syntax error. The original,
    /// with its kind, is kept as the source.
    fn from(error: smtlib::Error) -> Error {
        #[allow(unreachable_patterns)]
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
