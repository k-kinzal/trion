//! The error of reading and building syntax.
//!
//! An [`Error`] is a value: no function of this crate panics on bad input.
//! Its [`ErrorKind`] says which rule of the reference was broken, and its
//! position, when the error comes from text, is the line and column (both
//! counted from 1, columns in characters) of the token where the rule broke.
//!
//! A crate built on this one can keep an [`Error`] as the source of its
//! own error (it implements [`std::error::Error`], [`Clone`], [`Send`] and
//! [`Sync`]), or build one with [`Error::new`] and [`Error::at`] for a
//! format whose readers share these kinds.

use std::fmt;

/// A place in a source text: line and column, both counted from 1.
///
/// A line ends at a line feed, at a carriage return followed by a line
/// feed (counted once), or at a carriage return alone, as in every reader
/// of this crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Position {
    line: usize,
    column: usize,
}

impl Position {
    /// The first character of a text.
    pub const START: Position = Position { line: 1, column: 1 };

    /// The position at `line` and `column`, both counted from 1 (a 0 is
    /// taken as 1).
    pub fn new(line: usize, column: usize) -> Position {
        Position { line: line.max(1), column: column.max(1) }
    }

    /// The line, counted from 1.
    pub fn line(self) -> usize {
        self.line
    }

    /// The column in characters, counted from 1.
    pub fn column(self) -> usize {
        self.column
    }

    /// The position after `text`, read from this one.
    pub fn advance(self, text: &str) -> Position {
        let mut position = self;
        let mut chars = text.chars().peekable();
        while let Some(c) = chars.next() {
            position = position.after(c, chars.peek().copied());
        }
        position
    }

    /// The position after the character `c`, which `next` follows. A
    /// carriage return followed by a line feed ends one line, not two.
    pub(crate) fn after(self, c: char, next: Option<char>) -> Position {
        match c {
            '\n' => Position { line: self.line + 1, column: 1 },
            '\r' if next == Some('\n') => self,
            '\r' => Position { line: self.line + 1, column: 1 },
            _ => Position { line: self.line, column: self.column + 1 },
        }
    }
}

impl Default for Position {
    fn default() -> Position {
        Position::START
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// Which rule an [`Error`] reports as broken.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ErrorKind {
    /// The text is not a sequence of tokens of §3.1.
    Lexical,
    /// The tokens do not form the production that was expected (§3.2–§3.11,
    /// Figure 3.10).
    Syntax,
    /// The text nests parentheses deeper than the reader's limit
    /// ([`crate::Dialect::with_max_depth`]).
    Depth,
    /// A value given to a constructor of the syntax is not one the grammar
    /// admits (for example a symbol containing `|`).
    Construction,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ErrorKind::Lexical => "lexical error",
            ErrorKind::Syntax => "syntax error",
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
}

impl Error {
    /// An error of `kind` with `message` and no position.
    pub fn new(kind: ErrorKind, message: impl Into<String>) -> Error {
        Error { kind, position: None, message: message.into() }
    }

    /// An error of `kind` at `position`.
    pub fn at(kind: ErrorKind, position: Position, message: impl Into<String>) -> Error {
        Error { kind, position: Some(position), message: message.into() }
    }

    /// This error, at `position` if it has no position yet.
    pub fn or_at(mut self, position: Position) -> Error {
        self.position.get_or_insert(position);
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

    pub(crate) fn construction(message: impl Into<String>) -> Error {
        Error::new(ErrorKind::Construction, message)
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

impl std::error::Error for Error {}

/// The result type of this crate.
pub type Result<T> = std::result::Result<T, Error>;
