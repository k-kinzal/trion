//! Errors are values. Every error has a kind, which says which part of the
//! language rejected the input, the source file and position where known, a
//! message in English, and the contexts it was reported in. The kind
//! [`ErrorKind::Unsupported`] marks input that MMT v27.0.0 reads but that
//! this crate does not implement: such input is rejected, never read or
//! printed silently. The kind [`ErrorKind::Limit`] marks input that exceeds
//! a limit of this crate (see [`crate::Limits`]), never a stack overflow.

use std::fmt;
use std::path::{Path, PathBuf};

/// A position in a source text: line and column count from 1; the column
/// and the offset count Unicode scalar values (not bytes), and a line break
/// counts as one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Pos {
    line: u32,
    column: u32,
    offset: usize,
}

impl Default for Pos {
    fn default() -> Pos {
        Pos::START
    }
}

impl Pos {
    /// The first position of a text.
    pub const START: Pos = Pos { line: 1, column: 1, offset: 0 };

    /// The line, from 1.
    pub fn line(self) -> u32 {
        self.line
    }

    /// The column, from 1, in Unicode scalar values.
    pub fn column(self) -> u32 {
        self.column
    }

    /// The offset from the start of the text, in Unicode scalar values.
    pub fn offset(self) -> usize {
        self.offset
    }

    /// The position after reading `c` at this position.
    pub fn after(self, c: char) -> Pos {
        if c == '\n' {
            Pos { line: self.line.saturating_add(1), column: 1, offset: self.offset + 1 }
        } else {
            Pos { line: self.line, column: self.column.saturating_add(1), offset: self.offset + 1 }
        }
    }

    /// The position after reading all characters of `s` at this position.
    pub fn after_str(self, s: &str) -> Pos {
        s.chars().fold(self, Pos::after)
    }
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// Which part of the language rejected the input.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ErrorKind {
    /// The structural syntax of a `.mmt` file (delimiters, keywords, names).
    Syntax,
    /// An MMT URI or name is ill-formed.
    Uri,
    /// A name or URI does not resolve to a declaration in scope.
    Unresolved,
    /// A notation declaration is ill-formed.
    Notation,
    /// An object does not parse with the notations and lexing rules in scope.
    Object,
    /// Several notations apply in a way that MMT reports as ambiguous.
    Ambiguous,
    /// The construct is part of MMT but outside the subset implemented here.
    Unsupported,
    /// A declaration violates a structural rule of the module system (for
    /// example a duplicate name, a theory declared twice or a cyclic include).
    Structure,
    /// An archive (manifest, source folder, dependency) could not be loaded.
    Archive,
    /// A term or theory cannot be written so that it reads back the same.
    Print,
    /// The input exceeds a limit of this crate (see [`crate::Limits`]).
    Limit,
}

impl ErrorKind {
    fn label(self) -> &'static str {
        match self {
            ErrorKind::Syntax => "syntax error",
            ErrorKind::Uri => "ill-formed URI",
            ErrorKind::Unresolved => "unresolved",
            ErrorKind::Notation => "ill-formed notation",
            ErrorKind::Object => "object error",
            ErrorKind::Ambiguous => "ambiguous",
            ErrorKind::Unsupported => "unsupported",
            ErrorKind::Structure => "structural error",
            ErrorKind::Archive => "archive error",
            ErrorKind::Print => "cannot print",
            ErrorKind::Limit => "limit exceeded",
        }
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

/// An error: its kind, the file and position where known, a message, and the
/// contexts it was reported in (innermost first). It is one pointer wide, so
/// that results stay small.
#[derive(Clone, PartialEq, Eq)]
pub struct Error {
    inner: Box<Inner>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Inner {
    kind: ErrorKind,
    file: Option<PathBuf>,
    pos: Option<Pos>,
    message: String,
    contexts: Vec<String>,
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let i = &self.inner;
        f.debug_struct("Error").field("kind", &i.kind).field("file", &i.file).field("pos", &i.pos).field("message", &i.message).field("contexts", &i.contexts).finish()
    }
}

impl Error {
    /// An error without position.
    pub fn new(kind: ErrorKind, message: impl Into<String>) -> Error {
        Error { inner: Box::new(Inner { kind, file: None, pos: None, message: message.into(), contexts: Vec::new() }) }
    }

    /// An error at a position.
    pub fn at(kind: ErrorKind, pos: Pos, message: impl Into<String>) -> Error {
        let mut e = Error::new(kind, message);
        e.inner.pos = Some(pos);
        e
    }

    /// Which part of the language rejected the input.
    pub fn kind(&self) -> ErrorKind {
        self.inner.kind
    }

    /// The source file, if known.
    pub fn file(&self) -> Option<&Path> {
        self.inner.file.as_deref()
    }

    /// The position in the source, if known.
    pub fn pos(&self) -> Option<Pos> {
        self.inner.pos
    }

    /// What went wrong, without the contexts.
    pub fn message(&self) -> &str {
        &self.inner.message
    }

    /// The contexts the error was reported in, innermost first.
    pub fn contexts(&self) -> &[String] {
        &self.inner.contexts
    }

    /// The same error with a position, unless it has one already.
    pub fn or_at(mut self, pos: Pos) -> Error {
        if self.inner.pos.is_none() {
            self.inner.pos = Some(pos);
        }
        self
    }

    /// The same error without position.
    pub(crate) fn unpositioned(mut self) -> Error {
        self.inner.pos = None;
        self
    }

    /// The same error attributed to a file, unless it has one already.
    pub fn in_file(mut self, file: impl Into<PathBuf>) -> Error {
        if self.inner.file.is_none() {
            self.inner.file = Some(file.into());
        }
        self
    }

    /// The same error with a context (shown before the message).
    pub fn context(mut self, context: impl fmt::Display) -> Error {
        self.inner.contexts.push(context.to_string());
        self
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(file) = &self.inner.file {
            write!(f, "{}:", file.display())?;
        }
        if let Some(pos) = &self.inner.pos {
            write!(f, "{pos}: ")?;
        } else if self.inner.file.is_some() {
            write!(f, " ")?;
        }
        write!(f, "{}: ", self.inner.kind.label())?;
        for c in self.inner.contexts.iter().rev() {
            write!(f, "{c}: ")?;
        }
        f.write_str(&self.inner.message)
    }
}

impl std::error::Error for Error {}

/// Results of this crate.
pub type Result<T> = std::result::Result<T, Error>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_shows_file_position_kind_contexts_and_message() {
        let e = Error::at(ErrorKind::Object, Pos::START.after_str("ab\nc"), "x").context("inner").context("outer").in_file("f.mmt");
        assert_eq!(e.to_string(), "f.mmt:2:2: object error: outer: inner: x");
        assert_eq!(e.message(), "x");
        assert_eq!(e.pos().map(Pos::offset), Some(4));
    }
}
