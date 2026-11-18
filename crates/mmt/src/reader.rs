//! The structural reader: the four delimiters of MMT's surface syntax
//! (doc/language/delimiters.md) and the read operations of
//! `api/parser/Reader.scala`, on which the structure parser is built.
//!
//! The delimiters form a hierarchy: the module delimiter ❚ (U+275A, or the
//! ASCII control character GS, 29) ends modules, the declaration delimiter ❙
//! (U+2759, or RS, 30) ends declarations, the object delimiter ❘ (U+2758, or
//! US, 31) ends components of declarations, and FS (28) ends a document. A
//! delimiter also ends every lower level. Line breaks `\r\n` and `\r` are read
//! as `\n`.

use crate::chars::{can_follow, is_java_whitespace};
use crate::error::Pos;

/// The level of a delimiter that ended the previous read operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Level {
    /// Nothing read yet.
    None,
    /// A space ended a token.
    Space,
    /// ❘ or US.
    Object,
    /// ❙ or RS.
    Declaration,
    /// ❚ or GS.
    Module,
    /// FS.
    Document,
    /// End of input.
    End,
}

/// The level of a delimiter character.
pub(crate) fn delimiter_level(c: char) -> Option<Level> {
    match c {
        '\u{2758}' | '\u{1F}' => Some(Level::Object),
        '\u{2759}' | '\u{1E}' => Some(Level::Declaration),
        '\u{275A}' | '\u{1D}' => Some(Level::Module),
        '\u{1C}' => Some(Level::Document),
        _ => None,
    }
}

/// Whether a character is one of the delimiters.
pub fn is_delimiter(c: char) -> bool {
    delimiter_level(c).is_some()
}

/// `Reader.whitespace`: Java whitespace that is not a delimiter.
pub(crate) fn is_ws(c: char) -> bool {
    !is_delimiter(c) && is_java_whitespace(c)
}

/// A reader over a source text.
pub(crate) struct Reader {
    chars: Vec<char>,
    i: usize,
    pos: Pos,
    last: Level,
}

impl Reader {
    pub(crate) fn new(text: &str) -> Reader {
        Reader::at(text, Pos::START)
    }

    pub(crate) fn at(text: &str, start: Pos) -> Reader {
        let normalized = text.replace("\r\n", "\n").replace('\r', "\n");
        Reader { chars: normalized.chars().collect(), i: 0, pos: start, last: Level::None }
    }

    pub(crate) fn end_of_input(&self) -> bool {
        self.last == Level::End
    }
    pub(crate) fn end_of_document(&self) -> bool {
        self.last >= Level::Document
    }
    pub(crate) fn end_of_module(&self) -> bool {
        self.last >= Level::Module
    }
    pub(crate) fn end_of_declaration(&self) -> bool {
        self.last >= Level::Declaration
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.i).copied()
    }

    fn read(&mut self) -> Option<char> {
        let c = self.chars.get(self.i).copied()?;
        self.i += 1;
        self.pos = self.pos.after(c);
        Some(c)
    }

    /// Skips whitespace and returns the next character with its position.
    fn read_skip_ws(&mut self) -> (Option<char>, Pos) {
        loop {
            let p = self.pos;
            match self.read() {
                Some(c) if is_ws(c) => continue,
                other => return (other, p),
            }
        }
    }

    /// Reads up to and including the next character at or above `level`
    /// (or, for `Level::Space`, the next ASCII space or delimiter); returns the
    /// text without leading and trailing whitespace and its start position.
    fn read_until(&mut self, level: Level) -> (String, Pos) {
        let (mut c, start) = self.read_skip_ws();
        let mut buffer = String::new();
        loop {
            match c {
                None => {
                    self.last = Level::End;
                    break;
                }
                Some(ch) => {
                    let stop = match delimiter_level(ch) {
                        Some(l) => l >= level || level == Level::Space,
                        None => level == Level::Space && ch == ' ',
                    };
                    if stop {
                        self.last = if ch == ' ' && delimiter_level(ch).is_none() { Level::Space } else { delimiter_level(ch).unwrap_or(Level::Space) };
                        break;
                    }
                    buffer.push(ch);
                    c = self.read();
                }
            }
        }
        let trimmed = buffer.trim_end_matches(is_ws).to_string();
        (trimmed, start)
    }

    /// Reads until the end of the current module.
    pub(crate) fn read_module(&mut self) -> (String, Pos) {
        self.read_until(Level::Module)
    }
    /// Reads until the end of the current declaration.
    pub(crate) fn read_declaration(&mut self) -> (String, Pos) {
        self.read_until(Level::Declaration)
    }
    /// Reads until the end of the current object.
    pub(crate) fn read_object(&mut self) -> (String, Pos) {
        self.read_until(Level::Object)
    }
    /// Reads until the next ASCII space or delimiter.
    pub(crate) fn read_to_space(&mut self) -> (String, Pos) {
        self.read_until(Level::Space)
    }

    /// Reads a token: a maximal sequence of characters without a word break
    /// (`Reader.readToken`); `/` never breaks a token. A delimiter met before
    /// the token starts is consumed and yields the empty token.
    pub(crate) fn read_token(&mut self) -> (String, Pos) {
        let (first, start) = self.read_skip_ws();
        let mut s = String::new();
        let mut c = match first {
            None => {
                self.last = Level::End;
                return (s, start);
            }
            Some(c) => {
                if let Some(l) = delimiter_level(c) {
                    self.last = l;
                    return (s, start);
                }
                c
            }
        };
        loop {
            s.push(c);
            match self.peek() {
                None => {
                    self.last = Level::End;
                    break;
                }
                Some(l) => {
                    if !can_follow(c, l) && l != '/' {
                        self.last = Level::Space;
                        break;
                    }
                    c = self.read().unwrap_or(l);
                }
            }
        }
        (s, start)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokens_and_objects() {
        let mut r = Reader::new("c : a ⟶ b ❘ = x❙ d❚");
        assert_eq!(r.read_token().0, "c");
        assert_eq!(r.read_token().0, ":");
        assert_eq!(r.read_object().0, "a ⟶ b");
        assert!(!r.end_of_declaration());
        assert_eq!(r.read_token().0, "=");
        assert_eq!(r.read_object().0, "x");
        assert!(r.end_of_declaration() && !r.end_of_module());
        assert_eq!(r.read_token().0, "d");
        assert_eq!(r.read_token().0, "");
        assert!(r.end_of_module());
    }

    #[test]
    fn slash_continues_a_token() {
        let mut r = Reader::new("// comment❙");
        assert_eq!(r.read_token().0, "//");
        // `/` is appended, but the letter after it is a word break again
        let mut r = Reader::new("a/b?c x");
        assert_eq!(r.read_token().0, "a/");
    }
}
