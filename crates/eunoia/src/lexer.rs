//! The lexicon of Eunoia: how a text is cut into tokens.
//!
//! The manual describes the lexicon only by reference to SMT-LIB ("Eunoia is
//! SMT-LIB-like"); the tokens that Ethos actually reads are fixed by its lexer,
//! `src/lexer.cpp` and `src/lexer.h` of Ethos commit
//! 08e4aa40c4f8a6e00833f10e8d8985777e424027, which this module follows:
//!
//! - whitespace is space, tab, carriage return and line feed; `;` starts a
//!   comment that runs to the end of the line;
//! - a simple symbol starts with a letter or one of `+-/*=%?!.$_~&^<>@` and
//!   continues with those characters, digits and `:` (the colon is allowed so
//!   that `eo::add` is one symbol); a quoted symbol is `|...|` with any
//!   character but `|` inside, and names the same symbol as its content;
//! - a keyword is `:` followed by a symbol start character and symbol
//!   characters;
//! - a token that starts with a digit is a numeral `[0-9]+`, a decimal
//!   `[0-9]+.[0-9]+` or a rational `[0-9]+/[0-9]+`; a simple symbol that starts
//!   with `-` and reads as `-` followed by such a literal is that negative
//!   literal (`Lexer::tokenizeCurrentSymbol`);
//! - `#b[01]+` is a binary and `#x[0-9a-fA-F]+` a hexadecimal literal;
//! - a string literal is `"..."` in which `""` stands for one `"`; a byte
//!   outside ASCII must be written as an escape sequence
//!   (`ExprParser::unescapeString`);
//! - the simple symbols `!`, `let`, `par` and `eo::define` are reserved words
//!   (`Lexer::tokenizeCurrentSymbol`): they begin a term annotation, a let, a
//!   parametric datatype and a definition binder, and never name a symbol.
//!
//! Ethos also lexes `Bool` and `Type` as separate tokens; they denote the
//! builtin types in every position, and Ethos refuses to bind them. Neither
//! is a matter of the grammar, so the lexer reads them as ordinary symbols.

use crate::ast::LiteralCategory;
use crate::error::{Found, LiteralProblem, ParseError, ParseErrorKind, Position, SyntaxProblem};

/// The characters besides letters that can start a simple symbol
/// (`s_extraSymbolChars` in Ethos `src/lexer.h`).
const EXTRA_SYMBOL_CHARS: &str = "+-/*=%?!.$_~&^<>@";

/// The simple symbols that Ethos lexes as reserved words.
pub(crate) const RESERVED_WORDS: [&str; 4] = ["!", "let", "par", "eo::define"];

/// Whether `c` can start a simple symbol.
pub(crate) fn is_symbol_start(c: char) -> bool {
    c.is_ascii_alphabetic() || EXTRA_SYMBOL_CHARS.contains(c)
}

/// Whether `c` can continue a simple symbol.
pub(crate) fn is_symbol_char(c: char) -> bool {
    is_symbol_start(c) || c.is_ascii_digit() || c == ':'
}

/// The literal kinds that a token can carry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NumberShape {
    Numeral,
    Decimal,
    Rational,
}

/// Classifies a text as Ethos does a negative literal: `-` followed by digits
/// with at most one `.` or `/` that is not the last character.
pub(crate) fn negative_number_shape(text: &str) -> Option<NumberShape> {
    let rest = text.strip_prefix('-')?;
    if rest.is_empty() {
        return None;
    }
    let chars: Vec<char> = rest.chars().collect();
    let mut shape = NumberShape::Numeral;
    for (i, c) in chars.iter().enumerate() {
        if c.is_ascii_digit() {
            continue;
        }
        if i + 1 < chars.len() && shape == NumberShape::Numeral {
            if *c == '.' {
                shape = NumberShape::Decimal;
                continue;
            }
            if *c == '/' {
                shape = NumberShape::Rational;
                continue;
            }
        }
        return None;
    }
    Some(shape)
}

/// Whether `text` is read back as exactly one simple symbol token naming `text`.
pub(crate) fn is_simple_symbol(text: &str) -> bool {
    let mut chars = text.chars();
    match chars.next() {
        Some(c) if is_symbol_start(c) => {}
        _ => return false,
    }
    chars.all(is_symbol_char) && negative_number_shape(text).is_none() && !RESERVED_WORDS.contains(&text)
}

/// A token of the Eunoia lexicon.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Tok {
    LParen,
    RParen,
    /// A simple symbol that is not a reserved word.
    Symbol(String),
    /// A quoted symbol, by its content.
    Quoted(String),
    /// One of [`RESERVED_WORDS`].
    Reserved(&'static str),
    /// A keyword, without its colon.
    Keyword(String),
    Numeral(String),
    Decimal(String),
    Rational(String),
    /// A binary literal, by its digits.
    Binary(String),
    /// A hexadecimal literal, by its digits.
    Hexadecimal(String),
    /// A string literal, by its content with `""` read as `"`.
    Str(String),
}

impl Tok {
    /// The token as an error reports it.
    pub(crate) fn describe(&self) -> Found {
        match self {
            Tok::LParen => Found::LParen,
            Tok::RParen => Found::RParen,
            Tok::Symbol(s) | Tok::Quoted(s) => Found::Symbol(s.clone()),
            Tok::Reserved(s) => Found::Reserved(s),
            Tok::Keyword(s) => Found::Keyword(s.clone()),
            Tok::Numeral(s) => Found::Literal(LiteralCategory::Numeral, s.clone()),
            Tok::Decimal(s) => Found::Literal(LiteralCategory::Decimal, s.clone()),
            Tok::Rational(s) => Found::Literal(LiteralCategory::Rational, s.clone()),
            Tok::Binary(s) => Found::Literal(LiteralCategory::Binary, format!("#b{s}")),
            Tok::Hexadecimal(s) => Found::Literal(LiteralCategory::Hexadecimal, format!("#x{s}")),
            Tok::Str(s) => Found::Literal(LiteralCategory::String, s.clone()),
        }
    }
}

/// A token with the position of its first character.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Token {
    pub(crate) tok: Tok,
    pub(crate) pos: Position,
}

/// Cuts a whole text into tokens.
#[cfg(test)]
pub(crate) fn tokenize(text: &str) -> Result<Vec<Token>, ParseError> {
    tokenize_from(text, Position::START).map(|(t, _)| t)
}

/// Cuts a text that begins at `start` of a larger text into tokens, with
/// positions in the larger text, and the position of the end of the text.
pub(crate) fn tokenize_from(text: &str, start: Position) -> Result<(Vec<Token>, Position), ParseError> {
    let mut lexer = Lexer { chars: text.chars().collect(), at: 0, line: start.line, column: start.column };
    let mut tokens = Vec::new();
    while let Some(token) = lexer.next_token()? {
        tokens.push(token);
    }
    Ok((tokens, lexer.pos()))
}

struct Lexer {
    chars: Vec<char>,
    at: usize,
    line: u32,
    column: u32,
}

impl Lexer {
    fn peek(&self) -> Option<char> {
        self.chars.get(self.at).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.at += 1;
        if c == '\n' {
            self.line = self.line.saturating_add(1);
            self.column = 1;
        } else {
            self.column = self.column.saturating_add(1);
        }
        Some(c)
    }

    fn pos(&self) -> Position {
        Position { line: self.line, column: self.column }
    }

    fn take_while(&mut self, pred: impl Fn(char) -> bool) -> String {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if !pred(c) {
                break;
            }
            s.push(c);
            self.bump();
        }
        s
    }

    fn next_token(&mut self) -> Result<Option<Token>, ParseError> {
        loop {
            match self.peek() {
                None => return Ok(None),
                Some(' ' | '\t' | '\r' | '\n') => {
                    self.bump();
                }
                Some(';') => {
                    while let Some(c) = self.bump() {
                        if c == '\n' {
                            break;
                        }
                    }
                }
                Some(_) => break,
            }
        }
        let pos = self.pos();
        let err = |kind| Err(ParseError::new(pos, kind));
        let Some(c) = self.bump() else { return Ok(None) };
        let tok = match c {
            '(' => Tok::LParen,
            ')' => Tok::RParen,
            '|' => {
                let mut s = String::new();
                loop {
                    match self.bump() {
                        None => return err(ParseErrorKind::UnterminatedQuotedSymbol),
                        Some('|') => break,
                        Some(c) => s.push(c),
                    }
                }
                Tok::Quoted(s)
            }
            '#' => match self.bump() {
                Some('b') => {
                    let digits = self.take_while(|c| c == '0' || c == '1');
                    if digits.is_empty() {
                        return err(ParseErrorKind::InvalidLiteral(LiteralProblem::MissingDigits(LiteralCategory::Binary)));
                    }
                    Tok::Binary(digits)
                }
                Some('x') => {
                    let digits = self.take_while(|c| c.is_ascii_hexdigit());
                    if digits.is_empty() {
                        return err(ParseErrorKind::InvalidLiteral(LiteralProblem::MissingDigits(LiteralCategory::Hexadecimal)));
                    }
                    Tok::Hexadecimal(digits)
                }
                _ => return err(ParseErrorKind::InvalidLiteral(LiteralProblem::UnknownRadix)),
            },
            '"' => {
                let mut s = String::new();
                loop {
                    match self.bump() {
                        None => return err(ParseErrorKind::UnterminatedString),
                        Some('"') => {
                            if self.peek() == Some('"') {
                                self.bump();
                                s.push('"');
                            } else {
                                break;
                            }
                        }
                        Some(c) if !c.is_ascii() => {
                            return err(ParseErrorKind::InvalidLiteral(LiteralProblem::NonAsciiString))
                        }
                        Some(c) => s.push(c),
                    }
                }
                Tok::Str(s)
            }
            ':' => match self.peek() {
                Some(c) if is_symbol_start(c) => Tok::Keyword(self.take_while(is_symbol_char)),
                _ => return err(ParseErrorKind::Syntax(SyntaxProblem::EmptyKeyword)),
            },
            c if c.is_ascii_digit() => {
                let mut s = c.to_string();
                s.push_str(&self.take_while(|c| c.is_ascii_digit()));
                match self.peek() {
                    Some(sep @ ('.' | '/')) => {
                        self.bump();
                        let digits = self.take_while(|c| c.is_ascii_digit());
                        if digits.is_empty() {
                            return err(ParseErrorKind::InvalidLiteral(LiteralProblem::MissingDigits(if sep == '/' { LiteralCategory::Rational } else { LiteralCategory::Decimal })));
                        }
                        s.push(sep);
                        s.push_str(&digits);
                        if sep == '.' {
                            Tok::Decimal(s)
                        } else {
                            Tok::Rational(s)
                        }
                    }
                    _ => Tok::Numeral(s),
                }
            }
            c if is_symbol_start(c) => {
                let mut s = c.to_string();
                s.push_str(&self.take_while(is_symbol_char));
                if let Some(word) = RESERVED_WORDS.iter().find(|w| **w == s) {
                    Tok::Reserved(word)
                } else {
                    match negative_number_shape(&s) {
                        Some(NumberShape::Numeral) => Tok::Numeral(s),
                        Some(NumberShape::Decimal) => Tok::Decimal(s),
                        Some(NumberShape::Rational) => Tok::Rational(s),
                        None => Tok::Symbol(s),
                    }
                }
            }
            other => return err(ParseErrorKind::Syntax(SyntaxProblem::UnexpectedCharacter(other))),
        };
        Ok(Some(Token { tok, pos }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(s: &str) -> Vec<Tok> {
        tokenize(s).unwrap().into_iter().map(|t| t.tok).collect()
    }

    #[test]
    fn negative_literals_follow_tokenize_current_symbol() {
        assert_eq!(toks("-1 -1.5 -1/3 - -a -1."), vec![Tok::Numeral("-1".into()), Tok::Decimal("-1.5".into()), Tok::Rational("-1/3".into()), Tok::Symbol("-".into()), Tok::Symbol("-a".into()), Tok::Symbol("-1.".into())]);
    }

    #[test]
    fn reserved_words_and_symbols_with_colons() {
        assert_eq!(toks("(! eo::define let par eo::add)"), vec![Tok::LParen, Tok::Reserved("!"), Tok::Reserved("eo::define"), Tok::Reserved("let"), Tok::Reserved("par"), Tok::Symbol("eo::add".into()), Tok::RParen]);
    }

    #[test]
    fn strings_double_their_quotes() {
        assert_eq!(toks("\"a\"\"b\""), vec![Tok::Str("a\"b".into())]);
    }

    #[test]
    fn positions_are_one_based() {
        let t = tokenize("; c\n  (x").unwrap();
        assert_eq!(t[0].pos, Position { line: 2, column: 3 });
        assert_eq!(t[1].pos, Position { line: 2, column: 4 });
    }
}
