//! The tokenizer of the object parser and the lexer extensions of the
//! literals this crate implements (`api/parser/TokenList.scala`,
//! `api/parser/LexerExtension.scala`, `api/uom/StandardLiterals.scala`).
//!
//! Tokens are maximal sequences of letters and numbers, or single other
//! characters; connectors (such as `_`) join the characters around them,
//! combining marks stay with the preceding character, `?` starts a token
//! before a letter, and `?` and `/` continue a token. Whitespace separates
//! tokens. Before the default rules, the lexer extensions in scope are tried
//! at every position in order of decreasing priority; each turns a piece of
//! text into one token. The extensions implemented here are the lexers of
//! realized types (number literals, string literals in double quotes, the
//! keywords `true` and `false`, notation literals `nt"…"`), the string
//! interpolation lexer `s"…${…}…"` and the URI lexer `☞URI`.

use crate::chars::{is_connector, is_digit, is_java_whitespace, is_letter, is_mark, is_number};
use crate::error::{Error, ErrorKind, Pos, Result};
use crate::term::{Integer, LitValue, Literal, Term};

/// A semantic type of literals (`api/uom/StandardLiterals.scala`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SemType {
    /// StandardString.
    String,
    /// StandardInt.
    Int,
    /// StandardNat (non-negative integers).
    Nat,
    /// StandardPositive (positive integers).
    Positive,
    /// StandardBool.
    Bool,
    /// NotationRealizedType (the type `http://cds.omdoc.org/mmt?mmt?notation`).
    Notation,
}

impl SemType {
    /// Whether a value belongs to this semantic type.
    pub fn contains(self, v: &LitValue) -> bool {
        match (self, v) {
            (SemType::String, LitValue::String(_)) => true,
            (SemType::Int, LitValue::Int(_)) => true,
            (SemType::Nat, LitValue::Int(i)) => !i.is_negative(),
            (SemType::Positive, LitValue::Int(i)) => !i.is_negative() && !i.is_zero(),
            (SemType::Bool, LitValue::Bool(_)) => true,
            (SemType::Notation, LitValue::Notation(_)) => true,
            _ => false,
        }
    }

    /// The lexer of the semantic type.
    pub(crate) fn lex_kind(self) -> LexKind {
        match self {
            SemType::String => LexKind::Quoted,
            SemType::Int | SemType::Nat | SemType::Positive => LexKind::Number,
            SemType::Bool => LexKind::Keywords,
            SemType::Notation => LexKind::NotationQuote,
        }
    }

    /// Parses the lexed text into a value (`RealizedType.parse`), if it is one.
    fn parse(self, text: &str) -> Option<LitValue> {
        let v = match self {
            SemType::String => LitValue::String(text.to_string()),
            SemType::Int | SemType::Nat | SemType::Positive => LitValue::Int(Integer::parse(text)?),
            SemType::Bool => LitValue::Bool(match text {
                "true" => true,
                "false" => false,
                _ => return None,
            }),
            SemType::Notation => LitValue::Notation(crate::notation::Notation::parse(text, &crate::uri::NamespaceMap::empty()).ok()?.to_string()),
        };
        self.contains(&v).then_some(v)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LexKind {
    Number,
    Quoted,
    Keywords,
    NotationQuote,
}

/// A lexer extension in scope.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum LexerRule {
    /// The lexer of a realized type: literals of `sem` get the syntactic type `tp`.
    Literal { sem: SemType, tp: Term },
    /// `s"…${t}…"`: string parts are literals of type `string`, joined by LF application of `concat`.
    Interpolation { string: Term, concat: Term },
    /// `☞URI`.
    Uri,
}

impl LexerRule {
    /// The priority (`LexerExtension.priority`): the length of the trigger,
    /// except for realized types, whose lexers have the priority of the rule (0).
    pub(crate) fn priority(&self) -> usize {
        match self {
            LexerRule::Literal { .. } => 0,
            LexerRule::Interpolation { .. } => 2,
            LexerRule::Uri => 1,
        }
    }
}

/// A token of the default lexer.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Token {
    pub(crate) word: String,
    pub(crate) pos: Pos,
    pub(crate) ws_before: bool,
}

/// A part of an interpolated string.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum InterpolationPart {
    Str(String),
    Mmt(String, Pos),
}

/// A token produced by a lexer extension.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum External {
    /// A context-free token that is a term (a literal).
    Term(Term, Pos),
    /// An interpolated string, parsed later.
    Interpolation { parts: Vec<InterpolationPart>, string: Term, concat: Term, pos: Pos },
}

/// The result of the tokenizer.
#[derive(Clone, Debug, PartialEq)]
#[allow(clippy::large_enum_variant)] // token lists are short-lived and scanned in place
pub(crate) enum Lexed {
    Token(Token),
    External(External),
}

/// Tokenizes an object (`TokenList.apply`) with the lexer extensions in scope
/// (sorted by decreasing priority); interpolated strings nest at most
/// `max_nesting` levels (beyond, an error of kind `Limit`), so that the text
/// is not lexed again for every level.
#[allow(unused_assignments)] // the macro `end_token` resets `whitespace` also where it is set again right after
pub(crate) fn tokenize(s: &str, start: Pos, lexers: &[LexerRule], max_nesting: usize) -> Result<Vec<Lexed>> {
    let chars: Vec<char> = s.chars().collect();
    let n = chars.len();
    let mut tokens: Vec<Lexed> = Vec::new();
    let mut current = String::new();
    let mut current_pos = start;
    let mut connect = false;
    let mut skip = 0usize;
    let mut whitespace = true;
    let mut pos = start;
    let mut i = 0usize;
    macro_rules! end_token {
        () => {
            if !current.is_empty() {
                tokens.push(Lexed::Token(Token { word: std::mem::take(&mut current), pos: current_pos, ws_before: whitespace }));
                whitespace = false;
            }
        };
    }
    macro_rules! push_char {
        ($c:expr) => {
            if current.is_empty() {
                current_pos = pos;
            }
            current.push($c);
        };
    }
    while i < n {
        let c = chars[i];
        let next = chars.get(i + 1).copied();
        if skip > 0 {
            skip -= 1;
        } else if let Some((lexed, len)) = apply_lexers(&chars, i, pos, lexers, max_nesting)? {
            end_token!();
            tokens.push(lexed);
            skip = len - 1;
        } else if is_java_whitespace(c) {
            end_token!();
            whitespace = true;
        } else {
            if connect {
                push_char!(c);
                connect = false;
            } else if is_letter(c) || is_number(c) {
                push_char!(c);
            } else if is_mark(c) {
                push_char!(c);
                if let Some(nc) = next {
                    if !(is_connector(nc) || is_mark(nc)) {
                        end_token!();
                    }
                }
            } else if (c == '?' && current.is_empty() && next.is_some_and(is_letter)) || ((c == '?' || c == '/') && !current.is_empty() && next.is_some_and(|nc| !is_java_whitespace(nc))) {
                push_char!(c);
            } else if is_connector(c) {
                push_char!(c);
                connect = true;
            } else {
                end_token!();
                if next.is_some_and(|nc| is_connector(nc) || is_mark(nc)) {
                    push_char!(c);
                } else {
                    tokens.push(Lexed::Token(Token { word: c.to_string(), pos, ws_before: whitespace }));
                }
            }
            whitespace = false;
        }
        pos = pos.after(c);
        i += 1;
    }
    end_token!();
    Ok(tokens)
}

fn starts_with(chars: &[char], i: usize, s: &str) -> bool {
    let mut j = i;
    for c in s.chars() {
        if chars.get(j) != Some(&c) {
            return false;
        }
        j += 1;
    }
    true
}

/// Tries the lexer extensions at position `i`; returns the token and the number of characters it covers.
fn apply_lexers(chars: &[char], i: usize, pos: Pos, lexers: &[LexerRule], max_nesting: usize) -> Result<Option<(Lexed, usize)>> {
    for l in lexers {
        match l {
            LexerRule::Literal { sem, tp } => {
                if let Some((text, eaten)) = lex_literal(sem.lex_kind(), chars, i) {
                    if let Some(v) = sem.parse(&text) {
                        // several realized types with the same lexer would make the reading depend on MMT's internal order
                        let rivals: Vec<&Term> = lexers
                            .iter()
                            .filter_map(|o| match o {
                                LexerRule::Literal { sem: s2, tp: t2 } if t2 != tp && s2.lex_kind() == sem.lex_kind() && s2.parse(&text).is_some() => Some(t2),
                                _ => None,
                            })
                            .collect();
                        if !rivals.is_empty() {
                            return Err(Error::at(ErrorKind::Unsupported, pos, format!("literal {text} can be read by several realized types ({tp} and {}); the choice between them is not supported", rivals[0])));
                        }
                        return Ok(Some((Lexed::External(External::Term(Term::Lit(Literal { value: v, tp: Box::new(tp.clone()) }), pos)), eaten)));
                    }
                }
            }
            LexerRule::Uri => {
                if chars[i] == '☞' {
                    let mut j = i + 1;
                    while j < chars.len() && !is_java_whitespace(chars[j]) && chars[j] != '(' && chars[j] != ')' {
                        j += 1;
                    }
                    let word: String = chars[i + 1..j].iter().collect();
                    return Ok(Some((Lexed::Token(Token { word, pos, ws_before: true }), j - i)));
                }
            }
            LexerRule::Interpolation { string, concat } => {
                if starts_with(chars, i, "s\"") {
                    let (parts, eaten) = lex_interpolation(chars, i, pos, max_nesting)?;
                    return Ok(Some((Lexed::External(External::Interpolation { parts, string: string.clone(), concat: concat.clone(), pos }), eaten)));
                }
            }
        }
    }
    Ok(None)
}

/// The lex functions of the realized types: returns the lexed text and the number of characters eaten.
fn lex_literal(kind: LexKind, chars: &[char], i: usize) -> Option<(String, usize)> {
    match kind {
        LexKind::Number => {
            // NumberLiteralLexer(false, false)
            let previous_ok = i == 0 || !(is_letter(chars[i - 1]) || is_connector(chars[i - 1]));
            if !(is_digit(chars[i]) && previous_ok) {
                return None;
            }
            let mut j = i;
            while j < chars.len() && is_digit(chars[j]) {
                j += 1;
            }
            let text: String = chars[i..j].iter().collect();
            // BigInt accepts only ASCII digits in practice for the numerals that matter here
            Some((text, j - i))
        }
        LexKind::Quoted => {
            // SymmetricEscapeLexer('"', '\\')
            if chars[i] != '"' {
                return None;
            }
            let mut j = i + 1;
            while j < chars.len() && chars[j] != '"' {
                if chars[j] == '\\' && chars.get(j + 1) == Some(&'"') {
                    j += 2;
                } else {
                    j += 1;
                }
            }
            let end = j.min(chars.len());
            let text: String = chars[i + 1..end].iter().collect();
            let eaten = if j < chars.len() { j + 1 - i } else { chars.len() - i };
            Some((text, eaten))
        }
        LexKind::Keywords => {
            // FiniteKeywordsLexer(List("true","false"))
            if i != 0 && (chars[i - 1].is_alphanumeric()) {
                return None;
            }
            for k in ["false", "true"] {
                if starts_with(chars, i, k) {
                    let after = chars.get(i + k.len());
                    if after.is_none_or(|c| !c.is_alphanumeric()) {
                        return Some((k.to_string(), k.len()));
                    }
                }
            }
            None
        }
        LexKind::NotationQuote => {
            // AsymmetricEscapeLexer("nt\"", "\"")
            if !starts_with(chars, i, "nt\"") {
                return None;
            }
            let first = i + 3;
            let mut j = first;
            let mut level = 1;
            while j < chars.len() && level > 0 {
                if starts_with(chars, j, "nt\"") {
                    level += 1;
                    j += 3;
                } else if chars[j] == '"' {
                    level -= 1;
                    j += 1;
                } else {
                    j += 1;
                }
            }
            let text_end = if level == 0 { j - 1 } else { j };
            Some((chars[first..text_end].iter().collect(), j - i))
        }
    }
}

/// `StringInterpolationLexer.apply` with operator `s`, string brackets `"` and term brackets `${` `}`.
fn lex_interpolation(chars: &[char], index: usize, fp: Pos, max_nesting: usize) -> Result<(Vec<InterpolationPart>, usize)> {
    let (sb, se, mb, me) = ("\"", "\"", "${", "}");
    let mut level = 1usize;
    let mut i = index + 2;
    let mut cur_pos = fp.after('s').after('"');
    let mut start_of_current = cur_pos;
    let mut parts = Vec::new();
    let mut current = String::new();
    while i < chars.len() && level > 0 {
        if starts_with(chars, i, sb) && level.is_multiple_of(2) {
            level += 1;
            current.push_str(sb);
            cur_pos = cur_pos.after_str(sb);
            i += 1;
        } else if starts_with(chars, i, se) && level % 2 == 1 {
            level -= 1;
            if level == 0 {
                parts.push(InterpolationPart::Str(std::mem::take(&mut current)));
            } else {
                current.push_str(se);
            }
            cur_pos = cur_pos.after_str(se);
            i += 1;
        } else if starts_with(chars, i, mb) && level % 2 == 1 {
            if level == 1 {
                parts.push(InterpolationPart::Str(std::mem::take(&mut current)));
                cur_pos = cur_pos.after_str(mb);
                start_of_current = cur_pos;
            } else {
                current.push_str(mb);
                cur_pos = cur_pos.after_str(mb);
            }
            i += 2;
            level += 1;
            if level / 2 > max_nesting {
                return Err(Error::at(ErrorKind::Limit, cur_pos, format!("interpolated strings nest more than {max_nesting} levels")));
            }
        } else if starts_with(chars, i, me) && level.is_multiple_of(2) {
            if level == 2 {
                parts.push(InterpolationPart::Mmt(std::mem::take(&mut current), start_of_current));
            } else {
                current.push_str(me);
            }
            cur_pos = cur_pos.after_str(me);
            i += 1;
            level -= 1;
        } else {
            current.push(chars[i]);
            cur_pos = cur_pos.after(chars[i]);
            i += 1;
        }
    }
    if !current.is_empty() {
        // end of input reached: MMT recovers by adding a final part
        if level == 1 {
            parts.push(InterpolationPart::Str(current));
        } else {
            parts.push(InterpolationPart::Mmt(current, start_of_current));
        }
    }
    Ok((parts, i - index))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn words(s: &str) -> Vec<String> {
        tokenize(s, Pos::START, &[], 10)
            .unwrap()
            .into_iter()
            .map(|t| match t {
                Lexed::Token(t) => t.word,
                Lexed::External(_) => "<ext>".into(),
            })
            .collect()
    }

    #[test]
    fn default_tokens() {
        assert_eq!(words("a ⟶ bc⟶d"), vec!["a", "⟶", "bc", "⟶", "d"]);
        assert_eq!(words("x_1+y"), vec!["x_1", "+", "y"]);
        assert_eq!(words("?T?c ur:?LF"), vec!["?T?c", "ur", ":", "?LF"]);
        assert_eq!(words("rules/lf?Realize"), vec!["rules/lf?Realize"]);
        assert_eq!(words("(f a)"), vec!["(", "f", "a", ")"]);
        assert_eq!(words("{x}"), vec!["{", "x", "}"]);
    }

    #[test]
    fn literal_lexers() {
        let string = Term::var("string");
        let lexers = vec![
            LexerRule::Interpolation { string: string.clone(), concat: Term::var("concat") },
            LexerRule::Uri,
            LexerRule::Literal { sem: SemType::String, tp: string.clone() },
            LexerRule::Literal { sem: SemType::Int, tp: Term::var("int") },
        ];
        let toks = tokenize("f \"a b\" 42 x42 s\"p${q}r\" ☞http://a.org?T?c", Pos::START, &lexers, 10).unwrap();
        // as in MMT, lexer extensions are tried at every position: the number lexer applies to the `2`
        // of `x42` because the character before it is no letter (`NumberLiteralLexer.applicable`)
        assert_eq!(toks.len(), 7, "{toks:?}");
        assert!(matches!(&toks[1], Lexed::External(External::Term(Term::Lit(Literal { value: LitValue::String(s), .. }), _)) if s == "a b"));
        assert!(matches!(&toks[2], Lexed::External(External::Term(Term::Lit(Literal { value: LitValue::Int(i), .. }), _)) if i.as_str() == "42"));
        assert!(matches!(&toks[3], Lexed::Token(t) if t.word == "x4"));
        assert!(matches!(&toks[4], Lexed::External(External::Term(Term::Lit(Literal { value: LitValue::Int(i), .. }), _)) if i.as_str() == "2"));
        match &toks[5] {
            Lexed::External(External::Interpolation { parts, .. }) => {
                assert_eq!(parts, &vec![InterpolationPart::Str("p".into()), InterpolationPart::Mmt("q".into(), Pos::START.after_str("f \"a b\" 42 x42 s\"p${")), InterpolationPart::Str("r".into())]);
            }
            t => panic!("{t:?}"),
        }
        assert!(matches!(&toks[6], Lexed::Token(t) if t.word == "http://a.org?T?c"));
    }
}
