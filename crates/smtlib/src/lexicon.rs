//! The lexicon of SMT-LIB 2.7 (§3.1): tokens and the values they carry.
//!
//! A source text is a sequence of tokens separated by whitespace and
//! comments. The tokens are the two parentheses, numerals, decimals,
//! hexadecimals, binaries, string literals, symbols, keywords and reserved
//! words. Each kind of token that carries a value has a type here whose
//! constructor accepts exactly the values the grammar admits, so that every
//! value can be printed back as a token that reads as the same value.
//!
//! Two lexical facts shape the types. A simple symbol and the quoted symbol
//! with the same characters are the same symbol (`abc` and `|abc|`, §3.1), so
//! [`Symbol`] stores only the characters and the printer quotes exactly when
//! the characters do not form a simple symbol or form a reserved word. A
//! string literal has one escape sequence, `""` (§3.1), so
//! [`StringLiteral`] stores the characters it denotes.
//!
//! [`Dialect`] is the reader and printer configuration. The default is strict
//! SMT-LIB 2.7. A dialect is a format built on SMT-LIB that writes some
//! things SMT-LIB does not; its extensions are explicit and none of them is
//! SMT-LIB:
//!
//! - more simple-symbol characters ([`Dialect::with_symbol_char`]): MoXI
//!   writes the next-state copy of `x` as `x'`; the strict printer quotes
//!   such symbols (`|x'|`) so that strict readers still accept them;
//! - signed and fractional number literals
//!   ([`Dialect::with_extended_literals`], [`ExtendedConstant`]): Alethe
//!   writes `-1`, `-1.5` and `1/2` as constants, which strict SMT-LIB reads
//!   as a symbol (`-1`) or rejects (`1/2`); each such literal abbreviates an
//!   SMT-LIB term (`(- 1)`, `(- 1.5)`, `(/ 1 2)`);
//! - binders named by a symbol ([`Dialect::with_binder`]): Alethe's
//!   `(choice ((x S)) φ)`.
//!
//! A value that uses an extension prints, and reads back, in the dialect
//! that has it. The strict printer writes SMT-LIB only: a symbol with extra
//! characters quoted, and an extended literal as the term it abbreviates
//! (`-1` as `(- 1)`), which reads back as that term rather than as the
//! literal. A dialect binder has no SMT-LIB form; the printer writes it as
//! a list headed by its name, which a strict reader reads as an
//! application.

use crate::error::{Error, ErrorKind, Position, Result};
use std::fmt;

/// The characters other than letters and digits that may occur in a simple
/// symbol (§3.1): `~ ! @ $ % ^ & * _ - + = < > . ? /`.
const SIMPLE_SYMBOL_PUNCTUATION: &str = "~!@$%^&*_-+=<>.?/";

/// A white space character (§3.1): tab, line feed, carriage return, space.
pub(crate) fn is_white_space_char(c: char) -> bool {
    matches!(c, '\t' | '\n' | '\r' | ' ')
}

/// A printable character (§3.1): 32 to 126, and 128 on.
pub(crate) fn is_printable_char(c: char) -> bool {
    let code = c as u32;
    (32..=126).contains(&code) || code >= 128
}

/// The reader and printer configuration: strict SMT-LIB 2.7 by default.
///
/// The extensions (see the module documentation) are additional
/// simple-symbol characters, signed and fractional literals, and binders
/// named by a symbol; a dialect never changes keywords or reserved words.
/// The dialect also bounds the nesting depth that the reader accepts.
///
/// ```
/// use smtlib::{Dialect, Symbol, Term};
///
/// // MoXI writes the next-state copy of `x` as `x'`.
/// let moxi = Dialect::strict().with_symbol_char('\'').unwrap();
/// let term = Term::parse_in("(= x' (+ x 1))", &moxi).unwrap();
/// assert_eq!(term.to_text(&moxi), "(= x' (+ x 1))");
/// // The strict printer quotes it, so that a strict reader reads it.
/// assert_eq!(term.to_string(), "(= |x'| (+ x 1))");
///
/// // Alethe writes negative literals and a `choice` binder.
/// let alethe = Dialect::strict().with_extended_literals().with_binder(Symbol::new("choice").unwrap()).unwrap();
/// let term = Term::parse_in("(choice ((x Int)) (= x -1))", &alethe).unwrap();
/// assert!(matches!(term, Term::Binder(..)));
/// assert_eq!(term.to_string(), "(choice ((x Int)) (= x (- 1)))");
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dialect {
    extra_symbol_chars: Vec<char>,
    max_depth: usize,
    extended_literals: bool,
    binders: Vec<Symbol>,
}

impl Default for Dialect {
    fn default() -> Dialect {
        Dialect::strict()
    }
}

impl Dialect {
    /// The nesting depth of parentheses that the reader accepts by default.
    pub const DEFAULT_MAX_DEPTH: usize = 1000;

    /// Strict SMT-LIB 2.7.
    pub fn strict() -> Dialect {
        Dialect { extra_symbol_chars: Vec::new(), max_depth: Dialect::DEFAULT_MAX_DEPTH, extended_literals: false, binders: Vec::new() }
    }

    /// This dialect, extended with the literals of [`ExtendedConstant`]:
    /// `-n`, `-d`, `n/m` and `-n/m` for numerals `n`, `m` (`m` not 0) and
    /// decimals `d` (dialect extension; not SMT-LIB). The reader then reads
    /// a run of simple-symbol characters that starts with a digit or `-`
    /// as one of these literals, a numeral or a decimal when it is one;
    /// such a run that starts with a digit and is none of them is an error,
    /// and any other run is a symbol (`-`, `-x`). The printer quotes a
    /// symbol whose characters spell one of these literals (`|-1|`).
    pub fn with_extended_literals(mut self) -> Dialect {
        self.extended_literals = true;
        self
    }

    /// Whether this dialect reads the literals of [`ExtendedConstant`].
    pub fn has_extended_literals(&self) -> bool {
        self.extended_literals
    }

    /// This dialect, extended with a binder named `name` (dialect
    /// extension; not SMT-LIB): `(name ((x σ)…) t)` is read as
    /// [`crate::Term::Binder`] instead of an application of `name`. An
    /// error when `name` is a reserved word, which cannot head a binder
    /// that reads like `forall`.
    pub fn with_binder(mut self, name: Symbol) -> Result<Dialect> {
        if Reserved::from_name(name.as_str()).is_some() {
            return Err(Error::construction(format!("{name} is a reserved word and cannot name a dialect binder")));
        }
        if !self.binders.contains(&name) {
            self.binders.push(name);
        }
        Ok(self)
    }

    /// Whether `name` is a binder of this dialect.
    pub fn is_binder(&self, name: &Symbol) -> bool {
        self.binders.contains(name)
    }

    /// The binders this dialect adds.
    pub fn binders(&self) -> &[Symbol] {
        &self.binders
    }

    /// Whether the printer of this dialect writes `symbol` quoted: exactly
    /// when its characters are not a simple symbol of the dialect.
    pub fn quotes(&self, symbol: &Symbol) -> bool {
        !self.is_simple_symbol(symbol.as_str())
    }

    /// This dialect, extended so that `c` may occur in simple symbols
    /// (dialect extension; not SMT-LIB). `c` must be a printable ASCII
    /// character that is not a letter, digit, delimiter (`(`, `)`, `"`, `|`,
    /// `;`), `:`, `#` or `\\`, because those already have a lexical role.
    pub fn with_symbol_char(mut self, c: char) -> Result<Dialect> {
        let reserved_role = c.is_ascii_alphanumeric() || "()\"|;:#\\".contains(c) || SIMPLE_SYMBOL_PUNCTUATION.contains(c);
        if !c.is_ascii() || !is_printable_char(c) || c == ' ' || reserved_role {
            return Err(Error::construction(format!("{c:?} cannot be added to simple symbols: it is not a free printable ASCII character")));
        }
        if !self.extra_symbol_chars.contains(&c) {
            self.extra_symbol_chars.push(c);
        }
        Ok(self)
    }

    /// The characters this dialect adds to simple symbols.
    pub fn extra_symbol_chars(&self) -> &[char] {
        &self.extra_symbol_chars
    }

    /// This dialect with a different limit on the nesting depth of
    /// parentheses that the reader accepts; deeper text is an error of
    /// kind [`crate::ErrorKind::Depth`]. Reading, printing and dropping
    /// are iterative and need no limit; the limit bounds the recursion of
    /// the derived traits (`Clone`, `PartialEq`, `Hash`, `Ord`, `Debug`)
    /// on the values that are read, and the default keeps them within a
    /// 2 MiB stack.
    pub fn with_max_depth(mut self, depth: usize) -> Dialect {
        self.max_depth = depth;
        self
    }

    /// The nesting depth the reader accepts.
    pub fn max_depth(&self) -> usize {
        self.max_depth
    }

    /// Whether this dialect is strict SMT-LIB 2.7: no extension (the depth
    /// limit is not an extension).
    pub fn is_strict(&self) -> bool {
        self.extra_symbol_chars.is_empty() && !self.extended_literals && self.binders.is_empty()
    }

    /// Whether `c` may occur in a simple symbol of this dialect.
    pub fn is_symbol_char(&self, c: char) -> bool {
        c.is_ascii_alphanumeric() || SIMPLE_SYMBOL_PUNCTUATION.contains(c) || self.extra_symbol_chars.contains(&c)
    }

    /// Whether `name` is a simple symbol of this dialect: non-empty, made of
    /// symbol characters, not starting with a digit, not a reserved word,
    /// and, with extended literals, not spelling one.
    pub fn is_simple_symbol(&self, name: &str) -> bool {
        let mut chars = name.chars();
        match chars.next() {
            None => false,
            Some(first) if first.is_ascii_digit() || !self.is_symbol_char(first) => false,
            Some(_) => chars.all(|c| self.is_symbol_char(c)) && Reserved::from_name(name).is_none() && !(self.extended_literals && ExtendedConstant::parse(name).is_some()),
        }
    }
}

fn is_strict_symbol_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || SIMPLE_SYMBOL_PUNCTUATION.contains(c)
}

/// A numeral (§3.1): `0`, or a non-empty sequence of digits not starting
/// with `0`. Numerals are unbounded; the digits are kept as text.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Numeral(String);

impl Numeral {
    /// The numeral written `digits`.
    pub fn new(digits: &str) -> Result<Numeral> {
        let ok = !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit()) && (digits == "0" || !digits.starts_with('0'));
        if ok {
            Ok(Numeral(digits.to_string()))
        } else {
            Err(Error::construction(format!("{digits:?} is not a numeral: a numeral is 0 or digits not starting with 0 (§3.1)")))
        }
    }

    /// The digits.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// The value, when it fits in a `u64`.
    pub fn to_u64(&self) -> Option<u64> {
        self.0.parse().ok()
    }

    /// Whether this numeral is `0`.
    pub fn is_zero(&self) -> bool {
        self.0 == "0"
    }

    /// A value that allocates nothing, for the place of a term that is
    /// being dropped; never visible.
    pub(crate) fn hole() -> Numeral {
        Numeral(String::new())
    }
}

impl From<u64> for Numeral {
    fn from(n: u64) -> Numeral {
        Numeral(n.to_string())
    }
}

impl From<u32> for Numeral {
    fn from(n: u32) -> Numeral {
        Numeral(n.to_string())
    }
}

impl From<usize> for Numeral {
    fn from(n: usize) -> Numeral {
        Numeral(n.to_string())
    }
}

impl fmt::Display for Numeral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// A decimal (§3.1): a numeral, a dot, and a non-empty sequence of digits
/// (`⟨numeral⟩.0*⟨numeral⟩`). The text is kept as written: `1.5` and `1.50`
/// are different tokens.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Decimal(String);

impl Decimal {
    /// The decimal written `text`.
    pub fn new(text: &str) -> Result<Decimal> {
        let ok = match text.split_once('.') {
            Some((whole, fraction)) => Numeral::new(whole).is_ok() && !fraction.is_empty() && fraction.chars().all(|c| c.is_ascii_digit()),
            None => false,
        };
        if ok {
            Ok(Decimal(text.to_string()))
        } else {
            Err(Error::construction(format!("{text:?} is not a decimal: a decimal is ⟨numeral⟩.0*⟨numeral⟩ (§3.1)")))
        }
    }

    /// The decimal with integer part `whole` and fraction digits `fraction`.
    pub fn from_parts(whole: &Numeral, fraction: &str) -> Result<Decimal> {
        Decimal::new(&format!("{whole}.{fraction}"))
    }

    /// The text, as written.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// The integer part.
    pub fn whole(&self) -> &str {
        self.0.split_once('.').map(|(w, _)| w).unwrap_or(&self.0)
    }

    /// The digits after the dot.
    pub fn fraction(&self) -> &str {
        self.0.split_once('.').map(|(_, f)| f).unwrap_or("")
    }
}

impl fmt::Display for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// A hexadecimal (§3.1): `#x` followed by a non-empty, case-insensitive
/// sequence of hexadecimal digits. The digits are kept as written.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Hexadecimal(String);

impl Hexadecimal {
    /// The hexadecimal `#x` followed by `digits`.
    pub fn new(digits: &str) -> Result<Hexadecimal> {
        if !digits.is_empty() && digits.chars().all(|c| c.is_ascii_hexdigit()) {
            Ok(Hexadecimal(digits.to_string()))
        } else {
            Err(Error::construction(format!("{digits:?} is not a sequence of hexadecimal digits (§3.1)")))
        }
    }

    /// The digits after `#x`.
    pub fn digits(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Hexadecimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#x{}", self.0)
    }
}

/// A binary (§3.1): `#b` followed by a non-empty sequence of `0` and `1`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Binary(String);

impl Binary {
    /// The binary `#b` followed by `digits`.
    pub fn new(digits: &str) -> Result<Binary> {
        if !digits.is_empty() && digits.chars().all(|c| c == '0' || c == '1') {
            Ok(Binary(digits.to_string()))
        } else {
            Err(Error::construction(format!("{digits:?} is not a sequence of binary digits (§3.1)")))
        }
    }

    /// The digits after `#b`.
    pub fn digits(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Binary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#b{}", self.0)
    }
}

/// A string literal (§3.1): the characters it denotes, each a printable or
/// white space character. The printer doubles `"` (the only escape sequence).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StringLiteral(String);

impl StringLiteral {
    /// The literal denoting `content`.
    pub fn new(content: &str) -> Result<StringLiteral> {
        match content.chars().find(|&c| !is_printable_char(c) && !is_white_space_char(c)) {
            None => Ok(StringLiteral(content.to_string())),
            Some(c) => Err(Error::construction(format!("a string literal cannot contain {c:?}: only printable and white space characters (§3.1)"))),
        }
    }

    /// The characters the literal denotes.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for StringLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{}\"", self.0.replace('"', "\"\""))
    }
}

/// A special constant (§3.2): `⟨numeral⟩ | ⟨decimal⟩ | ⟨hexadecimal⟩ |
/// ⟨binary⟩ | ⟨string⟩`, and the dialect literals of [`ExtendedConstant`].
///
/// The dialect literals are a variant here, rather than a type parameter of
/// the term and S-expression types, so that one [`crate::Term`] type serves
/// SMT-LIB and its dialects: a dialect's reader produces them, the strict
/// reader never does, and every consumer that matches on the SMT-LIB
/// variants sees an extended literal as one more case it can reject.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum SpecConstant {
    /// A numeral.
    Numeral(Numeral),
    /// A decimal.
    Decimal(Decimal),
    /// A hexadecimal.
    Hexadecimal(Hexadecimal),
    /// A binary.
    Binary(Binary),
    /// A string literal.
    String(StringLiteral),
    /// A dialect literal (not SMT-LIB; [`Dialect::with_extended_literals`]).
    Extended(ExtendedConstant),
}

impl fmt::Display for SpecConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SpecConstant::Numeral(n) => n.fmt(f),
            SpecConstant::Decimal(d) => d.fmt(f),
            SpecConstant::Hexadecimal(h) => h.fmt(f),
            SpecConstant::Binary(b) => b.fmt(f),
            SpecConstant::String(s) => s.fmt(f),
            SpecConstant::Extended(e) => e.fmt(f),
        }
    }
}

/// A signed or fractional number literal of a dialect
/// ([`Dialect::with_extended_literals`]; not SMT-LIB). Each abbreviates an
/// SMT-LIB term ([`ExtendedConstant::expansion`]); Alethe's ⟨nonpositive
/// numeral⟩, ⟨nonpositive decimal⟩ and ⟨rational⟩ are these.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum ExtendedConstant {
    /// `-n`, abbreviating `(- n)`.
    NegativeNumeral(Numeral),
    /// `-d`, abbreviating `(- d)`.
    NegativeDecimal(Decimal),
    /// `n/m` or `-n/m` with `m` not 0, abbreviating `(/ n m)` or
    /// `(- (/ n m))`. The digits are kept as written: `2/4` and `1/2` are
    /// different literals. Built with [`ExtendedConstant::fraction`], which
    /// refuses the denominator 0.
    #[non_exhaustive]
    Fraction {
        /// Whether the literal starts with `-`.
        negative: bool,
        /// The numerator, without the sign.
        numerator: Numeral,
        /// The denominator, not 0.
        denominator: Numeral,
    },
}

impl ExtendedConstant {
    /// The fraction `numerator/denominator`, negated when `negative`; the
    /// denominator must not be 0.
    pub fn fraction(negative: bool, numerator: Numeral, denominator: Numeral) -> Result<ExtendedConstant> {
        if denominator.is_zero() {
            return Err(Error::construction(format!("{numerator}/0 is not a fraction literal: the denominator is a positive numeral")));
        }
        Ok(ExtendedConstant::Fraction { negative, numerator, denominator })
    }

    /// The literal spelled `text`, if `text` spells one.
    pub fn parse(text: &str) -> Option<ExtendedConstant> {
        let (negative, rest) = match text.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, text),
        };
        if let Some((n, m)) = rest.split_once('/') {
            let numerator = Numeral::new(n).ok()?;
            let denominator = Numeral::new(m).ok()?;
            return ExtendedConstant::fraction(negative, numerator, denominator).ok();
        }
        if !negative {
            return None;
        }
        if let Ok(n) = Numeral::new(rest) {
            return Some(ExtendedConstant::NegativeNumeral(n));
        }
        Decimal::new(rest).ok().map(ExtendedConstant::NegativeDecimal)
    }
}

impl fmt::Display for ExtendedConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExtendedConstant::NegativeNumeral(n) => write!(f, "-{n}"),
            ExtendedConstant::NegativeDecimal(d) => write!(f, "-{d}"),
            ExtendedConstant::Fraction { negative, numerator, denominator } => write!(f, "{}{numerator}/{denominator}", if *negative { "-" } else { "" }),
        }
    }
}

/// A symbol (§3.1), simple or quoted. The two spellings of the same
/// characters are the same symbol, so only the characters are stored: any
/// sequence of printable and white space characters without `|` and `\`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(String);

impl Symbol {
    /// The symbol made of `name`'s characters.
    pub fn new(name: &str) -> Result<Symbol> {
        match name.chars().find(|&c| c == '|' || c == '\\' || (!is_printable_char(c) && !is_white_space_char(c))) {
            None => Ok(Symbol(name.to_string())),
            Some(c) => Err(Error::construction(format!("a symbol cannot contain {c:?}: a quoted symbol excludes | and \\ and non-printable characters (§3.1)"))),
        }
    }

    /// The characters of the symbol.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// The token that denotes this symbol in `dialect`: the characters
    /// themselves when they form a simple symbol of the dialect, otherwise
    /// the quoted symbol `|…|`.
    pub fn to_text(&self, dialect: &Dialect) -> String {
        if dialect.quotes(self) {
            format!("|{}|", self.0)
        } else {
            self.0.clone()
        }
    }
}

impl fmt::Display for Symbol {
    /// The token of the symbol in strict SMT-LIB 2.7.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if Dialect::strict().quotes(self) {
            write!(f, "|{}|", self.0)
        } else {
            f.write_str(&self.0)
        }
    }
}

impl std::str::FromStr for Symbol {
    type Err = Error;

    /// Reads a symbol token, simple or quoted, in strict SMT-LIB 2.7: `abc`
    /// and `|abc|` give the same symbol. For the symbol made of given
    /// characters, use [`Symbol::new`].
    fn from_str(text: &str) -> Result<Symbol> {
        let tokens = tokenize(text, &Dialect::strict())?;
        match tokens.as_slice() {
            [Token { kind: TokenKind::Symbol(symbol), .. }] => Ok(symbol.clone()),
            _ => Err(Error::at(ErrorKind::Syntax, tokens.first().map_or(Position::START, |t| t.position), format!("{text:?} is not one symbol token"))),
        }
    }
}

/// A keyword (§3.1): `:` followed by a non-empty sequence of simple-symbol
/// characters. The stored name excludes the colon.
///
/// §3.1 defines a keyword as `:⟨simple_symbol⟩` but lists `:56` among its
/// examples; this crate follows the example and admits a name that starts
/// with a digit or spells a reserved word. Dialect characters
/// ([`Dialect::with_symbol_char`]) are not admitted in keywords, because a
/// keyword cannot be quoted for a strict reader.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Keyword(String);

impl Keyword {
    /// The keyword `:name`. A leading colon in `name` is accepted and dropped.
    pub fn new(name: &str) -> Result<Keyword> {
        let name = name.strip_prefix(':').unwrap_or(name);
        if !name.is_empty() && name.chars().all(is_strict_symbol_char) {
            Ok(Keyword(name.to_string()))
        } else {
            Err(Error::construction(format!("{name:?} is not a keyword name: a keyword is : followed by simple-symbol characters (§3.1)")))
        }
    }

    /// The name, without the colon.
    pub fn name(&self) -> &str {
        &self.0
    }

    /// Whether this keyword is `:name`.
    pub fn is(&self, name: &str) -> bool {
        self.0 == name.strip_prefix(':').unwrap_or(name)
    }
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ":{}", self.0)
    }
}

macro_rules! reserved_words {
    ($($variant:ident => $text:literal),* $(,)?) => {
        /// A reserved word (§3.1): the basic set and every command name.
        ///
        /// §3.1 makes "each command name in the scripting language defined in
        /// Section 3.11" a reserved word; the list in Appendix B omits
        /// `define-funs-rec`, which Figure 3.7 defines, and this crate follows
        /// §3.1 and reserves it.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[non_exhaustive]
        pub enum Reserved {
            $(
                #[doc = concat!("`", $text, "`")]
                $variant,
            )*
        }

        impl Reserved {
            /// Every reserved word.
            pub const ALL: &'static [Reserved] = &[$(Reserved::$variant),*];

            /// The text of the reserved word.
            pub fn as_str(self) -> &'static str {
                match self {
                    $(Reserved::$variant => $text,)*
                }
            }

            /// The reserved word spelled `name`, if any.
            pub fn from_name(name: &str) -> Option<Reserved> {
                match name {
                    $($text => Some(Reserved::$variant),)*
                    _ => None,
                }
            }
        }
    };
}

reserved_words! {
    Binary => "BINARY",
    Decimal => "DECIMAL",
    Hexadecimal => "HEXADECIMAL",
    Numeral => "NUMERAL",
    String => "STRING",
    Underscore => "_",
    Bang => "!",
    As => "as",
    Lambda => "lambda",
    Let => "let",
    Exists => "exists",
    Forall => "forall",
    Match => "match",
    Par => "par",
    Assert => "assert",
    CheckSat => "check-sat",
    CheckSatAssuming => "check-sat-assuming",
    DeclareConst => "declare-const",
    DeclareDatatype => "declare-datatype",
    DeclareDatatypes => "declare-datatypes",
    DeclareFun => "declare-fun",
    DeclareSort => "declare-sort",
    DeclareSortParameter => "declare-sort-parameter",
    DefineConst => "define-const",
    DefineFun => "define-fun",
    DefineFunRec => "define-fun-rec",
    DefineFunsRec => "define-funs-rec",
    DefineSort => "define-sort",
    Echo => "echo",
    Exit => "exit",
    GetAssertions => "get-assertions",
    GetAssignment => "get-assignment",
    GetInfo => "get-info",
    GetModel => "get-model",
    GetOption => "get-option",
    GetProof => "get-proof",
    GetUnsatAssumptions => "get-unsat-assumptions",
    GetUnsatCore => "get-unsat-core",
    GetValue => "get-value",
    Pop => "pop",
    Push => "push",
    Reset => "reset",
    ResetAssertions => "reset-assertions",
    SetInfo => "set-info",
    SetLogic => "set-logic",
    SetOption => "set-option",
}

impl fmt::Display for Reserved {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A token of §3.1 with the position of its first character.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Token {
    /// Where the token starts.
    pub(crate) position: Position,
    /// What the token is.
    pub(crate) kind: TokenKind,
}

/// The kinds of tokens of §3.1.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TokenKind {
    /// `(`
    Open,
    /// `)`
    Close,
    /// A special constant.
    Constant(SpecConstant),
    /// A symbol, simple or quoted.
    Symbol(Symbol),
    /// A keyword.
    Keyword(Keyword),
    /// A reserved word.
    Reserved(Reserved),
}

/// Splits `text` into the tokens of §3.1, skipping whitespace and comments.
pub(crate) fn tokenize(text: &str, dialect: &Dialect) -> Result<Vec<Token>> {
    Lexer::new(text, dialect).run()
}

struct Lexer<'a> {
    chars: Vec<char>,
    index: usize,
    position: Position,
    dialect: &'a Dialect,
}

impl<'a> Lexer<'a> {
    fn new(text: &str, dialect: &'a Dialect) -> Lexer<'a> {
        Lexer { chars: text.chars().collect(), index: 0, position: Position::START, dialect }
    }

    fn position(&self) -> Position {
        self.position
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.index).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<char> {
        self.chars.get(self.index + offset).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.chars.get(self.index).copied()?;
        self.index += 1;
        self.position = self.position.after(c, self.peek());
        Some(c)
    }

    fn error(&self, position: Position, message: impl Into<String>) -> Error {
        Error::at(ErrorKind::Lexical, position, message)
    }

    fn run(mut self) -> Result<Vec<Token>> {
        let mut tokens = Vec::new();
        while let Some(c) = self.peek() {
            let position = self.position();
            if is_white_space_char(c) {
                self.bump();
                continue;
            }
            if c == ';' {
                while let Some(c) = self.peek() {
                    if c == '\n' || c == '\r' {
                        break;
                    }
                    self.bump();
                }
                continue;
            }
            let kind = match c {
                '(' => {
                    self.bump();
                    TokenKind::Open
                }
                ')' => {
                    self.bump();
                    TokenKind::Close
                }
                '"' => self.string(position)?,
                '|' => self.quoted_symbol(position)?,
                ':' => self.keyword(position)?,
                '#' => self.radix(position)?,
                c if self.dialect.extended_literals && (c.is_ascii_digit() || (c == '-' && self.peek_at(1).is_some_and(|d| d.is_ascii_digit()))) => self.extended(position)?,
                c if c.is_ascii_digit() => self.number(position)?,
                c if self.dialect.is_symbol_char(c) => self.simple_symbol(),
                c => return Err(self.error(position, format!("unexpected character {c:?}: not the start of any token of §3.1"))),
            };
            tokens.push(Token { position, kind });
        }
        Ok(tokens)
    }

    fn string(&mut self, start: Position) -> Result<TokenKind> {
        self.bump();
        let mut content = String::new();
        loop {
            let position = self.position();
            match self.bump() {
                None => return Err(self.error(start, "unterminated string literal")),
                Some('"') => {
                    if self.peek() == Some('"') {
                        self.bump();
                        content.push('"');
                    } else {
                        break;
                    }
                }
                Some(c) if is_printable_char(c) || is_white_space_char(c) => content.push(c),
                Some(c) => return Err(self.error(position, format!("{c:?} cannot occur in a string literal: only printable and white space characters (§3.1)"))),
            }
        }
        Ok(TokenKind::Constant(SpecConstant::String(StringLiteral(content))))
    }

    fn quoted_symbol(&mut self, start: Position) -> Result<TokenKind> {
        self.bump();
        let mut name = String::new();
        loop {
            let position = self.position();
            match self.bump() {
                None => return Err(self.error(start, "unterminated quoted symbol")),
                Some('|') => break,
                Some('\\') => return Err(self.error(position, "a quoted symbol cannot contain \\ (§3.1)")),
                Some(c) if is_printable_char(c) || is_white_space_char(c) => name.push(c),
                Some(c) => return Err(self.error(position, format!("{c:?} cannot occur in a quoted symbol (§3.1)"))),
            }
        }
        Ok(TokenKind::Symbol(Symbol(name)))
    }

    fn take_symbol_chars(&mut self) -> String {
        let mut text = String::new();
        while let Some(c) = self.peek() {
            if self.dialect.is_symbol_char(c) {
                text.push(c);
                self.bump();
            } else {
                break;
            }
        }
        text
    }

    fn keyword(&mut self, start: Position) -> Result<TokenKind> {
        self.bump();
        let mut name = String::new();
        while let Some(c) = self.peek() {
            if is_strict_symbol_char(c) {
                name.push(c);
                self.bump();
            } else {
                break;
            }
        }
        if name.is_empty() {
            return Err(self.error(start, "a keyword needs a name after the colon (§3.1)"));
        }
        self.expect_boundary("keyword")?;
        Ok(TokenKind::Keyword(Keyword(name)))
    }

    /// A run of symbol characters that starts with a digit or `-`, in a
    /// dialect with extended literals.
    fn extended(&mut self, start: Position) -> Result<TokenKind> {
        let text = self.take_symbol_chars();
        if let Some(e) = ExtendedConstant::parse(&text) {
            return Ok(TokenKind::Constant(SpecConstant::Extended(e)));
        }
        if let Ok(n) = Numeral::new(&text) {
            return Ok(TokenKind::Constant(SpecConstant::Numeral(n)));
        }
        if let Ok(d) = Decimal::new(&text) {
            return Ok(TokenKind::Constant(SpecConstant::Decimal(d)));
        }
        if text.starts_with(|c: char| c.is_ascii_digit()) {
            return Err(self.error(start, format!("{text} is not a numeral, a decimal or a fraction literal, and a symbol does not start with a digit (§3.1)")));
        }
        Ok(match Reserved::from_name(&text) {
            Some(reserved) => TokenKind::Reserved(reserved),
            None => TokenKind::Symbol(Symbol(text)),
        })
    }

    fn simple_symbol(&mut self) -> TokenKind {
        let text = self.take_symbol_chars();
        match Reserved::from_name(&text) {
            Some(reserved) => TokenKind::Reserved(reserved),
            None => TokenKind::Symbol(Symbol(text)),
        }
    }

    /// A numeral, decimal, hexadecimal or binary must not run into a symbol
    /// character: `12abc` is not two tokens.
    fn expect_boundary(&self, what: &str) -> Result<()> {
        match self.peek() {
            Some(c) if self.dialect.is_symbol_char(c) || c == '#' || c == ':' => Err(self.error(self.position(), format!("{c:?} cannot follow a {what} without whitespace"))),
            _ => Ok(()),
        }
    }

    fn digits(&mut self) -> String {
        let mut text = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                text.push(c);
                self.bump();
            } else {
                break;
            }
        }
        text
    }

    fn number(&mut self, start: Position) -> Result<TokenKind> {
        let whole = self.digits();
        if whole.len() > 1 && whole.starts_with('0') {
            return Err(self.error(start, format!("{whole} is not a numeral: a numeral other than 0 does not start with 0 (§3.1)")));
        }
        if self.peek() == Some('.') && self.peek_at(1).is_some_and(|c| c.is_ascii_digit()) {
            self.bump();
            let fraction = self.digits();
            self.expect_boundary("decimal")?;
            return Ok(TokenKind::Constant(SpecConstant::Decimal(Decimal(format!("{whole}.{fraction}")))));
        }
        self.expect_boundary("numeral")?;
        Ok(TokenKind::Constant(SpecConstant::Numeral(Numeral(whole))))
    }

    fn radix(&mut self, start: Position) -> Result<TokenKind> {
        self.bump();
        let base = self.bump();
        let mut digits = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric() {
                digits.push(c);
                self.bump();
            } else {
                break;
            }
        }
        let constant = match base {
            Some('x') => Hexadecimal::new(&digits).map(SpecConstant::Hexadecimal),
            Some('b') => Binary::new(&digits).map(SpecConstant::Binary),
            _ => return Err(self.error(start, "# must be followed by x (hexadecimal) or b (binary) (§3.1)")),
        };
        let constant = constant.map_err(|e| self.error(start, e.message().to_string()))?;
        self.expect_boundary("literal")?;
        Ok(TokenKind::Constant(constant))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(text: &str) -> Vec<TokenKind> {
        tokenize(text, &Dialect::strict()).unwrap().into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn quoted_and_simple_symbols_are_the_same_symbol() {
        assert_eq!(kinds("abc |abc|"), vec![TokenKind::Symbol(Symbol::new("abc").unwrap()); 2]);
    }

    #[test]
    fn positions_count_lines_and_columns() {
        let tokens = tokenize("(a\n  b)", &Dialect::strict()).unwrap();
        assert_eq!(tokens[2].position, Position::new(2, 3));
        // A carriage return alone ends a line, and so does \r\n, once.
        let tokens = tokenize("a\rb\r\nc\n\nd", &Dialect::strict()).unwrap();
        let lines: Vec<usize> = tokens.iter().map(|t| t.position.line()).collect();
        assert_eq!(lines, [1, 2, 3, 5]);
        assert_eq!(Position::START.advance("a\rb\r\nc\n\nd"), Position::new(5, 2));
    }

    #[test]
    fn primes_are_a_dialect_extension() {
        assert!(tokenize("x'", &Dialect::strict()).is_err());
        let moxi = Dialect::strict().with_symbol_char('\'').unwrap();
        assert_eq!(kinds_in("x'", &moxi), vec![TokenKind::Symbol(Symbol::new("x'").unwrap())]);
        assert_eq!(Symbol::new("x'").unwrap().to_string(), "|x'|");
        assert_eq!(Symbol::new("x'").unwrap().to_text(&moxi), "x'");
    }

    fn kinds_in(text: &str, dialect: &Dialect) -> Vec<TokenKind> {
        tokenize(text, dialect).unwrap().into_iter().map(|t| t.kind).collect()
    }
}
