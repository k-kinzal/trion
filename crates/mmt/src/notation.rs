//! Notations (doc/language/declarations.md, section Notations): the declaration syntax of mixfix
//! notations and the derived information the parser needs, as
//! `api/notations/Notation.scala`, `NotationComponents.scala`, `Arity.scala`
//! and `Precedence.scala` define them.
//!
//! A notation is a whitespace-separated list of markers, optionally preceded
//! by `meta M` and `block` and followed by `prec P`. The markers are
//! argument positions `n`, sequence arguments `nSEP…`, implicit arguments
//! `%In`, bound variables `Vn`, `VnT`, `VnSEP…`, `VnTSEP…`, label arguments
//! `Ln[T][D]` and `Ln[T][D]SEP…`, the symbol name `%n`, instance-name
//! delimiters `%iD`, the whitespace delimiter `%w`, escaped delimiters
//! `%Dtext` and right-associative delimiters `%Rtext`, and any other word as a
//! delimiter. The default precedence is 0, or -1000001 if the notation
//! contains `(`.
//!
//! Rejected as unsupported: fixity declarations `%%infix` and the like, and
//! local notations `%L..._`. Presentation markers (scripts, fractions,
//! tables) are not interpreted: as in MMT they are plain delimiters when a
//! notation is used for parsing.
//!
//! Argument and variable numbers are at most [`MAX_ARGUMENT_NUMBER`]: the
//! arity fills the numbers that the markers skip with implicit arguments, so
//! a larger number would make a notation of a few characters stand for
//! billions of arguments. MMT has no such bound; a notation above it is
//! rejected with [`ErrorKind::Limit`].

use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt;
use std::str::FromStr;

use crate::error::{Error, ErrorKind, Result};
use crate::uri::{LocalName, MPath, NamespaceMap, Path};

/// The largest argument or variable number of a notation that this crate reads.
pub const MAX_ARGUMENT_NUMBER: u32 = 1024;

/// An integer extended by infinities (`InfInt`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum InfInt {
    /// Minus infinity.
    NegInfinite,
    /// A finite value (a Java `Int`).
    Finite(i32),
    /// Infinity.
    Infinite,
}

impl InfInt {
    fn rank(self) -> (i8, i64) {
        match self {
            InfInt::NegInfinite => (0, 0),
            InfInt::Finite(i) => (1, i as i64),
            InfInt::Infinite => (2, 0),
        }
    }
}

impl PartialOrd for InfInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for InfInt {
    fn cmp(&self, other: &Self) -> Ordering {
        self.rank().cmp(&other.rank())
    }
}

/// A precedence: notations of lower precedence are scanned first and so grab larger subterms.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Precedence {
    prec: InfInt,
    lose_tie: bool,
}

impl Precedence {
    /// A precedence of a value; `lose_tie` makes it lose ties against notations of the same value (`P*`).
    pub fn new(prec: InfInt, lose_tie: bool) -> Precedence {
        Precedence { prec, lose_tie }
    }

    /// A finite precedence.
    pub fn integer(i: i32) -> Precedence {
        Precedence { prec: InfInt::Finite(i), lose_tie: false }
    }

    /// The value.
    pub fn value(self) -> InfInt {
        self.prec
    }

    /// Whether the notation loses ties against notations of the same value.
    pub fn loses_tie(self) -> bool {
        self.lose_tie
    }
    /// The precedence of the notations that consist of a name only.
    pub const INFINITE: Precedence = Precedence { prec: InfInt::Infinite, lose_tie: false };

    /// Parses `P`, `P*`, `infinity`, `-infinity`.
    pub fn parse(s: &str) -> Result<Precedence> {
        let lose_tie = s.ends_with('*');
        let core = s.replace('*', "");
        let prec = match core.trim() {
            "infinity" => InfInt::Infinite,
            "-infinity" => InfInt::NegInfinite,
            i => InfInt::Finite(i.parse::<i32>().map_err(|_| Error::new(ErrorKind::Notation, format!("illegal precedence: {s}")))?),
        };
        Ok(Precedence { prec, lose_tie })
    }
}

impl PartialOrd for Precedence {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Precedence {
    /// `Precedence.compare`: a tie is broken against the side that loses ties.
    fn cmp(&self, that: &Self) -> Ordering {
        if self == that {
            Ordering::Equal
        } else if self.prec < that.prec || (self.prec == that.prec && self.lose_tie && !that.lose_tie) {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    }
}

impl FromStr for Precedence {
    type Err = Error;

    fn from_str(s: &str) -> Result<Precedence> {
        Precedence::parse(s)
    }
}

impl fmt::Display for Precedence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.prec {
            InfInt::NegInfinite => write!(f, "-infinity")?,
            InfInt::Finite(i) => write!(f, "{i}")?,
            InfInt::Infinite => write!(f, "infinity")?,
        }
        if self.lose_tie {
            write!(f, "*")?;
        }
        Ok(())
    }
}

/// A delimiter: its text (`%w` for whitespace) and whether it associates to the left.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Delim {
    pub(crate) text: String,
    pub(crate) assoc_left: bool,
}

impl Delim {
    /// A left-associative delimiter. The text is what the notation
    /// declaration writes; [`Notation::new`] checks that it can be written
    /// there (non-empty, without whitespace and MMT's delimiters).
    pub fn new(text: impl Into<String>) -> Delim {
        Delim { text: text.into(), assoc_left: true }
    }

    /// A right-associative delimiter (`%R`).
    pub fn right(text: impl Into<String>) -> Delim {
        Delim { text: text.into(), assoc_left: false }
    }

    /// The text as declared (`%w` for whitespace).
    pub fn text(&self) -> &str {
        &self.text
    }

    /// Whether the delimiter associates to the left (false for `%R`).
    pub fn is_left_associative(&self) -> bool {
        self.assoc_left
    }

    /// The text that must occur in the input (`Delim.text`): a space for `%w`.
    pub fn matched_text(&self) -> &str {
        if self.text == "%w" {
            " "
        } else {
            &self.text
        }
    }
}

impl fmt::Display for Delim {
    /// A delimiter marker as `Delim.toString` writes it, escaping also
    /// delimiters that would otherwise read as other markers. Unlike MMT,
    /// a right-associative `%w` is written `%R%w`, so that it reads back as
    /// itself. The separator of a sequence marker is not written this way
    /// (see [`Marker`]'s `Display`).
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = &self.text;
        if s == "%w" && self.assoc_left {
            return f.write_str(s);
        }
        let mut cs = s.chars();
        let first = cs.next().unwrap_or(' ');
        let second = cs.next();
        let escape = !self.assoc_left
            || first == '%'
            || first == 'V'
            || (first == 'L' && second.is_some_and(|c| c.is_ascii_digit()))
            || first.is_ascii_digit()
            || s.ends_with('…')
            || s == "meta"
            || s == "block"
            || s == "prec";
        if escape {
            write!(f, "{}{s}", if self.assoc_left { "%D" } else { "%R" })
        } else {
            f.write_str(s)
        }
    }
}

/// Requirements of a label argument (`LabelInfo`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LabelInfo {
    /// A type is required.
    pub typed: bool,
    /// A definiens is required.
    pub defined: bool,
}

/// A marker of a notation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Marker {
    /// A delimiter.
    Delim(Delim),
    /// `%n`: the name of the symbol (or its shortest alias).
    SymbolName,
    /// `%iD`: the delimiter prefixed by the instance name.
    InstanceName(Delim),
    /// `n`: an argument.
    Arg(u32),
    /// `nSEP…`: a sequence of arguments.
    SeqArg(u32, Delim),
    /// `%In`: an implicit argument.
    ImplicitArg(u32),
    /// `Vn[T][SEP…]`: a bound variable or a sequence of them.
    Var {
        /// The position.
        number: u32,
        /// Whether a type is expected (inferred if omitted).
        typed: bool,
        /// The separator of a sequence of variables.
        sep: Option<Delim>,
    },
    /// `Ln[T][D]`: a label argument.
    LabelArg(u32, LabelInfo),
    /// `Ln[T][D]SEP…`: a sequence of label arguments.
    LabelSeqArg(u32, Delim, LabelInfo),
}

impl Marker {
    /// Parses one marker (`Marker.parse`).
    pub fn parse(s: &str) -> Result<Marker> {
        let m = Marker::parse_unbounded(s)?;
        m.check_number()?;
        Ok(m)
    }

    fn check_number(&self) -> Result<()> {
        match self.number() {
            Some(0) => Err(Error::new(ErrorKind::Notation, format!("argument numbers start at 1: {self}"))),
            Some(n) if n > MAX_ARGUMENT_NUMBER => Err(Error::new(ErrorKind::Limit, format!("argument number {n} is above {MAX_ARGUMENT_NUMBER}, the largest that this crate reads"))),
            _ => Ok(()),
        }
    }

    fn parse_unbounded(s: &str) -> Result<Marker> {
        let err = || Error::new(ErrorKind::Notation, format!("not a valid marker: {s}"));
        // a number that does not fit is above the bound
        let number = |digits: &str| -> Result<u32> {
            if digits.is_empty() {
                return Err(err());
            }
            Ok(digits.parse::<u32>().unwrap_or(u32::MAX))
        };
        let digit_at = |i: usize| s.chars().nth(i).is_some_and(|c| c.is_ascii_digit());
        if s.starts_with("%L") {
            return Err(Error::new(ErrorKind::Unsupported, format!("local notations (%L markers) are not supported: {s}")));
        }
        if let Some(rest) = s.strip_prefix("%i") {
            return match Marker::parse(rest)? {
                Marker::Delim(d) => Ok(Marker::InstanceName(d)),
                _ => Err(Error::new(ErrorKind::Notation, format!("%i must be followed by plain delimiter: {s}"))),
            };
        }
        if s == "%n" {
            return Ok(Marker::SymbolName);
        }
        if s.starts_with("%D") || s.starts_with("%R") {
            if s.len() == 2 {
                return Err(err());
            }
            return Ok(Marker::Delim(Delim { text: s[2..].to_string(), assoc_left: s.as_bytes()[1] == b'D' }));
        }
        if let Some(rest) = s.strip_prefix("%I") {
            if !rest.chars().all(|c| c.is_ascii_digit()) {
                return Err(err());
            }
            return Ok(Marker::ImplicitArg(number(rest)?));
        }
        if s.starts_with('V') && digit_at(1) {
            let digits: String = s[1..].chars().take_while(|c| c.is_ascii_digit()).collect();
            let number = number(&digits)?;
            let d = &s[1 + digits.len()..];
            return if d.is_empty() {
                Ok(Marker::Var { number, typed: false, sep: None })
            } else if d == "T" {
                Ok(Marker::Var { number, typed: true, sep: None })
            } else if d.starts_with('T') && d.ends_with('…') {
                Ok(Marker::Var { number, typed: true, sep: Some(Delim::new(&d[1..d.len() - '…'.len_utf8()])) })
            } else if d.ends_with('…') {
                Ok(Marker::Var { number, typed: false, sep: Some(Delim::new(&d[..d.len() - '…'.len_utf8()])) })
            } else {
                Err(err())
            };
        }
        if s.starts_with('L') && digit_at(1) {
            let digits: String = s[1..].chars().take_while(|c| c.is_ascii_digit()).collect();
            let number = number(&digits)?;
            let mut d = &s[1 + digits.len()..];
            let typed = d.starts_with('T');
            if typed {
                d = &d[1..];
            }
            let defined = d.starts_with('D');
            if defined {
                d = &d[1..];
            }
            let info = LabelInfo { typed, defined };
            return if let Some(sep) = d.strip_suffix('…') {
                if d.starts_with('d') {
                    return Err(Error::new(ErrorKind::Notation, "'d' not supported anymore, use %B at the beginning of the marker instead"));
                }
                Ok(Marker::LabelSeqArg(number, Delim::new(sep), info))
            } else {
                Ok(Marker::LabelArg(number, info))
            };
        }
        if digit_at(0) {
            if let Some(rest) = s.strip_suffix('…') {
                let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
                return Ok(Marker::SeqArg(number(&digits)?, Delim::new(&rest[digits.len()..])));
            }
            if !s.chars().all(|c| c.is_ascii_digit()) {
                return Err(err());
            }
            return Ok(Marker::Arg(number(s)?));
        }
        if s.is_empty() {
            return Err(err());
        }
        Ok(Marker::Delim(Delim::new(s)))
    }

    /// The position of an argument or variable marker.
    pub fn number(&self) -> Option<u32> {
        match self {
            Marker::Arg(n) | Marker::SeqArg(n, _) | Marker::ImplicitArg(n) | Marker::LabelArg(n, _) | Marker::LabelSeqArg(n, _, _) => Some(*n),
            Marker::Var { number, .. } => Some(*number),
            _ => None,
        }
    }

    /// The separator if this marker stands for a sequence (`isSequenceVia`).
    pub fn sequence_via(&self) -> Option<&Delim> {
        match self {
            Marker::SeqArg(_, d) | Marker::LabelSeqArg(_, d, _) => Some(d),
            Marker::Var { sep, .. } => sep.as_ref(),
            _ => None,
        }
    }

    /// Whether this is a delimiter of any kind.
    pub fn is_delimiter(&self) -> bool {
        matches!(self, Marker::Delim(_) | Marker::SymbolName | Marker::InstanceName(_))
    }

    /// Whether this is a variable marker.
    pub fn is_var(&self) -> bool {
        matches!(self, Marker::Var { .. })
    }

    /// Whether this is a child marker that is picked as one argument (`splitOffSimples`).
    pub(crate) fn is_simple_child(&self) -> bool {
        matches!(self, Marker::Arg(_) | Marker::LabelArg(_, _) | Marker::Var { sep: None, .. })
    }

    /// Whether this is a child (argument, variable, label) marker.
    pub(crate) fn is_child(&self) -> bool {
        self.number().is_some() && !matches!(self, Marker::ImplicitArg(_))
    }

    /// Replaces placeholder delimiters by the delimiter they stand for (`Delimiter.expand`).
    pub(crate) fn expand(&self, name: &LocalName, aliases: &[LocalName]) -> Marker {
        match self {
            Marker::SymbolName => {
                let mut candidates: Vec<LocalName> = std::iter::once(name.drop_complex()).chain(aliases.iter().cloned()).collect();
                candidates.sort_by_key(|n| n.len());
                let shortest = candidates.into_iter().find(|n| !n.is_empty());
                Marker::Delim(Delim::new(shortest.map(|n| n.to_path()).unwrap_or_default()))
            }
            Marker::InstanceName(base) => {
                let simple = name.drop_complex();
                let prefix = if simple.len() <= 1 { String::new() } else { format!("{}/", simple.init().to_path()) };
                Marker::Delim(Delim { text: format!("{prefix}{}", base.text), assoc_left: base.assoc_left })
            }
            m => m.clone(),
        }
    }
}

impl fmt::Display for Marker {
    /// The marker as a notation declaration writes it.
    ///
    /// The separator of a sequence marker (`nSEP…`, `VnTSEP…`, `LnTDSEP…`)
    /// is written as its text, because [`Marker::parse`] reads it as the
    /// text between the number (and flags) and `…` without escapes, as
    /// MMT's `Marker.parse` does. MMT's `toString` escapes it as a
    /// delimiter instead (`1%…` becomes `1%D%…`, which reads as the
    /// separator `%D%`); this crate does not follow that, so that every
    /// marker read prints as text that reads back as the same marker. A
    /// separator that no text reads back as (one that begins with a digit,
    /// or a right-associative one) is refused by [`Notation::new`].
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Marker::Delim(d) => write!(f, "{d}"),
            Marker::SymbolName => write!(f, "%n"),
            Marker::InstanceName(d) => write!(f, "%i{d}"),
            Marker::Arg(n) => write!(f, "{n}"),
            Marker::SeqArg(n, d) => write!(f, "{n}{}…", d.text),
            Marker::ImplicitArg(n) => write!(f, "%I{n}"),
            Marker::Var { number, typed, sep } => {
                write!(f, "V{number}{}", if *typed { "T" } else { "" })?;
                if let Some(s) = sep {
                    write!(f, "{}…", s.text)?;
                }
                Ok(())
            }
            Marker::LabelArg(n, i) => write!(f, "L{n}{}{}", if i.typed { "T" } else { "" }, if i.defined { "D" } else { "" }),
            Marker::LabelSeqArg(n, d, i) => write!(f, "L{n}{}{}{}…", if i.typed { "T" } else { "" }, if i.defined { "D" } else { "" }, d.text),
        }
    }
}

/// The arity of a notation (`Arity`): the arguments before the bound
/// variables (with implicit arguments filled in), the variables, and the
/// arguments after the variables.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Arity {
    /// Arguments before the variables.
    pub(crate) subargs: Vec<Marker>,
    /// The variables.
    pub(crate) variables: Vec<Marker>,
    /// Arguments after the variables.
    pub(crate) arguments: Vec<Marker>,
}

impl Arity {
    /// All components in abstract syntax order.
    pub fn components(&self) -> impl Iterator<Item = &Marker> {
        self.subargs.iter().chain(self.variables.iter()).chain(self.arguments.iter())
    }
    /// No arguments and no variables.
    pub fn is_constant(&self) -> bool {
        self.subargs.is_empty() && self.arguments.is_empty() && self.variables.is_empty()
    }
    /// The number of the first variable (`firstVarNumberIfAny`).
    pub fn first_var_number(&self) -> u32 {
        self.subargs.last().and_then(Marker::number).map(|n| n + 1).unwrap_or(1)
    }
    fn count(ms: &[Marker], seq: bool) -> usize {
        ms.iter()
            .filter(|m| match m {
                Marker::SeqArg(..) | Marker::LabelSeqArg(..) => seq,
                Marker::Var { sep, .. } => sep.is_some() == seq,
                _ => !seq,
            })
            .count()
    }
    /// Number of non-sequence arguments after the variables (implicit ones included).
    #[allow(dead_code)]
    pub(crate) fn num_normal_args(&self) -> usize {
        Arity::count(&self.arguments, false)
    }
    /// Number of sequence arguments after the variables.
    #[allow(dead_code)]
    pub(crate) fn num_seq_args(&self) -> usize {
        Arity::count(&self.arguments, true)
    }
}

/// A notation (`TextNotation` with mixfix fixity).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Notation {
    markers: Vec<Marker>,
    precedence: Precedence,
    meta: Option<MPath>,
    block: bool,
}

impl Notation {
    /// A notation of markers with a precedence. It is checked as
    /// [`Notation::parse`] checks a declaration, and so that its text reads
    /// back as itself: argument numbers are at most
    /// [`MAX_ARGUMENT_NUMBER`], no argument lies between bound variables, and
    /// every delimiter is non-empty and free of whitespace and of MMT's
    /// delimiters ❘ ❙ ❚.
    pub fn new(markers: Vec<Marker>, precedence: Precedence) -> Result<Notation> {
        let n = Notation { markers, precedence, meta: None, block: false };
        n.validate()?;
        Ok(n)
    }

    /// The same notation with `meta M`: the theory whose notation extension determines the term built.
    pub fn with_meta(mut self, meta: MPath) -> Notation {
        self.meta = Some(meta);
        self
    }

    /// The same notation with `block`: names introduced in arguments are visible in later arguments.
    pub fn with_block(mut self) -> Notation {
        self.block = true;
        self
    }

    /// The markers in concrete syntax order.
    pub fn markers(&self) -> &[Marker] {
        &self.markers
    }

    /// The precedence.
    pub fn precedence(&self) -> Precedence {
        self.precedence
    }

    /// The theory whose notation extension determines the term built (`meta M`).
    pub fn meta(&self) -> Option<&MPath> {
        self.meta.as_ref()
    }

    /// Whether names introduced in arguments are visible in later arguments.
    pub fn is_block(&self) -> bool {
        self.block
    }

    /// The notation of a name only, of infinite precedence (the parsing rule of a constant's name).
    pub(crate) fn name_only(name: String) -> Notation {
        Notation { markers: vec![Marker::Delim(Delim::new(name))], precedence: Precedence::INFINITE, meta: None, block: false }
    }

    fn validate(&self) -> Result<()> {
        let bad_text = |t: &str| t.is_empty() || t.chars().any(|c| c.is_whitespace() || crate::reader::is_delimiter(c));
        for m in &self.markers {
            m.check_number()?;
            let delims: Vec<&Delim> = match m {
                Marker::Delim(d) | Marker::InstanceName(d) | Marker::SeqArg(_, d) | Marker::LabelSeqArg(_, d, _) => vec![d],
                Marker::Var { sep: Some(d), .. } => vec![d],
                _ => vec![],
            };
            for d in delims {
                let separator = !matches!(m, Marker::Delim(_) | Marker::InstanceName(_));
                if d.text != "%w" && !(separator && d.text.is_empty()) && bad_text(&d.text) {
                    return Err(Error::new(ErrorKind::Notation, format!("the delimiter {:?} cannot be written in a notation", d.text)));
                }
            }
        }
        self.arity()?;
        let text = self.to_string();
        // a notation that does not read back as itself (for example `%n` written for a delimiter) cannot be printed
        let back = Notation::parse_unchecked(&text, &NamespaceMap::empty())?;
        let meta_free = |n: &Notation| Notation { meta: None, ..n.clone() };
        if meta_free(&back) != meta_free(self) {
            return Err(Error::new(ErrorKind::Notation, format!("the notation does not read back as itself: {text}")));
        }
        Ok(())
    }

    /// Parses a notation declaration (`TextNotation.parse`); `meta M` is resolved against `ns`.
    ///
    /// ```
    /// use mmt::uri::NamespaceMap;
    ///
    /// let n = mmt::Notation::parse("1 + 2 prec 10", &NamespaceMap::empty())?;
    /// assert_eq!(n.to_string(), "1 + 2 prec 10");
    /// assert!(mmt::Notation::parse("1 + 4294967296", &NamespaceMap::empty()).is_err());
    /// # Ok::<(), mmt::Error>(())
    /// ```
    pub fn parse(s: &str, ns: &NamespaceMap) -> Result<Notation> {
        Notation::parse_unchecked(s, ns)
    }

    fn parse_unchecked(s: &str, ns: &NamespaceMap) -> Result<Notation> {
        let mut tokens: Vec<&str> = s.split([' ', '\t', '\n', '\u{0B}', '\u{0C}', '\r']).filter(|t| !t.is_empty()).collect();
        let meta = match tokens.as_slice() {
            ["meta", mt, ..] => {
                let m = Path::parse_module(mt, ns)?;
                tokens.drain(..2);
                Some(m)
            }
            ["meta"] => return Err(Error::new(ErrorKind::Notation, "theory expected")),
            _ => None,
        };
        let block = tokens.first() == Some(&"block");
        if block {
            tokens.remove(0);
        }
        let precedence = match tokens.iter().position(|t| *t == "prec") {
            Some(i) => {
                let rest = tokens.split_off(i);
                match rest.as_slice() {
                    [_, p] => Precedence::parse(p)?,
                    _ => return Err(Error::new(ErrorKind::Notation, format!("precedence not found: {s}"))),
                }
            }
            None if s.contains('(') => Precedence::integer(-1000001),
            None => Precedence::integer(0),
        };
        if tokens.first().is_some_and(|t| t.starts_with("%%")) {
            return Err(Error::new(ErrorKind::Unsupported, format!("fixity declarations ({}) are not supported; write the markers instead", tokens[0])));
        }
        let markers = tokens.iter().map(|t| Marker::parse(t)).collect::<Result<Vec<_>>>()?;
        let n = Notation { markers, precedence, meta, block };
        n.arity()?;
        Ok(n)
    }

    /// The markers used for parsing: all but implicit arguments.
    pub(crate) fn parsing_markers(&self) -> impl Iterator<Item = &Marker> {
        self.markers.iter().filter(|m| !matches!(m, Marker::ImplicitArg(_)))
    }

    /// The arity (`TextNotation.arity`); fails on arguments between variables.
    pub(crate) fn arity(&self) -> Result<Arity> {
        let var_positions: Vec<u32> = self.markers.iter().filter(|m| m.is_var()).filter_map(Marker::number).collect();
        let first_var = var_positions.iter().min().copied().unwrap_or(0);
        let last_var = var_positions.iter().max().copied().unwrap_or(0);
        let mut subs = Vec::new();
        let mut vars = Vec::new();
        let mut args = Vec::new();
        for m in &self.markers {
            if m.is_var() {
                vars.push(m.clone());
            } else if let Some(n) = m.number() {
                if n > last_var {
                    args.push(m.clone());
                } else if n < first_var {
                    subs.push(m.clone());
                } else {
                    return Err(Error::new(ErrorKind::Notation, format!("illegal components in notation {self}")));
                }
            }
        }
        let key = |m: &Marker| m.number().unwrap_or(0);
        subs.sort_by_key(key);
        vars.sort_by_key(key);
        args.sort_by_key(key);
        fn add_implicits(ac: Vec<Marker>, from: u32) -> Vec<Marker> {
            let mut result = Vec::new();
            let mut i = from;
            for a in ac {
                let n = a.number().unwrap_or(0);
                while i < n {
                    result.push(Marker::ImplicitArg(i));
                    i += 1;
                }
                result.push(a);
                i += 1;
            }
            result
        }
        let mut subs = add_implicits(subs, 1);
        let args = add_implicits(args, last_var + 1);
        let last_sub = subs.last().and_then(Marker::number).unwrap_or(0);
        for i in (last_sub + 1)..first_var {
            subs.push(Marker::ImplicitArg(i));
        }
        let dedup = |v: Vec<Marker>| {
            let mut seen: HashSet<Marker> = HashSet::new();
            v.into_iter().filter(|m| seen.insert(m.clone())).collect::<Vec<_>>()
        };
        Ok(Arity { subargs: dedup(subs), variables: dedup(vars), arguments: dedup(args) })
    }

    /// The number of arguments before the first delimiter (`openArgs`).
    pub(crate) fn open_args(&self, from_right: bool) -> usize {
        let ms: Vec<&Marker> = if from_right { self.parsing_markers().collect::<Vec<_>>().into_iter().rev().collect() } else { self.parsing_markers().collect() };
        let mut i = 0;
        for m in ms {
            match m {
                Marker::Arg(_) | Marker::LabelArg(_, _) => i += 1,
                Marker::SeqArg(..) | Marker::LabelSeqArg(..) | Marker::Var { .. } => return i + 1,
                m if m.is_delimiter() => return i,
                _ => {}
            }
        }
        i
    }

    /// Whether there are arguments before the first delimiter.
    pub(crate) fn is_left_open(&self) -> bool {
        self.open_args(false) > 0
    }

    /// Whether two notations expect the same markers (`TextNotation.agree`).
    pub(crate) fn agree(&self, other: &Notation) -> bool {
        self.parsing_markers().eq(other.parsing_markers()) && self.parsing_markers().all(|m| !matches!(m, Marker::SymbolName | Marker::InstanceName(_)))
    }
}

impl FromStr for Notation {
    type Err = Error;

    /// As [`Notation::parse`] with an empty namespace map (`meta` needs an absolute URI).
    fn from_str(s: &str) -> Result<Notation> {
        Notation::parse(s, &NamespaceMap::empty())
    }
}

impl fmt::Display for Notation {
    /// `TextNotation.toText`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts: Vec<String> = Vec::new();
        if let Some(m) = &self.meta {
            parts.push(format!("meta {m}"));
        }
        if self.block {
            parts.push("block".into());
        }
        let ms: Vec<String> = self.markers.iter().map(|m| m.to_string()).collect();
        if !ms.is_empty() {
            parts.push(ms.join(" "));
        }
        let text = parts.join(" ");
        // the precedence that `parse` assumes when none is given
        let default = if text.contains('(') { Precedence::integer(-1000001) } else { Precedence::integer(0) };
        if self.precedence != default {
            parts.push(format!("prec {}", self.precedence));
        }
        f.write_str(&parts.join(" "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> Notation {
        Notation::parse(s, &NamespaceMap::empty()).unwrap()
    }

    /// A separator is read as text, without escapes, and printed as text;
    /// a delimiter is escaped with `%D` or `%R` where it would read as
    /// another marker. Every marker that reads prints as text that reads
    /// back as the same marker, whatever `%` it holds and wherever.
    #[test]
    fn separators_are_written_as_read_and_delimiters_are_escaped() {
        let back = |s: &str| {
            let m = Marker::parse(s).unwrap();
            assert_eq!(Marker::parse(&m.to_string()).unwrap(), m, "{s} printed as {m}");
            m
        };
        // separators: the text between the number (and flags) and `…`
        assert_eq!(back("1%…"), Marker::SeqArg(1, Delim::new("%")));
        assert_eq!(Marker::SeqArg(1, Delim::new("%")).to_string(), "1%…");
        assert_eq!(back("1%D%…"), Marker::SeqArg(1, Delim::new("%D%")));
        assert_eq!(back("1%R,…"), Marker::SeqArg(1, Delim::new("%R,")));
        assert_eq!(back("1%w…"), Marker::SeqArg(1, Delim::new("%w")));
        assert_eq!(back("1V…"), Marker::SeqArg(1, Delim::new("V")));
        assert_eq!(back("1…"), Marker::SeqArg(1, Delim::new("")));
        assert_eq!(back("1a……"), Marker::SeqArg(1, Delim::new("a…")));
        assert_eq!(back("V1%…"), Marker::Var { number: 1, typed: false, sep: Some(Delim::new("%")) });
        assert_eq!(back("V1T%…"), Marker::Var { number: 1, typed: true, sep: Some(Delim::new("%")) });
        assert_eq!(back("V1TT…"), Marker::Var { number: 1, typed: true, sep: Some(Delim::new("T")) });
        assert_eq!(back("L1%…"), Marker::LabelSeqArg(1, Delim::new("%"), LabelInfo { typed: false, defined: false }));
        assert_eq!(back("L1TD%D…"), Marker::LabelSeqArg(1, Delim::new("%D"), LabelInfo { typed: true, defined: true }));
        // delimiters: escaped where the text would read as another marker
        assert_eq!(back("%D%x"), Marker::Delim(Delim::new("%x")));
        assert_eq!(Marker::Delim(Delim::new("%x")).to_string(), "%D%x");
        assert_eq!(back("%x"), Marker::Delim(Delim::new("%x")));
        assert_eq!(back("%R%w"), Marker::Delim(Delim::right("%w")));
        assert_eq!(Marker::Delim(Delim::right("%w")).to_string(), "%R%w");
        assert_eq!(back("%w"), Marker::Delim(Delim::new("%w")));
        assert_eq!(back("%i%x"), Marker::InstanceName(Delim::new("%x")));
        assert_eq!(back("%i%R%"), Marker::InstanceName(Delim::right("%")));
        for s in ["%D1", "%DV1", "%DL1", "%D%n", "%D%I1", "%Dx…", "%R…", "%Dprec"] {
            back(s);
        }
        // a separator that no text reads back as cannot be built
        for m in [
            Marker::SeqArg(1, Delim::new("2,")),
            Marker::SeqArg(1, Delim::right(",")),
            Marker::Var { number: 1, typed: false, sep: Some(Delim::new("T,")) },
            Marker::LabelSeqArg(1, Delim::new("D,"), LabelInfo { typed: false, defined: false }),
        ] {
            assert!(Notation::new(vec![Marker::Delim(Delim::new("f")), m.clone()], Precedence::integer(0)).is_err(), "{m}");
        }
    }

    #[test]
    fn lf_notations() {
        let pi = parse("{ V1T,… } 2 prec -10000");
        assert_eq!(pi.markers[1], Marker::Var { number: 1, typed: true, sep: Some(Delim::new(",")) });
        assert_eq!(pi.precedence, Precedence::integer(-10000));
        let arrow = parse("1⟶…        prec  -9990");
        assert_eq!(arrow.markers, vec![Marker::SeqArg(1, Delim::new("⟶"))]);
        assert_eq!(arrow.open_args(false), 1);
        let apply = parse("1%w…        prec -10");
        assert_eq!(apply.markers, vec![Marker::SeqArg(1, Delim::new("%w"))]);
        let brackets = parse("( 1 ) prec -1000005");
        assert_eq!(brackets.precedence, Precedence::integer(-1000005));
        assert_eq!(parse("( 1 )").precedence, Precedence::integer(-1000001));
    }

    #[test]
    fn arity_with_implicit_arguments() {
        // doc/language/declarations.md, Notations: falsE 1 %I2
        let n = parse("falsE 1 %I2");
        let a = n.arity().unwrap();
        assert_eq!(a.arguments, vec![Marker::Arg(1), Marker::ImplicitArg(2)]);
        let n = parse("PROVE %I1");
        assert_eq!(n.arity().unwrap().arguments, vec![Marker::ImplicitArg(1)]);
        let n = parse("2 + 3");
        assert_eq!(n.arity().unwrap().arguments, vec![Marker::ImplicitArg(1), Marker::Arg(2), Marker::Arg(3)]);
    }

    #[test]
    fn printing_round_trips() {
        for s in ["1 + 2 prec 10", "%R⇒ 1 2", "{ V1T,… } 2 prec -10000", "%D10 1", "%DV 1", "≪ 1 @ 2,… ≫ prec -100002", "block {| L1T,… |} prec -1000005", "meta http://a.org?T 1 ∘ 2", "%n 1 prec 3*"] {
            let n = parse(s);
            assert_eq!(parse(&n.to_string()), n, "{s} printed as {n}");
        }
    }

    #[test]
    fn argument_numbers_are_bounded() {
        assert_eq!(Notation::parse("f 4000000000", &NamespaceMap::empty()).unwrap_err().kind(), ErrorKind::Limit);
        assert_eq!(Notation::parse("f 99999999999999999999", &NamespaceMap::empty()).unwrap_err().kind(), ErrorKind::Limit);
        assert_eq!(Notation::parse("V4294967296T,… 1", &NamespaceMap::empty()).unwrap_err().kind(), ErrorKind::Limit);
        assert_eq!(Notation::parse("%I0 1", &NamespaceMap::empty()).unwrap_err().kind(), ErrorKind::Notation);
        let n = parse(&format!("f {MAX_ARGUMENT_NUMBER}"));
        assert_eq!(n.arity().unwrap().arguments.len(), MAX_ARGUMENT_NUMBER as usize);
    }

    #[test]
    fn constructed_notations_are_validated() {
        assert!(Notation::new(vec![Marker::Arg(1), Marker::Delim(Delim::new("+")), Marker::Arg(2)], Precedence::integer(10)).is_ok());
        for bad in ["", "a b", "x❙"] {
            let e = Notation::new(vec![Marker::Arg(1), Marker::Delim(Delim::new(bad))], Precedence::integer(0)).unwrap_err();
            assert_eq!(e.kind(), ErrorKind::Notation, "{bad:?}");
        }
        assert_eq!(Notation::new(vec![Marker::Arg(5000)], Precedence::integer(0)).unwrap_err().kind(), ErrorKind::Limit);
        // an argument between two bound variables
        assert!(Notation::new(vec![Marker::Var { number: 1, typed: false, sep: None }, Marker::Arg(2), Marker::Var { number: 3, typed: false, sep: None }], Precedence::integer(0)).is_err());
    }

    #[test]
    fn precedence_order() {
        assert!(Precedence::parse("5*").unwrap() < Precedence::integer(5));
        assert!(Precedence::integer(-10) < Precedence::integer(0));
        assert!(Precedence::INFINITE > Precedence::integer(1000));
    }
}
