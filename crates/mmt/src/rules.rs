//! The rules that change how objects are read. MMT's `rule` declarations
//! name Scala objects by URIs of the scheme `scala`
//! (`api/symbols/RuleConstant.scala`), which MMT loads by reflection. Most
//! rules belong to type checking or computation and have no effect on
//! reading; the ones that do are lexer extensions (`api/parser/LexerExtension.scala`)
//! and notation extensions (`api/notations/NotationExtension.scala`). This
//! crate has no JVM, so it recognizes those by the Java class name the URI
//! denotes (`scala://lf.mmt.kwarc.info?LFHOAS` and
//! `scala://mmt.kwarc.info/lf?LFHOAS` both denote `info.kwarc.mmt.lf.LFHOAS`).
//!
//! Read with effect: `Realize c S` for the semantic types `StandardString`,
//! `StandardInt`, `StandardNat`, `StandardPositive` and `StandardBool` (a
//! lexer of literals of type `c`), `StandardStringInterpolation`,
//! `MMTURILexer`, `NotationRealizedType` and `LFHOAS` (application and
//! binding through LF's `apply` and `lambda`).
//!
//! Rejected as unsupported, because MMT reads objects with them and this
//! crate cannot: `Realize` of the semantic types `StandardRat`,
//! `StandardDouble`, `URILiteral`, `UUIDLiteral` and `TermLiteral`, and the
//! lexers `info.kwarc.mmt.quotation.TermLiteralRule` and
//! `info.kwarc.mmt.semiformal.InformalLiterals` of MMT/urtheories.
//!
//! Every other rule is kept as [`RuleKind::Other`] and has no effect on
//! reading. A lexer or notation extension of a plugin that is not listed
//! above is therefore not applied; the objects that use it are not read as
//! MMT reads them (typically an unbound token is reported).

use std::fmt;

use crate::error::{Error, ErrorKind, Result};
pub use crate::lexer::SemType;
use crate::term::Term;
use crate::uri::{GlobalName, MPath};

/// LF's application, `http://cds.omdoc.org/urtheories?LambdaPi?apply`: under
/// the rule `LFHOAS`, a notation of `c` with arguments `a…` builds
/// `apply(c, a…)` (an OMA with this head).
pub fn hoas_apply() -> GlobalName {
    crate::paths::apply()
}

/// LF's λ-abstraction, `http://cds.omdoc.org/urtheories?LambdaPi?lambda`:
/// under the rule `LFHOAS`, a notation of `c` with bound variables builds
/// `apply(c, lambda(variables, arguments))`.
pub fn hoas_lambda() -> GlobalName {
    crate::paths::lambda()
}

/// The semantic types of `Realize` that MMT reads literals of and this crate does not.
const UNSUPPORTED_LITERALS: &[&str] = &["StandardRat", "StandardDouble", "URILiteral", "UUIDLiteral", "TermLiteral"];

/// The lexer extensions of MMT/urtheories that this crate does not implement.
const UNSUPPORTED_LEXERS: &[&str] = &["info.kwarc.mmt.quotation.TermLiteralRule", "info.kwarc.mmt.semiformal.InformalLiterals"];

/// What a rule declaration does to reading.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RuleKind {
    /// `Realize c S` for a semantic type `S`: literals of `S` are read as objects of type `c`.
    Literal {
        /// The realized constant, the type of the literals.
        syn: GlobalName,
        /// The semantic type.
        sem: SemType,
    },
    /// `StandardStringInterpolation string concat`: `s"…${t}…"`.
    StringInterpolation {
        /// The string type.
        string: GlobalName,
        /// The concatenation.
        concat: GlobalName,
    },
    /// `MMTURILexer`: the token `☞URI`.
    UriLexer,
    /// `NotationRealizedType`: notation literals `nt"…"` of type `http://cds.omdoc.org/mmt?mmt?notation`.
    NotationLiteral,
    /// `LFHOAS`: notations are applied and bind through LF's `apply` and `lambda`.
    Hoas,
    /// Any other rule, by Java class name: it has no effect on reading.
    Other(String),
}

impl fmt::Display for RuleKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuleKind::Literal { syn, sem } => write!(f, "literals of {sem:?} of type {syn}"),
            RuleKind::StringInterpolation { string, concat } => write!(f, "string interpolation with {string} and {concat}"),
            RuleKind::UriLexer => f.write_str("URI tokens"),
            RuleKind::NotationLiteral => f.write_str("notation literals"),
            RuleKind::Hoas => f.write_str("LF's higher-order abstract syntax"),
            RuleKind::Other(class) => write!(f, "{class}"),
        }
    }
}

/// The Java class name a `scala` URI denotes, as `Rule.loadRule` computes it.
pub fn class_name(p: &MPath) -> Option<String> {
    let u = p.doc().uri();
    if u.scheme() != Some("scala") {
        return None;
    }
    let mut parts: Vec<String> = u.authority().unwrap_or("").split('.').filter(|s| !s.is_empty()).rev().map(str::to_string).collect();
    parts.extend(u.path_no_trailing_slash().iter().filter(|s| !s.is_empty()).cloned());
    parts.extend(p.name().steps().iter().map(|s| s.to_path()));
    Some(parts.join("."))
}

/// What a rule declaration does to reading, from its parsed term (`RuleConstantInterpreter`).
pub fn interpret(rule: &Term) -> Result<RuleKind> {
    let malformed = || Error::new(ErrorKind::Structure, format!("cannot interpret as a rule: {rule}"));
    let (p, args): (&MPath, &[Term]) = match rule {
        Term::Module(p) => (p, &[]),
        Term::App(f, args) => match &**f {
            Term::Module(p) => (p, args.as_slice()),
            _ => return Err(malformed()),
        },
        _ => return Err(malformed()),
    };
    let Some(class) = class_name(p) else {
        return Err(Error::new(ErrorKind::Structure, format!("cannot interpret as a rule: {p} is not a scala URI")));
    };
    let sym = |t: &Term| match t {
        Term::Sym(g) => Ok(g.clone()),
        _ => Err(Error::new(ErrorKind::Structure, format!("rule {class}: identifier expected, found {t}"))),
    };
    match class.as_str() {
        "info.kwarc.mmt.lf.Realize" => {
            let [c, Term::Module(s)] = args else { return Err(Error::new(ErrorKind::Structure, "Realize expects a constant and a semantic object")) };
            let Some(name) = class_name(s) else { return Err(Error::new(ErrorKind::Structure, format!("Realize: {s} is not a scala URI"))) };
            let sem = match name.strip_prefix("info.kwarc.mmt.api.uom.") {
                Some("StandardString") => SemType::String,
                Some("StandardInt") => SemType::Int,
                Some("StandardNat") => SemType::Nat,
                Some("StandardPositive") => SemType::Positive,
                Some("StandardBool") => SemType::Bool,
                Some(t) if UNSUPPORTED_LITERALS.contains(&t) => return Err(Error::new(ErrorKind::Unsupported, format!("literals of the semantic type {name} are not supported"))),
                _ => return Ok(RuleKind::Other(class)),
            };
            Ok(RuleKind::Literal { syn: sym(c)?, sem })
        }
        "info.kwarc.mmt.literals.StandardStringInterpolation" => match args {
            [s, c] => Ok(RuleKind::StringInterpolation { string: sym(s)?, concat: sym(c)? }),
            _ => Err(Error::new(ErrorKind::Structure, "StandardStringInterpolation expects the string type and the concatenation")),
        },
        "info.kwarc.mmt.api.parser.MMTURILexer" if args.is_empty() => Ok(RuleKind::UriLexer),
        "info.kwarc.mmt.api.notations.NotationRealizedType" if args.is_empty() => Ok(RuleKind::NotationLiteral),
        "info.kwarc.mmt.lf.LFHOAS" if args.is_empty() => Ok(RuleKind::Hoas),
        c if UNSUPPORTED_LEXERS.contains(&c) => Err(Error::new(ErrorKind::Unsupported, format!("the lexer extension {class} is not supported"))),
        _ => Ok(RuleKind::Other(class)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn class_names() {
        let a = MPath::parse_plain("scala://lf.mmt.kwarc.info?LFHOAS").unwrap();
        let b = MPath::parse_plain("scala://mmt.kwarc.info/lf?LFHOAS").unwrap();
        assert_eq!(class_name(&a).unwrap(), "info.kwarc.mmt.lf.LFHOAS");
        assert_eq!(interpret(&Term::Module(b)).unwrap(), RuleKind::Hoas);
        let c = MPath::parse_plain("scala://mmt.kwarc.info/api/uom?StringOperations/Concat").unwrap();
        assert_eq!(class_name(&c).unwrap(), "info.kwarc.mmt.api.uom.StringOperations.Concat");
        let beta = MPath::parse_plain("scala://lf.mmt.kwarc.info?Beta").unwrap();
        assert_eq!(interpret(&Term::Module(beta)).unwrap(), RuleKind::Other("info.kwarc.mmt.lf.Beta".to_string()));
        let rat = Term::app(Term::Module(MPath::parse_plain("scala://lf.mmt.kwarc.info?Realize").unwrap()), vec![Term::Sym(MPath::parse_plain("http://a.org?T").unwrap().sym("q")), Term::Module(MPath::parse_plain("scala://mmt.kwarc.info/api/uom?StandardRat").unwrap())]);
        assert_eq!(interpret(&rat).unwrap_err().kind(), ErrorKind::Unsupported);
        let string = Term::app(Term::Module(MPath::parse_plain("scala://lf.mmt.kwarc.info?Realize").unwrap()), vec![Term::Sym(MPath::parse_plain("http://a.org?T").unwrap().sym("s")), Term::Module(MPath::parse_plain("scala://mmt.kwarc.info/api/uom?StandardString").unwrap())]);
        assert!(matches!(interpret(&string).unwrap(), RuleKind::Literal { sem: SemType::String, .. }));
    }
}
