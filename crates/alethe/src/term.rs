//! Proof terms (§2.1, Figure 2) as `smtlib` terms read in the Alethe
//! dialect.
//!
//! ```text
//! ⟨proof_term⟩ ≔ ⟨term⟩ extended with
//!                  ( choice ( ⟨sorted_var⟩ ) ⟨proof_term⟩ )
//!                | ⟨rational⟩ | ⟨nonpositive_numeral⟩ | ⟨nonpositive_decimal⟩
//! A ⟨symbol⟩ is an SMT-LIB ⟨symbol⟩ that is not a
//!     −⟨numeral⟩/⟨positive_numeral⟩, −⟨numeral⟩, or −⟨decimal⟩.
//! ```
//!
//! The extensions are switches of the `smtlib` reader ([`dialect`]): `-n`,
//! `-d` and `n/m` read as [`smtlib::ExtendedConstant`], and a list headed
//! by `choice` reads as [`Term::Binder`]. Since every list headed by
//! `choice` is the binder, `choice` cannot be applied as a function in a
//! proof; Carcara reserves it too (`src/parser/lexer.rs`,
//! `Reserved::Choice`).
//!
//! Three things the `smtlib` reader admits are not proof terms, and
//! [`validate`] rejects them wherever a proof term, sort, sorted variable or
//! ⟨symbol⟩ occurs:
//!
//! - a symbol that spells one of the number literals, quoted or not
//!   (`|-1|`, `|-1/2|`, `|-0.5|`): Figure 2 excludes it from ⟨symbol⟩
//!   ("These sequences cannot be used as symbols when using Alethe"), a
//!   syntax error;
//! - a `choice` that binds other than one variable, or another dialect
//!   binder: Figure 2 writes `(choice ( ⟨sorted_var⟩ ) ⟨proof_term⟩ )`, a
//!   syntax error;
//! - what SMT-LIB 2.7 added to the grammar of terms of SMT-LIB 2.6,
//!   namely `lambda` and the `_` wildcard of match patterns. Figure 2 takes
//!   ⟨term⟩ "as defined in the SMT-LIB standard [3, Appendix B]", and
//!   reference \[3\] is *The SMT-LIB Standard: Version 2.6*; these are
//!   rejected as unsupported.
//!
//! The function `@` and the sort constructor `->` of SMT-LIB 2.7 are
//! symbols of its HO-Core theory, not productions of its grammar, and both
//! are symbols in SMT-LIB 2.6 as well; they are read as symbols like any
//! other. Which theory symbols a proof may use is not syntax.
//!
//! [`validate`] folds the term with `smtlib`'s iterative
//! [`Term::try_fold`] and [`Sort::fold`], so a deep term built in code does
//! not exhaust the call stack, and visits each node once. The fold also
//! measures the nesting of the term's text against the reader's limit
//! ([`dialect`]), so that what the constructors of [`crate::proof`] accept
//! reads back.
//!
//! §4.1 (p. 24) writes the bit-vector constant bvⁱₙ as "(_ @bv𝑛 𝑖 )": the
//! numeral after `@bv` is the width and the index is the value, the
//! reverse of SMT-LIB's `(_ bvX n)`. [`bv_constant`] and
//! [`as_bv_constant`] write and recognise that form. Carcara writes the
//! constant `(@bv i n)` instead (`src/ast/term.rs`, `BvConst: "@bv"`);
//! `tests/carcara.rs` records the difference.

use crate::error::{Error, ErrorKind, Result};
use smtlib::lexicon::{Dialect, ExtendedConstant, Numeral, Symbol};
use smtlib::sexpr::{Atom, SExpr, Spanned, SpannedKind};
use smtlib::term::{Attribute, AttributeValue, Identifier, Index, NonEmpty, Pattern, QualIdentifier, Sort, SortedVar, Term};
use std::sync::OnceLock;

/// The name of the choice binder.
const CHOICE: &str = "choice";

/// The Alethe dialect of SMT-LIB: strict SMT-LIB with the number literals
/// and the choice binder of Figure 2.
///
/// Its nesting limit is `smtlib`'s default,
/// [`smtlib::Dialect::DEFAULT_MAX_DEPTH`] parentheses: deeper text is an
/// [`ErrorKind::Depth`] error, and the constructors of [`crate::proof`]
/// refuse a command whose text would nest deeper, so that every value they
/// build reads back. This is the one limit of the crate; in solver output
/// a proof is enclosed by one more pair of parentheses, which
/// [`crate::read_output`] admits.
///
/// ```
/// let term = smtlib::sexpr::read("(choice ((x Int)) (> x -1/2))", alethe::dialect()).unwrap();
/// assert!(term.as_list().is_some());
/// assert_eq!(alethe::dialect().max_depth(), smtlib::Dialect::DEFAULT_MAX_DEPTH);
/// ```
pub fn dialect() -> &'static Dialect {
    static DIALECT: OnceLock<Dialect> = OnceLock::new();
    DIALECT.get_or_init(|| Dialect::strict().with_extended_literals().with_binder(Symbol::new(CHOICE).expect("choice is a symbol")).expect("choice is not a reserved word"))
}

/// [`dialect`] with room for the parentheses that enclose a proof in
/// solver output.
pub(crate) fn output_dialect() -> &'static Dialect {
    static DIALECT: OnceLock<Dialect> = OnceLock::new();
    DIALECT.get_or_init(|| dialect().clone().with_max_depth(dialect().max_depth() + 1))
}

/// Whether `symbol` is an Alethe ⟨symbol⟩: Figure 2 excludes the SMT-LIB
/// symbols that spell `-n/m`, `-n` or `-d`, quoted forms included (a
/// quoted symbol is the same symbol as the simple one, SMT-LIB §3.1).
///
/// ```
/// use smtlib::Symbol;
/// assert!(alethe::term::is_alethe_symbol(&Symbol::new("-x").unwrap()));
/// assert!(!alethe::term::is_alethe_symbol(&Symbol::new("-1/2").unwrap()));
/// ```
pub fn is_alethe_symbol(symbol: &Symbol) -> bool {
    ExtendedConstant::parse(symbol.as_str()).is_none()
}

/// Reads a proof term from `text`.
///
/// ```
/// let term = alethe::term::parse("(* -1 y)").unwrap();
/// assert_eq!(alethe::term::to_text(&term), "(* -1 y)");
/// assert!(alethe::term::parse("(f |-1|)").is_err());
/// ```
pub fn parse(text: &str) -> Result<Term> {
    from_spanned(&smtlib::sexpr::read(text, dialect())?)
}

/// Reads a proof term from an S-expression read in [`dialect`].
pub fn from_spanned(node: &Spanned) -> Result<Term> {
    symbols_in(node)?;
    from_spanned_at(node, 0)
}

/// Reads a proof term enclosed by `depth` parentheses, from a node whose
/// symbols [`symbols_in`] has checked.
pub(crate) fn from_spanned_at(node: &Spanned, depth: usize) -> Result<Term> {
    let term = Term::from_spanned_in(node, dialect())?;
    validate_term_at(&term, depth, Symbols::Checked).map_err(|e| e.or_at(node.position()))?;
    Ok(term)
}

/// The text of a proof term.
pub fn to_text(term: &Term) -> String {
    term.to_text(dialect())
}

/// Whether a check looks at the ⟨symbol⟩s it meets: `Checked` when they
/// were read from text that [`symbols_in`] has already checked, so that
/// each symbol is checked once.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Symbols {
    Check,
    Checked,
}

fn unsupported(what: &str) -> Error {
    Error::new(ErrorKind::Unsupported, format!("{what} is SMT-LIB 2.7; a ⟨proof_term⟩ is an SMT-LIB 2.6 term (Figure 2 and reference [3]), so this crate does not support it"))
}

fn excluded(symbol: &Symbol) -> Error {
    Error::new(ErrorKind::Syntax, format!("the symbol {} spells a number literal of Figure 2, which \"cannot be used as symbols when using Alethe\" (§2.1)", symbol.as_str()))
}

/// Rejects a ⟨symbol⟩ that Figure 2 excludes.
pub(crate) fn validate_symbol(symbol: &Symbol) -> Result<()> {
    if is_alethe_symbol(symbol) {
        Ok(())
    } else {
        Err(excluded(symbol))
    }
}

/// Checks every symbol atom of a node read from text, so that the error
/// carries the position of the symbol itself.
pub(crate) fn symbols_in(node: &Spanned) -> Result<()> {
    let mut stack = vec![node];
    while let Some(node) = stack.pop() {
        match node.kind() {
            SpannedKind::Atom(Atom::Symbol(s)) if !is_alethe_symbol(s) => return Err(excluded(s).or_at(node.position())),
            SpannedKind::Atom(_) => {}
            SpannedKind::List(items) => stack.extend(items.iter()),
        }
    }
    Ok(())
}

/// The Alethe rules that the `smtlib` reader does not apply, checked over
/// `smtlib`'s iterative folds. Each method checks one part of the syntax
/// and returns the nesting of its text: the number of parentheses its
/// deepest token is enclosed by within the part itself.
struct Check {
    symbols: Symbols,
}

/// The nesting of a list whose items nest as deep as `items`.
fn list(items: impl IntoIterator<Item = usize>) -> usize {
    1 + items.into_iter().max().unwrap_or(0)
}

impl Check {
    fn symbol(&self, symbol: &Symbol) -> Result<usize> {
        if self.symbols == Symbols::Check {
            validate_symbol(symbol)?;
        }
        Ok(0)
    }

    /// `f` or `(_ f i…)`.
    fn identifier(&self, id: &Identifier) -> Result<usize> {
        self.symbol(id.symbol())?;
        for index in id.indices() {
            if let Index::Symbol(s) = index {
                self.symbol(s)?;
            }
        }
        Ok(usize::from(!id.indices().is_empty()))
    }

    fn sort(&self, sort: &Sort) -> Result<usize> {
        sort.fold(|s, arguments: Vec<Result<usize>>| {
            let id = self.identifier(s.identifier())?;
            if arguments.is_empty() {
                return Ok(id);
            }
            Ok(list(std::iter::once(Ok(id)).chain(arguments).collect::<Result<Vec<_>>>()?))
        })
    }

    /// `(x S)`.
    fn var(&self, var: &SortedVar) -> Result<usize> {
        self.symbol(var.variable())?;
        Ok(list([self.sort(var.sort())?]))
    }

    /// `((x S)…)`.
    fn vars(&self, vars: &[SortedVar]) -> Result<usize> {
        Ok(list(vars.iter().map(|v| self.var(v)).collect::<Result<Vec<_>>>()?))
    }

    /// `f`, `(_ f i…)` or `(as f S)`.
    fn qual(&self, q: &QualIdentifier) -> Result<usize> {
        let id = self.identifier(q.identifier())?;
        match q.sort() {
            Some(sort) => Ok(list([id, self.sort(sort)?])),
            None => Ok(id),
        }
    }

    /// An S-expression of an attribute value, walked with an explicit
    /// stack.
    fn sexpr(&self, sexpr: &SExpr) -> Result<usize> {
        let mut deepest = 0;
        let mut stack = vec![(sexpr, 0)];
        while let Some((sexpr, depth)) = stack.pop() {
            match sexpr {
                SExpr::Atom(Atom::Symbol(s)) => {
                    self.symbol(s)?;
                }
                SExpr::Atom(_) => {}
                SExpr::List(items) => {
                    deepest = deepest.max(depth + 1);
                    stack.extend(items.iter().map(|i| (i, depth + 1)));
                }
            }
        }
        Ok(deepest)
    }

    /// The values of `attributes`, which stand in the list that holds them.
    fn attributes(&self, attributes: &[Attribute]) -> Result<usize> {
        let mut deepest = 0;
        for a in attributes {
            let depth = match a.value() {
                Some(AttributeValue::Symbol(s)) => self.symbol(s)?,
                Some(AttributeValue::List(items)) => list(items.iter().map(|i| self.sexpr(i)).collect::<Result<Vec<_>>>()?),
                _ => 0,
            };
            deepest = deepest.max(depth);
        }
        Ok(deepest)
    }

    fn pattern(&self, pattern: &Pattern) -> Result<usize> {
        match pattern {
            Pattern::Symbol(s) => self.symbol(s),
            Pattern::Constructor(c, vars) => {
                self.symbol(c)?;
                for v in vars.iter() {
                    self.symbol(v.as_ref().ok_or_else(|| unsupported("the wildcard pattern _"))?)?;
                }
                Ok(1)
            }
            _ => Err(unsupported("the wildcard pattern _")),
        }
    }

    /// A term, folded bottom-up: each node gets the nesting of its
    /// subterms ([`Term::children`]).
    fn term(&self, term: &Term) -> Result<usize> {
        term.try_fold(|t, children: Vec<usize>| {
            let deepest = children.iter().copied().max().unwrap_or(0);
            match t {
                Term::Constant(_) => Ok(0),
                Term::Identifier(q) => self.qual(q),
                Term::Application(q, _) => {
                    if q.sort().is_none() && q.identifier().as_simple().is_some_and(|s| s.as_str() == CHOICE) {
                        return Err(Error::new(ErrorKind::Syntax, "choice is the binder of Figure 2 and cannot be applied as a function"));
                    }
                    Ok(list([self.qual(q)?, deepest]))
                }
                Term::Let(bindings, _) => {
                    // `(let ((x t)…) body)`: the children are the bound
                    // terms, then the body.
                    for b in bindings.iter() {
                        self.symbol(b.variable())?;
                    }
                    let (bound, body) = children.split_at(children.len().saturating_sub(1));
                    Ok(list([list([list(bound.iter().copied())]), body.first().copied().unwrap_or(0)]))
                }
                Term::Forall(vars, _) | Term::Exists(vars, _) => Ok(list([self.vars(vars)?, deepest])),
                Term::Binder(name, vars, _) => {
                    if name.as_str() != CHOICE {
                        return Err(Error::new(ErrorKind::Syntax, format!("{name} is not a binder of Figure 2; the only one Alethe adds is choice")));
                    }
                    if vars.len() != 1 {
                        return Err(Error::new(ErrorKind::Syntax, format!("choice binds exactly one variable (Figure 2), found {}", vars.len())));
                    }
                    Ok(list([self.vars(vars)?, deepest]))
                }
                Term::Match(_, cases) => {
                    // `(match t ((p t)…))`: the children are the matched
                    // term, then the term of each case.
                    let cases = cases.iter().zip(children.iter().skip(1)).map(|(case, &term)| Ok(list([self.pattern(case.pattern())?, term]))).collect::<Result<Vec<_>>>()?;
                    Ok(list([children.first().copied().unwrap_or(0), list(cases)]))
                }
                Term::Annotated(_, attributes) => Ok(list([deepest, self.attributes(attributes)?])),
                Term::Lambda(..) => Err(unsupported("lambda")),
                _ => Err(Error::new(ErrorKind::Unsupported, "a kind of term that this crate does not know")),
            }
        })
    }
}

/// Rejects text that nests deeper than [`dialect`] reads.
fn within_limit(depth: usize) -> Result<()> {
    let limit = dialect().max_depth();
    if depth > limit {
        return Err(Error::new(ErrorKind::Depth, format!("the text nests {depth} parentheses deep, deeper than {limit}, the limit of the reader")));
    }
    Ok(())
}

/// Checks that `term` is a ⟨proof_term⟩: no symbol that Figure 2 excludes,
/// `choice` over exactly one variable and no other dialect binder, and
/// none of the SMT-LIB 2.7 additions (see the module documentation); and
/// that its text nests no deeper than [`dialect`] reads, so that it reads
/// back.
///
/// ```
/// let lambda: smtlib::Term = "(lambda ((x Int)) x)".parse().unwrap();
/// assert_eq!(alethe::term::validate(&lambda).unwrap_err().kind(), alethe::ErrorKind::Unsupported);
/// ```
pub fn validate(term: &Term) -> Result<()> {
    validate_term_at(term, 0, Symbols::Check)
}

/// [`validate`] for a term whose text is enclosed by `depth` parentheses.
pub(crate) fn validate_term_at(term: &Term, depth: usize, symbols: Symbols) -> Result<()> {
    within_limit(depth + Check { symbols }.term(term)?)
}

/// Checks a sort whose text is enclosed by `depth` parentheses.
pub(crate) fn validate_sort_at(sort: &Sort, depth: usize, symbols: Symbols) -> Result<()> {
    within_limit(depth + Check { symbols }.sort(sort)?)
}

/// Checks the sorted variable `(x S)` enclosed by `depth` parentheses.
pub(crate) fn validate_var_at(var: &SortedVar, depth: usize, symbols: Symbols) -> Result<()> {
    within_limit(depth + Check { symbols }.var(var)?)
}

/// Checks the values of attributes that stand in a list enclosed by
/// `depth` parentheses (the list itself included).
pub(crate) fn validate_attributes_at(attributes: &[Attribute], depth: usize, symbols: Symbols) -> Result<()> {
    within_limit(depth + Check { symbols }.attributes(attributes)?)
}

/// The bit-vector constant bvⁱₙ of §4.1 written as the specification
/// writes it, `(_ @bvn i)`: the width `n` after `@bv`, the value `i` as
/// the index.
///
/// ```
/// use smtlib::lexicon::Numeral;
/// let term = alethe::term::bv_constant(&Numeral::new("2").unwrap(), &Numeral::new("3").unwrap());
/// assert_eq!(alethe::term::to_text(&term), "(_ @bv2 3)");
/// ```
pub fn bv_constant(width: &Numeral, value: &Numeral) -> Term {
    let symbol = Symbol::new(&format!("@bv{}", width.as_str())).expect("@bv followed by a numeral is a symbol");
    Term::Identifier(QualIdentifier::plain(Identifier::indexed(symbol, NonEmpty::one(Index::Numeral(value.clone())))))
}

/// The width and the value of a constant written `(_ @bvn i)` (§4.1), or
/// `None` for any other term.
///
/// ```
/// let term = alethe::term::parse("(_ @bv2 3)").unwrap();
/// let (width, value) = alethe::term::as_bv_constant(&term).unwrap();
/// assert_eq!((width.as_str(), value.as_str()), ("2", "3"));
/// ```
pub fn as_bv_constant(term: &Term) -> Option<(Numeral, Numeral)> {
    let Term::Identifier(q) = term else { return None };
    if q.sort().is_some() {
        return None;
    }
    let width = Numeral::new(q.identifier().symbol().as_str().strip_prefix("@bv")?).ok()?;
    match q.identifier().indices() {
        [Index::Numeral(value)] => Some((width, value.clone())),
        _ => None,
    }
}
