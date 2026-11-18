//! Objects: the OpenMath-style abstract syntax of MMT terms
//! (doc/language/objects.md, `api/objects/Obj.scala`), independent of any
//! notation.
//!
//! A term is a symbol reference (OMS), a module reference (OMMOD), a
//! variable (OMV), an application (OMA), a binding (OMBINDC: a binder, a
//! context of variable declarations and one or more scopes) or a literal
//! (OMLIT: a value of a semantic type together with its syntactic type).
//! MMT's attributions (OMATTR), labels (OML), semi-formal objects and
//! complex terms with substitutions are outside the subset and are never
//! produced; notations that would produce them are rejected by the reader.
//!
//! The reader represents what the text leaves open as variables whose name
//! starts with an empty step (`/I/0` for an omitted implicit argument,
//! `/_/0` for an explicit `_`, `/x/0` for an omitted variable type), applied
//! with a plain OMA to the bound variables in whose scope they occur, as
//! `Solver.makeUnknown` does. Solving them is type checking, which is not
//! part of this crate.
//!
//! Terms are trees. [`Term::depth`], [`Term::visit`], `Display` and `Drop`
//! work with explicit stacks and accept terms of any depth. The derived
//! `Clone`, `PartialEq`, `Hash` and `Debug` recurse; the reader never builds
//! a term deeper than [`crate::Limits::depth`], and the library refuses to
//! add or print deeper ones, so within this crate they run on bounded terms.

use std::fmt;

use crate::notation::Notation;
use crate::uri::{GlobalName, LocalName, MPath};

/// A term.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Term {
    /// OMS: a reference to a constant.
    Sym(GlobalName),
    /// OMMOD: a reference to a module.
    Module(MPath),
    /// OMV: a variable.
    Var(LocalName),
    /// OMA: an application of a function to arguments.
    App(Box<Term>, Vec<Term>),
    /// OMBINDC: a binder, the bound variables and the scopes.
    Bind(Box<Term>, Context, Vec<Term>),
    /// OMLIT: a literal.
    Lit(Literal),
}

/// A variable declaration in a context.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VarDecl {
    /// The name.
    pub name: LocalName,
    /// The type, if given.
    pub tp: Option<Term>,
    /// The definiens, if given.
    pub df: Option<Term>,
}

impl VarDecl {
    /// A declaration with a type.
    pub fn typed(name: LocalName, tp: Term) -> VarDecl {
        VarDecl { name, tp: Some(tp), df: None }
    }

    /// A declaration without type and definiens.
    pub fn untyped(name: LocalName) -> VarDecl {
        VarDecl { name, tp: None, df: None }
    }
}

/// A context: variable declarations in order.
pub type Context = Vec<VarDecl>;

/// A literal: a value and the syntactic type that a realization rule assigns to it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Literal {
    /// The value.
    pub value: LitValue,
    /// The syntactic type (normally a constant realized by a semantic type).
    pub tp: Box<Term>,
}

impl Literal {
    /// A literal of a value with a syntactic type.
    pub fn new(value: LitValue, tp: Term) -> Literal {
        Literal { value, tp: Box::new(tp) }
    }
}

/// The values of the semantic types this crate reads (`api/uom/StandardLiterals.scala`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LitValue {
    /// A string (StandardString), as written between the quotes.
    String(String),
    /// An integer (StandardInt, StandardNat, StandardPositive).
    Int(Integer),
    /// A boolean (StandardBool).
    Bool(bool),
    /// A notation (NotationRealizedType), kept as its normalized text.
    Notation(String),
}

/// An integer of any size, kept as a normalized decimal numeral (no leading
/// zeros, `-` only for negative numbers). This crate only reads and writes
/// integers; it does no arithmetic, so there is no bound on their size.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Integer(String);

impl Integer {
    /// Parses an optionally signed decimal numeral of ASCII digits.
    pub fn parse(s: &str) -> Option<Integer> {
        let (neg, digits) = match s.strip_prefix('-') {
            Some(d) => (true, d),
            None => (false, s.strip_prefix('+').unwrap_or(s)),
        };
        if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        let t = digits.trim_start_matches('0');
        let t = if t.is_empty() { "0" } else { t };
        Some(Integer(if neg && t != "0" { format!("-{t}") } else { t.to_string() }))
    }

    /// The machine integer, if it fits.
    pub fn to_i128(&self) -> Option<i128> {
        self.0.parse().ok()
    }

    /// Whether the integer is negative.
    pub fn is_negative(&self) -> bool {
        self.0.starts_with('-')
    }

    /// Whether the integer is zero.
    pub fn is_zero(&self) -> bool {
        self.0 == "0"
    }

    /// The numeral.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<i128> for Integer {
    fn from(i: i128) -> Integer {
        Integer(i.to_string())
    }
}

impl From<u64> for Integer {
    fn from(i: u64) -> Integer {
        Integer(i.to_string())
    }
}

impl std::str::FromStr for Integer {
    type Err = crate::error::Error;

    fn from_str(s: &str) -> crate::error::Result<Integer> {
        Integer::parse(s).ok_or_else(|| crate::error::Error::new(crate::error::ErrorKind::Object, format!("not a decimal numeral: {s}")))
    }
}

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl LitValue {
    /// The value as MMT writes it inside a literal.
    pub fn text(&self) -> String {
        match self {
            LitValue::String(s) => s.clone(),
            LitValue::Int(i) => i.to_string(),
            LitValue::Bool(b) => b.to_string(),
            LitValue::Notation(n) => n.clone(),
        }
    }

    /// The value of a notation literal.
    pub fn notation(n: &Notation) -> LitValue {
        LitValue::Notation(n.to_string())
    }
}

impl Term {
    /// A symbol reference.
    pub fn sym(p: &GlobalName) -> Term {
        Term::Sym(p.clone())
    }

    /// A variable of a simple name.
    pub fn var(n: &str) -> Term {
        Term::Var(LocalName::simple(n))
    }

    /// An application.
    pub fn app(f: Term, args: Vec<Term>) -> Term {
        Term::App(Box::new(f), args)
    }

    /// A binding with one scope.
    pub fn bind(binder: Term, ctx: Context, scope: Term) -> Term {
        Term::Bind(Box::new(binder), ctx, vec![scope])
    }

    /// A literal.
    pub fn lit(value: LitValue, tp: Term) -> Term {
        Term::Lit(Literal::new(value, tp))
    }

    /// The head symbol: the symbol of an OMS, or of the function of an OMA, or of the binder of an OMBINDC.
    pub fn head(&self) -> Option<&GlobalName> {
        let mut t = self;
        loop {
            match t {
                Term::Sym(p) => return Some(p),
                Term::App(f, _) | Term::Bind(f, _, _) => t = f,
                _ => return None,
            }
        }
    }

    /// The direct subterms in order: function and arguments; binder, the
    /// types and definientia of the variables, and the scopes; the type of a literal.
    pub fn children(&self) -> Vec<&Term> {
        let mut out = Vec::new();
        match self {
            Term::App(f, args) => {
                out.push(&**f);
                out.extend(args.iter());
            }
            Term::Bind(b, ctx, scopes) => {
                out.push(&**b);
                for vd in ctx {
                    out.extend(vd.tp.iter());
                    out.extend(vd.df.iter());
                }
                out.extend(scopes.iter());
            }
            Term::Lit(l) => out.push(&*l.tp),
            Term::Sym(_) | Term::Module(_) | Term::Var(_) => {}
        }
        out
    }

    /// The depth: 1 for a term without subterms, and one more than the
    /// deepest subterm otherwise.
    pub fn depth(&self) -> usize {
        let mut max = 0;
        let mut stack = vec![(self, 1usize)];
        while let Some((t, d)) = stack.pop() {
            max = max.max(d);
            stack.extend(t.children().into_iter().map(|c| (c, d + 1)));
        }
        max
    }

    /// Visits every subterm top-down, left to right.
    pub fn visit(&self, f: &mut dyn FnMut(&Term)) {
        let mut stack = vec![self];
        while let Some(t) = stack.pop() {
            f(t);
            stack.extend(t.children().into_iter().rev());
        }
    }
}

impl Drop for Term {
    /// Drops the subterms with an explicit stack, so that dropping a deep term does not overflow the stack.
    fn drop(&mut self) {
        fn take(t: &mut Term, stack: &mut Vec<Term>) {
            match t {
                Term::App(f, args) => {
                    stack.push(std::mem::replace(&mut **f, Term::Var(LocalName::default())));
                    stack.append(args);
                }
                Term::Bind(b, ctx, scopes) => {
                    stack.push(std::mem::replace(&mut **b, Term::Var(LocalName::default())));
                    for vd in ctx.iter_mut() {
                        stack.extend(vd.tp.take());
                        stack.extend(vd.df.take());
                    }
                    stack.append(scopes);
                }
                Term::Lit(l) => stack.push(std::mem::replace(&mut *l.tp, Term::Var(LocalName::default()))),
                Term::Sym(_) | Term::Module(_) | Term::Var(_) => {}
            }
        }
        let mut stack = Vec::new();
        take(self, &mut stack);
        while let Some(mut t) = stack.pop() {
            take(&mut t, &mut stack);
        }
    }
}

impl fmt::Display for Term {
    /// A notation-independent rendering in the style of MMT's `toString`, for messages.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Item<'a> {
            Term(&'a Term),
            Text(&'static str),
            Name(&'a LocalName),
        }
        let mut stack = vec![Item::Term(self)];
        while let Some(item) = stack.pop() {
            match item {
                Item::Text(s) => f.write_str(s)?,
                Item::Name(n) => write!(f, "{n}")?,
                Item::Term(t) => match t {
                    Term::Sym(p) => write!(f, "{}", p.name())?,
                    Term::Module(m) => write!(f, "{m}")?,
                    Term::Var(n) => write!(f, "{n}")?,
                    Term::Lit(l) => match &l.value {
                        LitValue::String(s) => write!(f, "{s:?}")?,
                        v => write!(f, "{}", v.text())?,
                    },
                    Term::App(h, args) => {
                        f.write_str("(")?;
                        let mut items = vec![Item::Term(h)];
                        for a in args {
                            items.push(Item::Text(" "));
                            items.push(Item::Term(a));
                        }
                        items.push(Item::Text(")"));
                        stack.extend(items.into_iter().rev());
                    }
                    Term::Bind(b, ctx, scopes) => {
                        f.write_str("(")?;
                        let mut items = vec![Item::Term(b), Item::Text(" [")];
                        for (i, vd) in ctx.iter().enumerate() {
                            if i > 0 {
                                items.push(Item::Text(", "));
                            }
                            items.push(Item::Name(&vd.name));
                            if let Some(t) = &vd.tp {
                                items.push(Item::Text(" : "));
                                items.push(Item::Term(t));
                            }
                            if let Some(t) = &vd.df {
                                items.push(Item::Text(" = "));
                                items.push(Item::Term(t));
                            }
                        }
                        items.push(Item::Text("]"));
                        for s in scopes {
                            items.push(Item::Text(" "));
                            items.push(Item::Term(s));
                        }
                        items.push(Item::Text(")"));
                        stack.extend(items.into_iter().rev());
                    }
                },
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn deep(n: usize) -> Term {
        let f = Term::sym(&GlobalName::parse_plain("http://a.org?T?f").unwrap());
        let mut t = Term::var("x");
        for _ in 0..n {
            t = Term::app(f.clone(), vec![t]);
        }
        t
    }

    #[test]
    fn integers_are_normalized() {
        assert_eq!(Integer::parse("007").unwrap().as_str(), "7");
        assert_eq!(Integer::parse("-0").unwrap().as_str(), "0");
        assert!(Integer::parse("1a").is_none());
        assert!(Integer::parse("٣").is_none());
    }

    #[test]
    fn deep_terms_are_measured_shown_visited_and_dropped_without_recursion() {
        // run on a thread with a small stack: a recursive drop of this term would overflow it
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let t = deep(200_000);
                assert_eq!(t.depth(), 200_001);
                let mut n = 0;
                t.visit(&mut |_| n += 1);
                assert_eq!(n, 400_001);
                assert!(t.to_string().starts_with("(f (f "));
                drop(t);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn display_of_a_binding() {
        let b = Term::sym(&GlobalName::parse_plain("http://a.org?T?lam").unwrap());
        let t = Term::bind(b, vec![VarDecl::typed(LocalName::simple("x"), Term::var("A")), VarDecl::untyped(LocalName::simple("y"))], Term::var("x"));
        assert_eq!(t.to_string(), "(lam [x : A, y] x)");
    }
}
