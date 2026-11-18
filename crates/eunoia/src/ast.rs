//! The abstract syntax of Eunoia, following the grammar "Full syntax for
//! Eunoia commands" of the Ethos user manual.
//!
//! Every value of these types is denoted by some text: where the grammar
//! constrains a construct beyond its shape (a symbol cannot contain `|`, an
//! application needs an argument, a variable list only follows a binder's
//! head), the type keeps its fields private and its constructor refuses the
//! values that no text denotes. That is what makes the printer total: every
//! value prints to a text that the parser reads back to an equal value.
//!
//! The grammar is read as Ethos reads it, which is wider than the manual's BNF
//! in four places, all taken from Ethos `src/expr_parser.cpp`:
//!
//! - the head of an application can itself be an application of `_` or `as`
//!   (`((_ f a) b)`, "we allow the syntax ((_ to begin a term");
//! - the first argument of an application can be a variable list
//!   `((x T) ...)`, which is the binder syntax of the manual section "Binder";
//! - `let` and `eo::define` take a list of bindings and a body (manual
//!   "Declaring theory signatures" and "Example: Term evaluator");
//! - where the grammar has `<x>+` (the attributes of `(! ...)`, the
//!   constructors of a datatype, the argument types of a program), the
//!   abstract syntax holds a [`NonEmpty`], so that every value prints to text
//!   in the grammar.
//!
//! # Depth
//!
//! Terms nest without limit, as in Ethos, which parses with an explicit stack
//! (`ExprParser::parseExpr`). Every operation on a [`Term`] here (printing,
//! comparing, hashing, cloning, dropping) works with an explicit stack too, so
//! a term of any depth that fits in memory is handled without exhausting the
//! call stack.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::{Deref, DerefMut};

use crate::error::{AstError, AstErrorKind, Position};
use crate::lexer::{is_simple_symbol, is_symbol_char, is_symbol_start, RESERVED_WORDS};

/// A sequence of at least one element: the grammar's `<x>+`.
///
/// ```
/// use eunoia::NonEmpty;
/// let mut types = NonEmpty::new(eunoia::Term::symbol("Int")?);
/// types.push(eunoia::Term::symbol("Bool")?);
/// assert_eq!(types.len(), 2);
/// assert!(NonEmpty::<eunoia::Term>::from_vec(Vec::new()).is_err());
/// # Ok::<(), eunoia::AstError>(())
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NonEmpty<T>(Vec<T>);

impl<T> NonEmpty<T> {
    /// The sequence of one element.
    pub fn new(first: T) -> NonEmpty<T> {
        NonEmpty(vec![first])
    }

    /// The sequence of `items`. Refused: no item.
    pub fn from_vec(items: Vec<T>) -> Result<NonEmpty<T>, AstError> {
        if items.is_empty() {
            return Err(AstError::new(AstErrorKind::Empty));
        }
        Ok(NonEmpty(items))
    }

    /// The first element.
    pub fn first(&self) -> &T {
        &self.0[0]
    }

    /// Appends an element.
    pub fn push(&mut self, item: T) {
        self.0.push(item);
    }

    /// The elements.
    pub fn as_slice(&self) -> &[T] {
        &self.0
    }

    /// The elements, as a vector.
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }
}

impl<T> Deref for NonEmpty<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.0
    }
}

impl<T> DerefMut for NonEmpty<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.0
    }
}

impl<T> TryFrom<Vec<T>> for NonEmpty<T> {
    type Error = AstError;
    fn try_from(items: Vec<T>) -> Result<NonEmpty<T>, AstError> {
        NonEmpty::from_vec(items)
    }
}

impl<T> From<NonEmpty<T>> for Vec<T> {
    fn from(items: NonEmpty<T>) -> Vec<T> {
        items.0
    }
}

impl<'a, T> IntoIterator for &'a NonEmpty<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<T> IntoIterator for NonEmpty<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// A symbol: the name of a constant, parameter, program, rule or proof.
///
/// A quoted symbol `|x|` and the simple symbol `x` are the same symbol, so the
/// value holds only the name and the printer quotes it when it must.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(String);

impl Symbol {
    /// A symbol with the given name. Refused: a name that contains `|` (no
    /// quoted symbol can hold it) and the reserved words `!`, `let`, `par` and
    /// `eo::define` (Ethos never reads them as symbols).
    pub fn new(name: impl Into<String>) -> Result<Symbol, AstError> {
        let name = name.into();
        if name.contains('|') {
            return Err(AstError::new(AstErrorKind::SymbolWithBar));
        }
        if let Some(word) = RESERVED_WORDS.iter().find(|w| **w == name) {
            return Err(AstError::new(AstErrorKind::ReservedWord(word)));
        }
        Ok(Symbol(name))
    }

    pub(crate) fn unchecked(name: String) -> Symbol {
        Symbol(name)
    }

    /// The name of the symbol.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if is_simple_symbol(&self.0) {
            f.write_str(&self.0)
        } else {
            write!(f, "|{}|", self.0)
        }
    }
}

/// A keyword, held without its leading colon.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Keyword(String);

impl Keyword {
    /// A keyword `:name`. Refused: a name that is not a symbol start
    /// character followed by symbol characters.
    pub fn new(name: impl Into<String>) -> Result<Keyword, AstError> {
        let name = name.into();
        let mut chars = name.chars();
        let ok = matches!(chars.next(), Some(c) if is_symbol_start(c)) && chars.all(is_symbol_char);
        if !ok {
            return Err(AstError::new(AstErrorKind::NotAKeyword));
        }
        Ok(Keyword(name))
    }

    pub(crate) fn unchecked(name: String) -> Keyword {
        Keyword(name)
    }

    /// The name, without the colon.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ":{}", self.0)
    }
}

/// The syntactic categories of literals (manual section "Literal types").
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum LiteralCategory {
    /// `<numeral>`: `-?<digit>+`.
    Numeral,
    /// `<decimal>`: `-?<digit>+.<digit>+`.
    Decimal,
    /// `<rational>`: `-?<digit>+/<digit>+`.
    Rational,
    /// `<binary>`: `#b<0|1>+`.
    Binary,
    /// `<hexadecimal>`: `#x<hex-digit>+`.
    Hexadecimal,
    /// `<string>`: `"<char>*"`.
    String,
    /// `<boolean>`: `true` and `false`. It is builtin: no literal has it as
    /// its category in the syntax (`true` is a symbol), and `declare-consts`
    /// cannot give it a type rule.
    Boolean,
}

impl LiteralCategory {
    /// Every category.
    pub const ALL: [LiteralCategory; 7] = [LiteralCategory::Numeral, LiteralCategory::Decimal, LiteralCategory::Rational, LiteralCategory::Binary, LiteralCategory::Hexadecimal, LiteralCategory::String, LiteralCategory::Boolean];

    /// The name as written in `declare-consts`, e.g. `<numeral>`.
    pub fn name(self) -> &'static str {
        match self {
            LiteralCategory::Numeral => "<numeral>",
            LiteralCategory::Decimal => "<decimal>",
            LiteralCategory::Rational => "<rational>",
            LiteralCategory::Binary => "<binary>",
            LiteralCategory::Hexadecimal => "<hexadecimal>",
            LiteralCategory::String => "<string>",
            LiteralCategory::Boolean => "<boolean>",
        }
    }

    /// The category named by `<numeral>`, `<string>`, ...
    pub fn from_name(name: &str) -> Option<LiteralCategory> {
        LiteralCategory::ALL.into_iter().find(|c| c.name() == name)
    }
}

impl fmt::Display for LiteralCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// A literal of one of the categories of the manual section "Literal types".
///
/// The text is kept as written (for binary and hexadecimal literals, the
/// digits after `#b`/`#x`; for strings, the content with `""` read as `"`).
/// Two literals that Ethos normalises to one value (`1/2` and `2/4`) are
/// different values here: this is syntax, not semantics.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Literal {
    category: LiteralCategory,
    text: String,
}

fn all_digits(s: &str) -> bool {
    !s.is_empty() && s.chars().all(|c| c.is_ascii_digit())
}

impl Literal {
    /// A literal of the given category with the given text. Refused: a text
    /// that is not of the category's form; a rational with a zero denominator
    /// ("Expected non-zero denominator", Ethos `ExprParser::parseExpr`); a
    /// string with a character outside ASCII, which Ethos requires to be
    /// written as an escape sequence; the category `<boolean>`.
    pub fn new(category: LiteralCategory, text: impl Into<String>) -> Result<Literal, AstError> {
        let text = text.into();
        let unsigned = text.strip_prefix('-').unwrap_or(&text);
        let ok = match category {
            LiteralCategory::Numeral => all_digits(unsigned),
            LiteralCategory::Decimal => matches!(unsigned.split_once('.'), Some((a, b)) if all_digits(a) && all_digits(b)),
            LiteralCategory::Rational => match unsigned.split_once('/') {
                Some((a, b)) if all_digits(a) && all_digits(b) => {
                    if b.chars().all(|c| c == '0') {
                        return Err(AstError::new(AstErrorKind::ZeroDenominator));
                    }
                    true
                }
                _ => false,
            },
            LiteralCategory::Binary => !text.is_empty() && text.chars().all(|c| c == '0' || c == '1'),
            LiteralCategory::Hexadecimal => !text.is_empty() && text.chars().all(|c| c.is_ascii_hexdigit()),
            LiteralCategory::String => {
                if !text.is_ascii() {
                    return Err(AstError::new(AstErrorKind::NonAsciiString));
                }
                true
            }
            LiteralCategory::Boolean => return Err(AstError::new(AstErrorKind::BooleanLiteral)),
        };
        if !ok {
            return Err(AstError::new(AstErrorKind::NotALiteral(category)));
        }
        Ok(Literal { category, text })
    }

    /// A numeral literal.
    pub fn numeral(n: i128) -> Literal {
        Literal { category: LiteralCategory::Numeral, text: n.to_string() }
    }

    /// A string literal with the given content.
    pub fn string(content: impl Into<String>) -> Result<Literal, AstError> {
        Literal::new(LiteralCategory::String, content)
    }

    /// The category of the literal.
    pub fn category(&self) -> LiteralCategory {
        self.category
    }

    /// The text of the literal (see the type documentation).
    pub fn text(&self) -> &str {
        &self.text
    }
}

fn write_string(f: &mut fmt::Formatter<'_>, content: &str) -> fmt::Result {
    write!(f, "\"{}\"", content.replace('"', "\"\""))
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.category {
            LiteralCategory::Binary => write!(f, "#b{}", self.text),
            LiteralCategory::Hexadecimal => write!(f, "#x{}", self.text),
            LiteralCategory::String => write_string(f, &self.text),
            _ => f.write_str(&self.text),
        }
    }
}

/// A string literal in a command (`include`, `reference`, `echo`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StrLit(String);

impl StrLit {
    /// A string with the given content; refused if it is not ASCII.
    pub fn new(content: impl Into<String>) -> Result<StrLit, AstError> {
        let content = content.into();
        if !content.is_ascii() {
            return Err(AstError::new(AstErrorKind::NonAsciiString));
        }
        Ok(StrLit(content))
    }

    /// The content.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for StrLit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_string(f, &self.0)
    }
}

/// An attribute `<keyword> <term>?`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Attribute {
    /// The keyword.
    pub keyword: Keyword,
    /// The value, if any.
    pub value: Option<Term>,
}

impl Attribute {
    /// An attribute without a value, e.g. `:implicit`.
    pub fn flag(name: &str) -> Result<Attribute, AstError> {
        Ok(Attribute { keyword: Keyword::new(name)?, value: None })
    }

    /// An attribute with a value, e.g. `:right-assoc-nil false`.
    pub fn with_value(name: &str, value: Term) -> Result<Attribute, AstError> {
        Ok(Attribute { keyword: Keyword::new(name)?, value: Some(value) })
    }
}

impl fmt::Display for Attribute {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.keyword)?;
        if let Some(v) = &self.value {
            write!(f, " {v}")?;
        }
        Ok(())
    }
}

/// Which binder a [`LetTerm`] uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LetForm {
    /// `let`, the SMT-LIB binder (a macro in Ethos).
    Let,
    /// `eo::define`, the Eunoia binder for common subterms.
    EoDefine,
}

/// `(let ((x t) ...) body)` or `(eo::define ((x t) ...) body)`: the bound
/// symbols stand for their terms in the body.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LetTerm {
    form: LetForm,
    bindings: Vec<(Symbol, Term)>,
    body: Box<Term>,
}

impl LetTerm {
    /// `(let ((x t) ...) body)` or `(eo::define ...)`.
    pub fn new(form: LetForm, bindings: Vec<(Symbol, Term)>, body: Term) -> LetTerm {
        LetTerm { form, bindings, body: Box::new(body) }
    }

    /// The binder.
    pub fn form(&self) -> LetForm {
        self.form
    }

    /// The bindings, all read in the scope outside the term.
    pub fn bindings(&self) -> &[(Symbol, Term)] {
        &self.bindings
    }

    /// The body.
    pub fn body(&self) -> &Term {
        &self.body
    }
}

/// `(! t attr...)`: a term annotation. Ethos ignores the attributes.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Annotation {
    term: Box<Term>,
    attributes: Vec<Attribute>,
}

impl Annotation {
    /// `(! term attributes...)` (the manual's `(! <term> <attr>+)`).
    pub fn new(term: Term, attributes: NonEmpty<Attribute>) -> Annotation {
        Annotation { term: Box::new(term), attributes: attributes.into_vec() }
    }

    /// The annotated term.
    pub fn term(&self) -> &Term {
        &self.term
    }

    /// The attributes.
    pub fn attributes(&self) -> &[Attribute] {
        &self.attributes
    }
}

/// An application `(head args...)`, possibly with a variable list as first
/// argument (binder syntax, manual section "Binder").
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Application {
    head: Box<Term>,
    vars: Option<Vec<(Symbol, Term)>>,
    args: Vec<Term>,
}

fn is_qualifier(t: &Term) -> bool {
    matches!(t, Term::Symbol(s) if s.as_str() == "_" || s.as_str() == "as")
}

impl Application {
    /// `(head args...)`. Refused: no arguments (the manual's `(<symbol>
    /// <term>+)`), or a head that is neither a symbol nor an application of
    /// `_` or `as` without a variable list.
    pub fn new(head: Term, args: Vec<Term>) -> Result<Application, AstError> {
        match &head {
            Term::Symbol(_) => {}
            Term::Apply(a) if is_qualifier(a.head()) && a.vars.is_none() => {}
            _ => return Err(AstError::new(AstErrorKind::ApplicationHead)),
        }
        if args.is_empty() {
            return Err(AstError::new(AstErrorKind::NoArguments));
        }
        Ok(Application { head: Box::new(head), vars: None, args })
    }

    /// `(head ((x1 T1) ... (xn Tn)) args...)`, the binder syntax. Refused: an
    /// empty variable list (Ethos: "Expected non-empty sorted variable list"),
    /// and a first variable named `_` or `as`, since `((_ ...` begins a
    /// qualified head instead.
    pub fn binder(head: Symbol, vars: Vec<(Symbol, Term)>, args: Vec<Term>) -> Result<Application, AstError> {
        match vars.first() {
            None => return Err(AstError::new(AstErrorKind::EmptyVariableList)),
            Some((x, _)) if x.as_str() == "_" || x.as_str() == "as" => return Err(AstError::new(AstErrorKind::QualifierVariable)),
            Some(_) => {}
        }
        Ok(Application { head: Box::new(Term::Symbol(head)), vars: Some(vars), args })
    }

    /// The head.
    pub fn head(&self) -> &Term {
        &self.head
    }

    /// The variable list, when the binder syntax is used.
    pub fn vars(&self) -> Option<&[(Symbol, Term)]> {
        self.vars.as_deref()
    }

    /// The arguments after the variable list.
    pub fn args(&self) -> &[Term] {
        &self.args
    }

    /// The head symbol, when the head is a symbol.
    pub fn head_symbol(&self) -> Option<&Symbol> {
        match &*self.head {
            Term::Symbol(s) => Some(s),
            _ => None,
        }
    }
}

/// A term (manual: `<term> ::= <symbol> | <literal> | (<symbol> <term>+) | (! <term> <attr>+)`,
/// widened as described in the module documentation).
///
/// `Clone`, `PartialEq`, `Hash`, `Debug`, `Display` and dropping work with an
/// explicit stack, for terms of any depth.
#[non_exhaustive]
pub enum Term {
    /// A symbol.
    Symbol(Symbol),
    /// A literal.
    Literal(Literal),
    /// An application.
    Apply(Application),
    /// `let` or `eo::define`.
    Let(LetTerm),
    /// `(! t attr...)`.
    Annotated(Annotation),
}

impl Term {
    /// The symbol term with the given name.
    pub fn symbol(name: &str) -> Result<Term, AstError> {
        Ok(Term::Symbol(Symbol::new(name)?))
    }

    /// `(head args...)` with a symbol head.
    pub fn app(head: &str, args: Vec<Term>) -> Result<Term, AstError> {
        Ok(Term::Apply(Application::new(Term::symbol(head)?, args)?))
    }

    /// The symbol, if this term is one.
    pub fn as_symbol(&self) -> Option<&Symbol> {
        match self {
            Term::Symbol(s) => Some(s),
            _ => None,
        }
    }

    /// The application, if this term is one.
    pub fn as_application(&self) -> Option<&Application> {
        match self {
            Term::Apply(a) => Some(a),
            _ => None,
        }
    }

    fn placeholder() -> Term {
        Term::Symbol(Symbol(String::new()))
    }

    /// The direct subterms, in the order in which they are written: the head,
    /// the types of a variable list, the arguments; the values of a `let` and
    /// its body; the annotated term and the attribute values.
    pub fn children(&self) -> Vec<&Term> {
        let mut out = Vec::new();
        push_children(self, &mut out);
        out
    }

    /// Every subterm, this term first, each before its subterms, in the order
    /// in which they are written.
    pub fn preorder(&self) -> Vec<&Term> {
        let mut out = Vec::new();
        let mut stack = vec![self];
        let mut kids = Vec::new();
        while let Some(t) = stack.pop() {
            out.push(t);
            kids.clear();
            push_children(t, &mut kids);
            stack.extend(kids.drain(..).rev());
        }
        out
    }

    /// The depth of the term: 1 for a symbol or literal.
    pub fn depth(&self) -> usize {
        let mut max = 0;
        let mut stack = vec![(self, 1usize)];
        let mut kids = Vec::new();
        while let Some((t, d)) = stack.pop() {
            max = max.max(d);
            kids.clear();
            push_children(t, &mut kids);
            stack.extend(kids.drain(..).map(|k| (k, d + 1)));
        }
        max
    }
}

pub(crate) fn push_children<'a>(t: &'a Term, out: &mut Vec<&'a Term>) {
    match t {
        Term::Symbol(_) | Term::Literal(_) => {}
        Term::Apply(a) => {
            out.push(&a.head);
            if let Some(vars) = &a.vars {
                out.extend(vars.iter().map(|(_, ty)| ty));
            }
            out.extend(a.args.iter());
        }
        Term::Let(l) => {
            out.extend(l.bindings.iter().map(|(_, v)| v));
            out.push(&l.body);
        }
        Term::Annotated(a) => {
            out.push(&a.term);
            out.extend(a.attributes.iter().filter_map(|x| x.value.as_ref()));
        }
    }
}

/// Whether two terms agree in everything but their children.
pub(crate) fn shallow_eq(a: &Term, b: &Term) -> bool {
    match (a, b) {
        (Term::Symbol(x), Term::Symbol(y)) => x == y,
        (Term::Literal(x), Term::Literal(y)) => x == y,
        (Term::Apply(x), Term::Apply(y)) => {
            let vars_eq = match (&x.vars, &y.vars) {
                (None, None) => true,
                (Some(v), Some(w)) => v.len() == w.len() && v.iter().zip(w).all(|((p, _), (q, _))| p == q),
                _ => false,
            };
            vars_eq && x.args.len() == y.args.len()
        }
        (Term::Let(x), Term::Let(y)) => x.form == y.form && x.bindings.len() == y.bindings.len() && x.bindings.iter().zip(&y.bindings).all(|((p, _), (q, _))| p == q),
        (Term::Annotated(x), Term::Annotated(y)) => x.attributes.len() == y.attributes.len() && x.attributes.iter().zip(&y.attributes).all(|(p, q)| p.keyword == q.keyword && p.value.is_some() == q.value.is_some()),
        _ => false,
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Term) -> bool {
        let mut stack = vec![(self, other)];
        let (mut ka, mut kb) = (Vec::new(), Vec::new());
        while let Some((a, b)) = stack.pop() {
            if !shallow_eq(a, b) {
                return false;
            }
            ka.clear();
            kb.clear();
            push_children(a, &mut ka);
            push_children(b, &mut kb);
            if ka.len() != kb.len() {
                return false;
            }
            stack.extend(ka.drain(..).zip(kb.drain(..)));
        }
        true
    }
}

impl Eq for Term {}

impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut stack = vec![self];
        let mut kids = Vec::new();
        while let Some(t) = stack.pop() {
            match t {
                Term::Symbol(s) => (0u8, s).hash(state),
                Term::Literal(l) => (1u8, l).hash(state),
                Term::Apply(a) => {
                    2u8.hash(state);
                    a.vars.as_ref().map(|v| v.iter().map(|(x, _)| x).collect::<Vec<_>>()).hash(state);
                    a.args.len().hash(state);
                }
                Term::Let(l) => {
                    3u8.hash(state);
                    l.form.hash(state);
                    for (x, _) in &l.bindings {
                        x.hash(state);
                    }
                    l.bindings.len().hash(state);
                }
                Term::Annotated(a) => {
                    4u8.hash(state);
                    for x in &a.attributes {
                        (&x.keyword, x.value.is_some()).hash(state);
                    }
                    a.attributes.len().hash(state);
                }
            }
            kids.clear();
            push_children(t, &mut kids);
            stack.extend(kids.drain(..).rev());
        }
    }
}

/// Rebuilds a node like `t` with the given children, in the order of [`push_children`].
fn rebuild(t: &Term, kids: Vec<Term>) -> Term {
    let mut kids = kids.into_iter();
    let mut next = || kids.next().unwrap_or_else(Term::placeholder);
    match t {
        Term::Symbol(s) => Term::Symbol(s.clone()),
        Term::Literal(l) => Term::Literal(l.clone()),
        Term::Apply(a) => {
            let head = Box::new(next());
            let vars = a.vars.as_ref().map(|v| v.iter().map(|(x, _)| (x.clone(), next())).collect());
            let args = a.args.iter().map(|_| next()).collect();
            Term::Apply(Application { head, vars, args })
        }
        Term::Let(l) => {
            let bindings = l.bindings.iter().map(|(x, _)| (x.clone(), next())).collect();
            Term::Let(LetTerm { form: l.form, bindings, body: Box::new(next()) })
        }
        Term::Annotated(a) => {
            let term = Box::new(next());
            let attributes = a.attributes.iter().map(|x| Attribute { keyword: x.keyword.clone(), value: x.value.as_ref().map(|_| next()) }).collect();
            Term::Annotated(Annotation { term, attributes })
        }
    }
}

impl Clone for Term {
    fn clone(&self) -> Term {
        enum Job<'a> {
            Visit(&'a Term),
            Build(&'a Term, usize),
        }
        let mut jobs = vec![Job::Visit(self)];
        let mut values: Vec<Term> = Vec::new();
        let mut kids = Vec::new();
        while let Some(job) = jobs.pop() {
            match job {
                Job::Visit(t) => {
                    kids.clear();
                    push_children(t, &mut kids);
                    if kids.is_empty() {
                        values.push(rebuild(t, Vec::new()));
                    } else {
                        jobs.push(Job::Build(t, kids.len()));
                        jobs.extend(kids.drain(..).rev().map(Job::Visit));
                    }
                }
                Job::Build(t, n) => {
                    let built = values.split_off(values.len().saturating_sub(n));
                    values.push(rebuild(t, built));
                }
            }
        }
        values.pop().unwrap_or_else(Term::placeholder)
    }
}

/// Moves the children of `t` out into `out`, leaving placeholders.
fn take_children(t: &mut Term, out: &mut Vec<Term>) {
    match t {
        Term::Symbol(_) | Term::Literal(_) => {}
        Term::Apply(a) => take_application(a, out),
        Term::Let(l) => take_let(l, out),
        Term::Annotated(a) => take_annotation(a, out),
    }
}

fn take_application(a: &mut Application, out: &mut Vec<Term>) {
    if !matches!(&*a.head, Term::Symbol(_) | Term::Literal(_)) {
        out.push(mem::replace(&mut *a.head, Term::placeholder()));
    }
    if let Some(vars) = a.vars.as_mut() {
        out.extend(vars.drain(..).map(|(_, t)| t));
    }
    out.append(&mut a.args);
}

fn take_let(l: &mut LetTerm, out: &mut Vec<Term>) {
    out.extend(l.bindings.drain(..).map(|(_, t)| t));
    if !matches!(&*l.body, Term::Symbol(_) | Term::Literal(_)) {
        out.push(mem::replace(&mut *l.body, Term::placeholder()));
    }
}

fn take_annotation(a: &mut Annotation, out: &mut Vec<Term>) {
    if !matches!(&*a.term, Term::Symbol(_) | Term::Literal(_)) {
        out.push(mem::replace(&mut *a.term, Term::placeholder()));
    }
    out.extend(a.attributes.iter_mut().filter_map(|x| x.value.take()));
}

fn drop_all(mut stack: Vec<Term>) {
    while let Some(mut t) = stack.pop() {
        take_children(&mut t, &mut stack);
    }
}

impl Drop for Application {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_application(self, &mut stack);
        drop_all(stack);
    }
}

impl Drop for LetTerm {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_let(self, &mut stack);
        drop_all(stack);
    }
}

impl Drop for Annotation {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_annotation(self, &mut stack);
        drop_all(stack);
    }
}

/// A piece of printed output.
enum Out<'a> {
    Term(&'a Term),
    Text(&'static str),
    Symbol(&'a Symbol),
    Attr(&'a Attribute),
}

/// Prints a term with an explicit stack.
fn write_term(f: &mut fmt::Formatter<'_>, root: &Term) -> fmt::Result {
    let mut stack = vec![Out::Term(root)];
    let mut items: Vec<Out<'_>> = Vec::new();
    while let Some(out) = stack.pop() {
        match out {
            Out::Text(s) => f.write_str(s)?,
            Out::Symbol(s) => write!(f, "{s}")?,
            Out::Attr(a) => {
                write!(f, " {}", a.keyword)?;
                if let Some(v) = &a.value {
                    stack.push(Out::Term(v));
                    stack.push(Out::Text(" "));
                }
            }
            Out::Term(t) => {
                items.clear();
                match t {
                    Term::Symbol(s) => write!(f, "{s}")?,
                    Term::Literal(l) => write!(f, "{l}")?,
                    Term::Apply(a) => {
                        items.push(Out::Text("("));
                        items.push(Out::Term(&a.head));
                        if let Some(vars) = &a.vars {
                            items.push(Out::Text(" ("));
                            for (i, (x, ty)) in vars.iter().enumerate() {
                                items.push(Out::Text(if i == 0 { "(" } else { " (" }));
                                items.push(Out::Symbol(x));
                                items.push(Out::Text(" "));
                                items.push(Out::Term(ty));
                                items.push(Out::Text(")"));
                            }
                            items.push(Out::Text(")"));
                        }
                        for arg in &a.args {
                            items.push(Out::Text(" "));
                            items.push(Out::Term(arg));
                        }
                        items.push(Out::Text(")"));
                    }
                    Term::Let(l) => {
                        items.push(Out::Text(match l.form {
                            LetForm::Let => "(let (",
                            LetForm::EoDefine => "(eo::define (",
                        }));
                        for (i, (x, v)) in l.bindings.iter().enumerate() {
                            items.push(Out::Text(if i == 0 { "(" } else { " (" }));
                            items.push(Out::Symbol(x));
                            items.push(Out::Text(" "));
                            items.push(Out::Term(v));
                            items.push(Out::Text(")"));
                        }
                        items.push(Out::Text(") "));
                        items.push(Out::Term(&l.body));
                        items.push(Out::Text(")"));
                    }
                    Term::Annotated(a) => {
                        items.push(Out::Text("(! "));
                        items.push(Out::Term(&a.term));
                        items.extend(a.attributes.iter().map(Out::Attr));
                        items.push(Out::Text(")"));
                    }
                }
                stack.extend(items.drain(..).rev());
            }
        }
    }
    Ok(())
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_term(f, self)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Term(`{self}`)")
    }
}

/// A parameter `(<symbol> <type> <attr>*)` of a declaration, definition,
/// program or rule.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypedParam {
    /// The parameter's name.
    pub name: Symbol,
    /// Its type.
    pub ty: Term,
    /// Its attributes (`:implicit`, `:opaque`, `:list`).
    pub attributes: Vec<Attribute>,
}

impl TypedParam {
    /// A parameter without attributes.
    pub fn new(name: Symbol, ty: Term) -> TypedParam {
        TypedParam { name, ty, attributes: Vec::new() }
    }

    /// Whether the parameter carries the attribute `:name`.
    pub fn has(&self, name: &str) -> bool {
        self.attributes.iter().any(|a| a.keyword.as_str() == name)
    }
}

impl fmt::Display for TypedParam {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {}", self.name, self.ty)?;
        for a in &self.attributes {
            write!(f, " {a}")?;
        }
        f.write_str(")")
    }
}

/// A constructor declaration `(<symbol> <sel-dec>*)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstructorDec {
    /// The constructor.
    pub name: Symbol,
    /// Its selectors and their types.
    pub selectors: Vec<(Symbol, Term)>,
}

/// A datatype declaration `(<cons-dec>+) | (par (<symbol>+) (<cons-dec>+))`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DatatypeDec {
    /// The type parameters; empty means no `par`.
    pub params: Vec<Symbol>,
    /// The constructors.
    pub constructors: NonEmpty<ConstructorDec>,
}

impl fmt::Display for DatatypeDec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.params.is_empty() {
            f.write_str("(par (")?;
            write_spaced(f, &self.params)?;
            f.write_str(") ")?;
        }
        f.write_str("(")?;
        for (i, c) in self.constructors.iter().enumerate() {
            if i > 0 {
                f.write_str(" ")?;
            }
            write!(f, "({}", c.name)?;
            for (s, t) in &c.selectors {
                write!(f, " ({s} {t})")?;
            }
            f.write_str(")")?;
        }
        f.write_str(")")?;
        if !self.params.is_empty() {
            f.write_str(")")?;
        }
        Ok(())
    }
}

/// The premises of a rule (`<premises>` of `declare-rule`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RulePremises {
    /// `:premises (<term>*)`: a fixed list of premise patterns.
    Premises(Vec<Term>),
    /// `:premise-list <term> <term>`: any number of premises, combined by the
    /// constructor and matched against the pattern.
    PremiseList {
        /// The pattern.
        pattern: Term,
        /// The variadic operator that combines the premises.
        constructor: Term,
    },
}

/// The conclusion of a rule.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RuleConclusion {
    /// `:conclusion <term>`.
    Conclusion(Term),
    /// `:conclusion-explicit <term>`: a pattern for a conclusion that the step provides.
    Explicit(Term),
}

impl RuleConclusion {
    /// The conclusion term.
    pub fn term(&self) -> &Term {
        match self {
            RuleConclusion::Conclusion(t) | RuleConclusion::Explicit(t) => t,
        }
    }
}

/// `(declare-rule <symbol> (<typed-param>*) <assumption>? <premises>? <arguments>? <reqs>? <conclusion> <attr>*)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RuleDecl {
    /// The rule's name.
    pub name: Symbol,
    /// The free parameters of its patterns.
    pub params: Vec<TypedParam>,
    /// `:assumption <term>`.
    pub assumption: Option<Term>,
    /// `:premises (...)` or `:premise-list ...`.
    pub premises: Option<RulePremises>,
    /// `:args (...)`.
    pub args: Option<Vec<Term>>,
    /// `:requires ((t s)...)`.
    pub requires: Option<Vec<(Term, Term)>>,
    /// `:conclusion` or `:conclusion-explicit`.
    pub conclusion: RuleConclusion,
    /// Trailing attributes (`:sorry`).
    pub attributes: Vec<Attribute>,
}

/// `(program <symbol> (<typed-param>*) :signature (<type>+) <type> ((<term> <term>)*)?)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProgramDecl {
    /// The program's name.
    pub name: Symbol,
    /// The parameters of its cases.
    pub params: Vec<TypedParam>,
    /// The argument types.
    pub arg_types: NonEmpty<Term>,
    /// The return type.
    pub return_type: Term,
    /// The cases; `None` is a forward declaration.
    pub cases: Option<Vec<(Term, Term)>>,
}

/// `(step <symbol> <term>? :rule <symbol> <simple-premises>? <arguments>?)`, also
/// the shape of `step-pop`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Step {
    /// The name bound to the proof.
    pub name: Symbol,
    /// The conclusion that the step claims, if given.
    pub conclusion: Option<Term>,
    /// The rule applied.
    pub rule: Symbol,
    /// `:premises (...)`.
    pub premises: Option<Vec<Term>>,
    /// `:args (...)`.
    pub args: Option<Vec<Term>>,
}

impl Step {
    /// `(step name :rule rule)` without conclusion, premises or arguments.
    pub fn new(name: Symbol, rule: Symbol) -> Step {
        Step { name, conclusion: None, rule, premises: None, args: None }
    }
}

/// A command (`<eo-command>` and `<common-command>` of the manual).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Command {
    /// `(assume <symbol> <term>)`.
    Assume {
        /// The proof name.
        name: Symbol,
        /// The assumed formula.
        formula: Term,
    },
    /// `(assume-push <symbol> <term>)`.
    AssumePush {
        /// The proof name.
        name: Symbol,
        /// The local assumption.
        formula: Term,
    },
    /// `(step ...)`.
    Step(Step),
    /// `(step-pop ...)`.
    StepPop(Step),
    /// `(declare-const <symbol> <type> <attr>*)`.
    DeclareConst {
        /// The constant.
        name: Symbol,
        /// Its type.
        ty: Term,
        /// Its attributes.
        attributes: Vec<Attribute>,
    },
    /// `(declare-parameterized-const <symbol> (<typed-param>*) <type> <attr>*)`.
    DeclareParameterizedConst {
        /// The constant.
        name: Symbol,
        /// Its parameters.
        params: Vec<TypedParam>,
        /// Its type.
        ty: Term,
        /// Its attributes.
        attributes: Vec<Attribute>,
    },
    /// `(declare-consts <lit-category> <type>)`.
    DeclareConsts {
        /// The literal category.
        category: LiteralCategory,
        /// The type of its literals.
        ty: Term,
    },
    /// `(declare-datatype <symbol> <datatype-dec>)`.
    DeclareDatatype {
        /// The datatype.
        name: Symbol,
        /// Its declaration.
        datatype: DatatypeDec,
    },
    /// `(declare-datatypes (<sort-dec>^n) (<datatype-dec>^n))`, with the sort
    /// declarations and datatype declarations paired.
    DeclareDatatypes(Vec<(Symbol, u32, DatatypeDec)>),
    /// `(declare-sort <symbol> <numeral>)`.
    DeclareSort {
        /// The sort.
        name: Symbol,
        /// Its arity.
        arity: u32,
    },
    /// `(declare-rule ...)`.
    DeclareRule(RuleDecl),
    /// `(define <symbol> (<typed-param>*) <term> <attr>*)`.
    Define {
        /// The defined symbol.
        name: Symbol,
        /// Its parameters.
        params: Vec<TypedParam>,
        /// Its body.
        body: Term,
        /// Its attributes (`:type`).
        attributes: Vec<Attribute>,
    },
    /// `(program ...)`.
    Program(ProgramDecl),
    /// `(include <string>)`.
    Include(StrLit),
    /// `(reference <string> <term>?)`.
    Reference {
        /// The referenced SMT-LIB file.
        file: StrLit,
        /// The normalization function.
        normalize: Option<Term>,
    },
    /// `(echo <string>?)`.
    Echo(Option<StrLit>),
    /// `(exit)`.
    Exit,
    /// `(reset)`.
    Reset,
    /// `(set-option <attr>)`, with `<attr> ::= <keyword> <term>?` (manual
    /// "Full syntax for Eunoia commands").
    SetOption {
        /// The option.
        keyword: Keyword,
        /// Its value.
        value: Option<Term>,
    },
}

fn attr_terms<'a>(attrs: &'a [Attribute], out: &mut Vec<&'a Term>) {
    out.extend(attrs.iter().filter_map(|a| a.value.as_ref()));
}

fn param_terms<'a>(params: &'a [TypedParam], out: &mut Vec<&'a Term>) {
    for p in params {
        out.push(&p.ty);
        attr_terms(&p.attributes, out);
    }
}

impl Command {
    /// The terms of the command that are not inside another term, in the
    /// order in which they are written.
    pub fn terms(&self) -> Vec<&Term> {
        let mut out = Vec::new();
        match self {
            Command::Assume { formula, .. } | Command::AssumePush { formula, .. } => out.push(formula),
            Command::Step(s) | Command::StepPop(s) => {
                out.extend(s.conclusion.iter());
                out.extend(s.premises.iter().flatten());
                out.extend(s.args.iter().flatten());
            }
            Command::DeclareConst { ty, attributes, .. } => {
                out.push(ty);
                attr_terms(attributes, &mut out);
            }
            Command::DeclareParameterizedConst { params, ty, attributes, .. } => {
                param_terms(params, &mut out);
                out.push(ty);
                attr_terms(attributes, &mut out);
            }
            Command::DeclareConsts { ty, .. } => out.push(ty),
            Command::DeclareDatatype { datatype, .. } => {
                for c in &datatype.constructors {
                    out.extend(c.selectors.iter().map(|(_, t)| t));
                }
            }
            Command::DeclareDatatypes(dts) => {
                for (_, _, dt) in dts {
                    for c in &dt.constructors {
                        out.extend(c.selectors.iter().map(|(_, t)| t));
                    }
                }
            }
            Command::DeclareSort { .. } | Command::Include(_) | Command::Echo(_) | Command::Exit | Command::Reset => {}
            Command::DeclareRule(r) => {
                param_terms(&r.params, &mut out);
                out.extend(r.assumption.iter());
                match &r.premises {
                    Some(RulePremises::Premises(ps)) => out.extend(ps.iter()),
                    Some(RulePremises::PremiseList { pattern, constructor }) => {
                        out.push(pattern);
                        out.push(constructor);
                    }
                    None => {}
                }
                out.extend(r.args.iter().flatten());
                for (a, b) in r.requires.iter().flatten() {
                    out.push(a);
                    out.push(b);
                }
                out.push(r.conclusion.term());
                attr_terms(&r.attributes, &mut out);
            }
            Command::Define { params, body, attributes, .. } => {
                param_terms(params, &mut out);
                out.push(body);
                attr_terms(attributes, &mut out);
            }
            Command::Program(p) => {
                param_terms(&p.params, &mut out);
                out.extend(p.arg_types.iter());
                out.push(&p.return_type);
                for (l, r) in p.cases.iter().flatten() {
                    out.push(l);
                    out.push(r);
                }
            }
            Command::Reference { normalize, .. } => out.extend(normalize.iter()),
            Command::SetOption { value, .. } => out.extend(value.iter()),
        }
        out
    }
}

fn write_spaced<T: fmt::Display>(f: &mut fmt::Formatter<'_>, items: &[T]) -> fmt::Result {
    for (i, x) in items.iter().enumerate() {
        if i > 0 {
            f.write_str(" ")?;
        }
        write!(f, "{x}")?;
    }
    Ok(())
}

fn write_list<T: fmt::Display>(f: &mut fmt::Formatter<'_>, items: &[T]) -> fmt::Result {
    f.write_str("(")?;
    write_spaced(f, items)?;
    f.write_str(")")
}

fn write_attrs(f: &mut fmt::Formatter<'_>, attrs: &[Attribute]) -> fmt::Result {
    for a in attrs {
        write!(f, " {a}")?;
    }
    Ok(())
}

fn write_step(f: &mut fmt::Formatter<'_>, cmd: &str, s: &Step) -> fmt::Result {
    write!(f, "({cmd} {}", s.name)?;
    if let Some(c) = &s.conclusion {
        write!(f, " {c}")?;
    }
    write!(f, " :rule {}", s.rule)?;
    if let Some(p) = &s.premises {
        f.write_str(" :premises ")?;
        write_list(f, p)?;
    }
    if let Some(a) = &s.args {
        f.write_str(" :args ")?;
        write_list(f, a)?;
    }
    f.write_str(")")
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Command::Assume { name, formula } => write!(f, "(assume {name} {formula})"),
            Command::AssumePush { name, formula } => write!(f, "(assume-push {name} {formula})"),
            Command::Step(s) => write_step(f, "step", s),
            Command::StepPop(s) => write_step(f, "step-pop", s),
            Command::DeclareConst { name, ty, attributes } => {
                write!(f, "(declare-const {name} {ty}")?;
                write_attrs(f, attributes)?;
                f.write_str(")")
            }
            Command::DeclareParameterizedConst { name, params, ty, attributes } => {
                write!(f, "(declare-parameterized-const {name} ")?;
                write_list(f, params)?;
                write!(f, " {ty}")?;
                write_attrs(f, attributes)?;
                f.write_str(")")
            }
            Command::DeclareConsts { category, ty } => write!(f, "(declare-consts {category} {ty})"),
            Command::DeclareDatatype { name, datatype } => write!(f, "(declare-datatype {name} {datatype})"),
            Command::DeclareDatatypes(dts) => {
                f.write_str("(declare-datatypes (")?;
                for (i, (name, arity, _)) in dts.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ")?;
                    }
                    write!(f, "({name} {arity})")?;
                }
                f.write_str(") (")?;
                for (i, (_, _, dt)) in dts.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ")?;
                    }
                    write!(f, "{dt}")?;
                }
                f.write_str("))")
            }
            Command::DeclareSort { name, arity } => write!(f, "(declare-sort {name} {arity})"),
            Command::DeclareRule(r) => {
                write!(f, "(declare-rule {} ", r.name)?;
                write_list(f, &r.params)?;
                if let Some(a) = &r.assumption {
                    write!(f, " :assumption {a}")?;
                }
                match &r.premises {
                    Some(RulePremises::Premises(ps)) => {
                        f.write_str(" :premises ")?;
                        write_list(f, ps)?;
                    }
                    Some(RulePremises::PremiseList { pattern, constructor }) => write!(f, " :premise-list {pattern} {constructor}")?,
                    None => {}
                }
                if let Some(a) = &r.args {
                    f.write_str(" :args ")?;
                    write_list(f, a)?;
                }
                if let Some(reqs) = &r.requires {
                    f.write_str(" :requires (")?;
                    for (i, (a, b)) in reqs.iter().enumerate() {
                        if i > 0 {
                            f.write_str(" ")?;
                        }
                        write!(f, "({a} {b})")?;
                    }
                    f.write_str(")")?;
                }
                match &r.conclusion {
                    RuleConclusion::Conclusion(c) => write!(f, " :conclusion {c}")?,
                    RuleConclusion::Explicit(c) => write!(f, " :conclusion-explicit {c}")?,
                }
                write_attrs(f, &r.attributes)?;
                f.write_str(")")
            }
            Command::Define { name, params, body, attributes } => {
                write!(f, "(define {name} ")?;
                write_list(f, params)?;
                write!(f, " {body}")?;
                write_attrs(f, attributes)?;
                f.write_str(")")
            }
            Command::Program(p) => {
                write!(f, "(program {} ", p.name)?;
                write_list(f, &p.params)?;
                f.write_str(" :signature ")?;
                write_list(f, &p.arg_types)?;
                write!(f, " {}", p.return_type)?;
                if let Some(cases) = &p.cases {
                    f.write_str(" (")?;
                    for (i, (l, r)) in cases.iter().enumerate() {
                        if i > 0 {
                            f.write_str(" ")?;
                        }
                        write!(f, "({l} {r})")?;
                    }
                    f.write_str(")")?;
                }
                f.write_str(")")
            }
            Command::Include(s) => write!(f, "(include {s})"),
            Command::Reference { file, normalize } => {
                write!(f, "(reference {file}")?;
                if let Some(n) = normalize {
                    write!(f, " {n}")?;
                }
                f.write_str(")")
            }
            Command::Echo(s) => match s {
                Some(s) => write!(f, "(echo {s})"),
                None => f.write_str("(echo)"),
            },
            Command::Exit => f.write_str("(exit)"),
            Command::Reset => f.write_str("(reset)"),
            Command::SetOption { keyword, value } => match value {
                Some(v) => write!(f, "(set-option {keyword} {v})"),
                None => write!(f, "(set-option {keyword})"),
            },
        }
    }
}

/// A sequence of commands: the content of a signature file or a proof file.
///
/// A script read by [`parse_script`](crate::parse_script) also knows where
/// each command was written. A command added or changed through the methods
/// here has no position; equality, hashing and printing ignore positions.
#[derive(Clone, Default)]
pub struct Script {
    commands: Vec<Command>,
    positions: Vec<Option<Position>>,
}

impl Script {
    /// A script of the given commands, without positions.
    pub fn new(commands: Vec<Command>) -> Script {
        let positions = vec![None; commands.len()];
        Script { commands, positions }
    }

    pub(crate) fn with_positions(commands: Vec<Command>, positions: Vec<Option<Position>>) -> Script {
        Script { commands, positions }
    }

    /// The commands in order.
    pub fn commands(&self) -> &[Command] {
        &self.commands
    }

    /// The commands, consuming the script.
    pub fn into_commands(self) -> Vec<Command> {
        self.commands
    }

    /// The number of commands.
    pub fn len(&self) -> usize {
        self.commands.len()
    }

    /// Whether the script has no command.
    pub fn is_empty(&self) -> bool {
        self.commands.is_empty()
    }

    /// The commands with the positions where they begin, when known.
    pub fn iter(&self) -> impl Iterator<Item = (Option<Position>, &Command)> {
        self.commands.iter().zip(&self.positions).map(|(c, p)| (*p, c))
    }

    /// Where the command at `index` begins, when it was read from a text.
    pub fn position(&self, index: usize) -> Option<Position> {
        self.positions.get(index).copied().flatten()
    }

    /// The command at `index`, to change it; it loses its position.
    pub fn command_mut(&mut self, index: usize) -> Option<&mut Command> {
        if let Some(p) = self.positions.get_mut(index) {
            *p = None;
        }
        self.commands.get_mut(index)
    }

    /// Appends a command.
    pub fn push(&mut self, command: Command) {
        self.commands.push(command);
        self.positions.push(None);
    }

    /// Inserts a command at `index` (at the end if `index` is past it).
    pub fn insert(&mut self, index: usize, command: Command) {
        let index = index.min(self.commands.len());
        self.commands.insert(index, command);
        self.positions.insert(index, None);
    }

    /// Removes the command at `index`, if there is one.
    pub fn remove(&mut self, index: usize) -> Option<Command> {
        if index >= self.commands.len() {
            return None;
        }
        self.positions.remove(index);
        Some(self.commands.remove(index))
    }

    /// Appends the commands of `other`, with their positions.
    pub fn append(&mut self, other: Script) {
        self.commands.extend(other.commands);
        self.positions.extend(other.positions);
    }
}

impl From<Vec<Command>> for Script {
    fn from(commands: Vec<Command>) -> Script {
        Script::new(commands)
    }
}

impl FromIterator<Command> for Script {
    fn from_iter<I: IntoIterator<Item = Command>>(iter: I) -> Script {
        Script::new(iter.into_iter().collect())
    }
}

impl PartialEq for Script {
    fn eq(&self, other: &Script) -> bool {
        self.commands == other.commands
    }
}

impl Eq for Script {}

impl Hash for Script {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.commands.hash(state);
    }
}

impl fmt::Debug for Script {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Script").field("commands", &self.commands).finish()
    }
}

impl fmt::Display for Script {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for c in &self.commands {
            writeln!(f, "{c}")?;
        }
        Ok(())
    }
}
