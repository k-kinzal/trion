//! Identifiers, attributes, sorts and terms (§3.3–§3.6).
//!
//! ```text
//! ⟨index⟩           ::= ⟨numeral⟩ | ⟨symbol⟩
//! ⟨identifier⟩      ::= ⟨symbol⟩ | ( _ ⟨symbol⟩ ⟨index⟩+ )
//! ⟨attribute_value⟩ ::= ⟨spec_constant⟩ | ⟨symbol⟩ | ( ⟨s_expr⟩* )
//! ⟨attribute⟩       ::= ⟨keyword⟩ | ⟨keyword⟩ ⟨attribute_value⟩
//! ⟨sort⟩            ::= ⟨identifier⟩ | ( ⟨identifier⟩ ⟨sort⟩+ )
//! ⟨qual_identifier⟩ ::= ⟨identifier⟩ | ( as ⟨identifier⟩ ⟨sort⟩ )
//! ⟨var_binding⟩     ::= ( ⟨symbol⟩ ⟨term⟩ )
//! ⟨sorted_var⟩      ::= ( ⟨symbol⟩ ⟨sort⟩ )
//! ⟨symbol_⟩         ::= ⟨symbol⟩ | _
//! ⟨pattern⟩         ::= ⟨symbol_⟩ | ( ⟨symbol⟩ ⟨symbol_⟩+ )
//! ⟨match_case⟩      ::= ( ⟨pattern⟩ ⟨term⟩ )
//! ⟨term⟩            ::= ⟨spec_constant⟩ | ⟨qual_identifier⟩ | ( ⟨qual_identifier⟩ ⟨term⟩+ )
//!                     | ( let ( ⟨var_binding⟩+ ) ⟨term⟩ ) | ( lambda ( ⟨sorted_var⟩+ ) ⟨term⟩ )
//!                     | ( forall ( ⟨sorted_var⟩+ ) ⟨term⟩ ) | ( exists ( ⟨sorted_var⟩+ ) ⟨term⟩ )
//!                     | ( match ⟨term⟩ ( ⟨match_case⟩+ ) ) | ( ! ⟨term⟩ ⟨attribute⟩+ )
//! ```
//!
//! This is the grammar of SMT-LIB 2.7 (Appendix B), which added `lambda`
//! and the wildcard `_` in patterns to that of 2.6 (§1.1.2). Every `+` of
//! the grammar is a [`NonEmpty`], so a value of these types always prints
//! as text the grammar accepts. Whether a term is well sorted is not a
//! question of the grammar, and this crate does not answer it.
//!
//! A [`Dialect`] may add binders named by a symbol
//! ([`Dialect::with_binder`]); they are read as [`Term::Binder`] only by
//! [`Term::from_spanned_in`] with that dialect, never by the strict reader.
//!
//! Reading ([`Term::from_spanned_in`], [`Sort::from_spanned`]), printing
//! ([`Term::write`], [`Term::to_sexpr`]), traversal ([`Term::iter`],
//! [`Term::fold`], [`Sort::fold`]) and dropping are iterative, so the depth
//! of a term does not grow the call stack. The derived traits (`Clone`,
//! `PartialEq`, `Hash`, `Ord`, `Debug`) recurse; the reader's depth limit
//! ([`Dialect::max_depth`]) keeps them within a 2 MiB stack for the values
//! it reads.

use crate::error::{Error, Result};
use crate::lexicon::{Dialect, ExtendedConstant, Keyword, Numeral, Reserved, SpecConstant, Symbol};
use crate::read;
use crate::sexpr::{read as read_sexpr, Atom, SExpr, Spanned, SpannedKind};
use std::fmt;
use std::ops::Deref;

/// A sequence with at least one element: the `+` of the grammar.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NonEmpty<T>(Vec<T>);

impl<T> NonEmpty<T> {
    /// The sequence `items`, or `None` when it is empty.
    pub fn new(items: Vec<T>) -> Option<NonEmpty<T>> {
        if items.is_empty() {
            None
        } else {
            Some(NonEmpty(items))
        }
    }

    /// The sequence of the single element `item`.
    pub fn one(item: T) -> NonEmpty<T> {
        NonEmpty(vec![item])
    }

    /// The first element.
    pub fn first(&self) -> &T {
        &self.0[0]
    }

    /// The elements, as a vector.
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }

    /// Appends `item`.
    pub fn push(&mut self, item: T) {
        self.0.push(item);
    }
}

impl<T> Deref for NonEmpty<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.0
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

impl<T> TryFrom<Vec<T>> for NonEmpty<T> {
    type Error = Error;

    /// The sequence `items`; an error of kind
    /// [`crate::ErrorKind::Construction`] when it is empty.
    fn try_from(items: Vec<T>) -> Result<NonEmpty<T>> {
        NonEmpty::new(items).ok_or_else(|| Error::construction("the sequence needs at least one element (the + of the grammar)"))
    }
}

/// An index of an indexed identifier (§3.3).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Index {
    /// A numeral index.
    Numeral(Numeral),
    /// A symbol index.
    Symbol(Symbol),
}

/// An identifier (§3.3): a symbol, or an indexed symbol `(_ f i1 … in)`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Identifier {
    symbol: Symbol,
    indices: Vec<Index>,
}

impl Identifier {
    /// The simple identifier `symbol`.
    pub fn simple(symbol: Symbol) -> Identifier {
        Identifier { symbol, indices: Vec::new() }
    }

    /// The indexed identifier `(_ symbol indices…)`.
    pub fn indexed(symbol: Symbol, indices: NonEmpty<Index>) -> Identifier {
        Identifier { symbol, indices: indices.into_vec() }
    }

    /// The simple identifier named `name`; an error when `name` cannot be
    /// a symbol ([`Symbol::new`]).
    pub fn named(name: &str) -> Result<Identifier> {
        Ok(Identifier::simple(Symbol::new(name)?))
    }

    /// The symbol.
    pub fn symbol(&self) -> &Symbol {
        &self.symbol
    }

    /// The indices; empty for a simple identifier.
    pub fn indices(&self) -> &[Index] {
        &self.indices
    }

    /// The symbol, when the identifier is simple.
    pub fn as_simple(&self) -> Option<&Symbol> {
        self.indices.is_empty().then_some(&self.symbol)
    }

    /// Whether the identifier is the simple identifier `name`.
    pub fn is(&self, name: &str) -> bool {
        self.indices.is_empty() && self.symbol.as_str() == name
    }

    /// The S-expression of this identifier.
    pub fn to_sexpr(&self) -> SExpr {
        if self.indices.is_empty() {
            return SExpr::symbol(self.symbol.clone());
        }
        let mut items = vec![SExpr::reserved(Reserved::Underscore), SExpr::symbol(self.symbol.clone())];
        items.extend(self.indices.iter().map(|index| match index {
            Index::Numeral(n) => SExpr::constant(SpecConstant::Numeral(n.clone())),
            Index::Symbol(s) => SExpr::symbol(s.clone()),
        }));
        SExpr::List(items)
    }

    /// Reads an identifier.
    pub fn from_spanned(node: &Spanned) -> Result<Identifier> {
        if let Some(symbol) = node.as_symbol() {
            return Ok(Identifier::simple(symbol.clone()));
        }
        let Some(rest) = node.headed(Reserved::Underscore) else {
            return Err(node.expected("an identifier: ⟨symbol⟩ or ( _ ⟨symbol⟩ ⟨index⟩+ )"));
        };
        let Some((symbol, indices)) = rest.split_first() else {
            return Err(node.error("an indexed identifier needs a symbol and at least one index (§3.3)"));
        };
        let symbol = symbol.expect_symbol("the symbol of an indexed identifier")?.clone();
        if indices.is_empty() {
            return Err(node.error("an indexed identifier needs at least one index (§3.3)"));
        }
        let indices = indices
            .iter()
            .map(|i| match (i.as_symbol(), i.as_constant()) {
                (Some(s), _) => Ok(Index::Symbol(s.clone())),
                (_, Some(SpecConstant::Numeral(n))) => Ok(Index::Numeral(n.clone())),
                _ => Err(i.expected("an index: ⟨numeral⟩ or ⟨symbol⟩")),
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Identifier { symbol, indices })
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_sexpr().fmt(f)
    }
}

/// A sort (§3.5): an identifier applied to zero or more sorts.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sort {
    identifier: Identifier,
    arguments: Vec<Sort>,
}

impl Sort {
    /// The sort named by `identifier` with no arguments.
    pub fn simple(identifier: Identifier) -> Sort {
        Sort { identifier, arguments: Vec::new() }
    }

    /// The sort named `name` with no arguments; an error when `name` cannot
    /// be a symbol.
    pub fn named(name: &str) -> Result<Sort> {
        Ok(Sort::simple(Identifier::named(name)?))
    }

    /// `(identifier arguments…)`.
    pub fn apply(identifier: Identifier, arguments: NonEmpty<Sort>) -> Sort {
        Sort { identifier, arguments: arguments.into_vec() }
    }

    fn word(name: &str) -> Sort {
        Sort::simple(Identifier::simple(Symbol::new(name).unwrap_or_else(|_| unreachable!("{name} is a symbol"))))
    }

    /// `Bool`.
    pub fn bool() -> Sort {
        Sort::word("Bool")
    }

    /// `Int`.
    pub fn int() -> Sort {
        Sort::word("Int")
    }

    /// `Real`.
    pub fn real() -> Sort {
        Sort::word("Real")
    }

    /// The identifier: the sort symbol or sort parameter.
    pub fn identifier(&self) -> &Identifier {
        &self.identifier
    }

    /// The arguments; empty for `⟨identifier⟩`.
    pub fn arguments(&self) -> &[Sort] {
        &self.arguments
    }

    /// Whether this sort is the simple sort `name`.
    pub fn is(&self, name: &str) -> bool {
        self.arguments.is_empty() && self.identifier.is(name)
    }

    /// This sort and the sorts in it, in pre-order.
    pub fn iter(&self) -> impl Iterator<Item = &Sort> {
        let mut pending = vec![self];
        std::iter::from_fn(move || {
            let sort = pending.pop()?;
            pending.extend(sort.arguments.iter().rev());
            Some(sort)
        })
    }

    /// Folds this sort bottom-up: `f` gets each sort with the results of its
    /// arguments, in order, and the result of the whole sort is returned.
    /// Iterative.
    pub fn fold<T>(&self, mut f: impl FnMut(&Sort, Vec<T>) -> T) -> T {
        let mut frames: Vec<(&Sort, std::slice::Iter<'_, Sort>, Vec<T>)> = vec![(self, self.arguments.iter(), Vec::new())];
        loop {
            let Some((_, arguments, _)) = frames.last_mut() else { unreachable!("the root frame is popped last") };
            if let Some(argument) = arguments.next() {
                frames.push((argument, argument.arguments.iter(), Vec::new()));
                continue;
            }
            let Some((sort, _, results)) = frames.pop() else { unreachable!() };
            let value = f(sort, results);
            match frames.last_mut() {
                Some((_, _, results)) => results.push(value),
                None => return value,
            }
        }
    }

    /// The S-expression of this sort.
    pub fn to_sexpr(&self) -> SExpr {
        self.fold(|sort, arguments: Vec<SExpr>| {
            if arguments.is_empty() {
                sort.identifier.to_sexpr()
            } else {
                let mut items = Vec::with_capacity(arguments.len() + 1);
                items.push(sort.identifier.to_sexpr());
                items.extend(arguments);
                SExpr::List(items)
            }
        })
    }

    /// Writes this sort in `dialect`.
    pub fn write<W: fmt::Write + ?Sized>(&self, out: &mut W, dialect: &Dialect) -> fmt::Result {
        self.to_sexpr().write(out, dialect)
    }

    /// The text of this sort in `dialect`.
    pub fn to_text(&self, dialect: &Dialect) -> String {
        self.to_sexpr().to_text(dialect)
    }

    /// Reads a sort.
    pub fn from_spanned(node: &Spanned) -> Result<Sort> {
        enum Step<'a> {
            Visit(&'a Spanned),
            Build(Identifier, usize),
        }
        let mut steps = vec![Step::Visit(node)];
        let mut values: Vec<Sort> = Vec::new();
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(node) => match node.kind() {
                    SpannedKind::Atom(_) => values.push(Sort::simple(Identifier::from_spanned(node)?)),
                    SpannedKind::List(items) => {
                        if items.first().is_some_and(|f| f.is_reserved(Reserved::Underscore)) {
                            values.push(Sort::simple(Identifier::from_spanned(node)?));
                            continue;
                        }
                        let Some((head, arguments)) = items.split_first() else {
                            return Err(node.expected("a sort"));
                        };
                        if arguments.is_empty() {
                            return Err(node.error("a parenthesized sort needs at least one argument sort (§3.5)"));
                        }
                        steps.push(Step::Build(Identifier::from_spanned(head)?, arguments.len()));
                        steps.extend(arguments.iter().rev().map(Step::Visit));
                    }
                },
                Step::Build(identifier, n) => {
                    let arguments = values.split_off(values.len() - n);
                    values.push(Sort { identifier, arguments });
                }
            }
        }
        values.pop().ok_or_else(|| node.expected("a sort"))
    }

    /// Reads a sort from `text` in strict SMT-LIB 2.7.
    pub fn parse(text: &str) -> Result<Sort> {
        Sort::from_spanned(&read_sexpr(text, &Dialect::strict())?)
    }
}

impl Drop for Sort {
    fn drop(&mut self) {
        if self.arguments.iter().all(|a| a.arguments.is_empty()) {
            return;
        }
        let mut pending = std::mem::take(&mut self.arguments);
        while let Some(mut sort) = pending.pop() {
            pending.append(&mut sort.arguments);
        }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write(f, &Dialect::strict())
    }
}

impl std::str::FromStr for Sort {
    type Err = Error;
    fn from_str(text: &str) -> Result<Sort> {
        Sort::parse(text)
    }
}

/// The value of an attribute (§3.4).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AttributeValue {
    /// A special constant.
    Constant(SpecConstant),
    /// A symbol.
    Symbol(Symbol),
    /// A parenthesized sequence of S-expressions.
    List(Vec<SExpr>),
}

impl AttributeValue {
    /// The S-expression of this value.
    pub fn to_sexpr(&self) -> SExpr {
        match self {
            AttributeValue::Constant(c) => SExpr::constant(c.clone()),
            AttributeValue::Symbol(s) => SExpr::symbol(s.clone()),
            AttributeValue::List(items) => SExpr::List(items.clone()),
        }
    }

    /// Reads an attribute value; `None` when `node` is a keyword or a
    /// reserved word, which cannot be a value.
    pub fn from_spanned(node: &Spanned) -> Option<AttributeValue> {
        match node.kind() {
            SpannedKind::Atom(Atom::Constant(c)) => Some(AttributeValue::Constant(c.clone())),
            SpannedKind::Atom(Atom::Symbol(s)) => Some(AttributeValue::Symbol(s.clone())),
            SpannedKind::List(_) => node.to_sexpr().into_list().ok().map(AttributeValue::List),
            _ => None,
        }
    }

    /// `⟨b_value⟩ ::= true | false`, if this value is one.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            AttributeValue::Symbol(s) if s.as_str() == "true" => Some(true),
            AttributeValue::Symbol(s) if s.as_str() == "false" => Some(false),
            _ => None,
        }
    }
}

/// An attribute (§3.4): a keyword with an optional value.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Attribute {
    keyword: Keyword,
    value: Option<AttributeValue>,
}

impl Attribute {
    /// The attribute `keyword` without a value.
    pub fn flag(keyword: Keyword) -> Attribute {
        Attribute { keyword, value: None }
    }

    /// The attribute `keyword value`.
    pub fn with_value(keyword: Keyword, value: AttributeValue) -> Attribute {
        Attribute { keyword, value: Some(value) }
    }

    fn keyword_named(name: &str) -> Keyword {
        Keyword::new(name).unwrap_or_else(|_| unreachable!("{name} is a keyword"))
    }

    /// `:named name` (§3.6.5).
    pub fn named(name: Symbol) -> Attribute {
        Attribute::with_value(Attribute::keyword_named("named"), AttributeValue::Symbol(name))
    }

    /// `:pattern (terms…)` (§3.6.5). The grammar of attribute values
    /// admits the empty list too, and so does this constructor.
    pub fn pattern(terms: Vec<Term>) -> Attribute {
        Attribute::with_value(Attribute::keyword_named("pattern"), AttributeValue::List(terms.iter().map(Term::to_sexpr).collect()))
    }

    /// The attribute name.
    pub fn keyword(&self) -> &Keyword {
        &self.keyword
    }

    /// The value, if any.
    pub fn value(&self) -> Option<&AttributeValue> {
        self.value.as_ref()
    }

    /// Appends the S-expressions of this attribute (one or two) to `out`.
    pub fn push_sexprs(&self, out: &mut Vec<SExpr>) {
        out.push(SExpr::keyword(self.keyword.clone()));
        if let Some(value) = &self.value {
            out.push(value.to_sexpr());
        }
    }

    /// Reads a sequence of attributes: each keyword takes the next node as
    /// its value unless that node is a keyword (or the sequence ends).
    pub fn sequence_from_spanned(nodes: &[Spanned]) -> Result<Vec<Attribute>> {
        let mut out = Vec::new();
        let mut rest = nodes.iter().peekable();
        while let Some(node) = rest.next() {
            let keyword = node.expect_keyword("an attribute (a keyword)")?.clone();
            let value = match rest.peek() {
                None => None,
                Some(next) if next.as_keyword().is_some() => None,
                Some(next) => match AttributeValue::from_spanned(next) {
                    Some(value) => {
                        rest.next();
                        Some(value)
                    }
                    None => return Err(next.expected("an attribute value: ⟨spec_constant⟩, ⟨symbol⟩ or ( ⟨s_expr⟩* )")),
                },
            };
            out.push(Attribute { keyword, value });
        }
        Ok(out)
    }
}

impl fmt::Display for Attribute {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.keyword)?;
        if let Some(value) = &self.value {
            write!(f, " {}", value.to_sexpr())?;
        }
        Ok(())
    }
}

/// A qualified identifier (§3.6): an identifier, optionally annotated with
/// its result sort as `(as f σ)`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QualIdentifier {
    identifier: Identifier,
    sort: Option<Sort>,
}

impl QualIdentifier {
    /// The unannotated identifier.
    pub fn plain(identifier: Identifier) -> QualIdentifier {
        QualIdentifier { identifier, sort: None }
    }

    /// `(as identifier sort)`.
    pub fn annotated(identifier: Identifier, sort: Sort) -> QualIdentifier {
        QualIdentifier { identifier, sort: Some(sort) }
    }

    /// The identifier.
    pub fn identifier(&self) -> &Identifier {
        &self.identifier
    }

    /// The sort of `(as f σ)`, if annotated.
    pub fn sort(&self) -> Option<&Sort> {
        self.sort.as_ref()
    }

    /// The S-expression of this qualified identifier.
    pub fn to_sexpr(&self) -> SExpr {
        match &self.sort {
            None => self.identifier.to_sexpr(),
            Some(sort) => SExpr::List(vec![SExpr::reserved(Reserved::As), self.identifier.to_sexpr(), sort.to_sexpr()]),
        }
    }

    /// Reads a qualified identifier.
    pub fn from_spanned(node: &Spanned) -> Result<QualIdentifier> {
        if let Some(rest) = node.headed(Reserved::As) {
            read::arity(node, rest, 2, "as")?;
            return Ok(QualIdentifier::annotated(Identifier::from_spanned(&rest[0])?, Sort::from_spanned(&rest[1])?));
        }
        Ok(QualIdentifier::plain(Identifier::from_spanned(node)?))
    }
}

impl fmt::Display for QualIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_sexpr().fmt(f)
    }
}

/// `( ⟨symbol⟩ ⟨term⟩ )`, a binding of `let`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VarBinding {
    variable: Symbol,
    term: Term,
}

impl VarBinding {
    /// `(variable term)`.
    pub fn new(variable: Symbol, term: Term) -> VarBinding {
        VarBinding { variable, term }
    }

    /// The variable.
    pub fn variable(&self) -> &Symbol {
        &self.variable
    }

    /// The term it stands for.
    pub fn term(&self) -> &Term {
        &self.term
    }
}

/// `( ⟨symbol⟩ ⟨sort⟩ )`, a variable with its sort.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SortedVar {
    variable: Symbol,
    sort: Sort,
}

impl SortedVar {
    /// `(variable sort)`.
    pub fn new(variable: Symbol, sort: Sort) -> SortedVar {
        SortedVar { variable, sort }
    }

    /// The variable.
    pub fn variable(&self) -> &Symbol {
        &self.variable
    }

    /// Its sort.
    pub fn sort(&self) -> &Sort {
        &self.sort
    }

    /// The S-expression `(variable sort)`.
    pub fn to_sexpr(&self) -> SExpr {
        SExpr::List(vec![SExpr::symbol(self.variable.clone()), self.sort.to_sexpr()])
    }

    /// Reads `(variable sort)`.
    pub fn from_spanned(node: &Spanned) -> Result<SortedVar> {
        match node.as_list() {
            Some([variable, sort]) => Ok(SortedVar { variable: variable.expect_symbol("a variable")?.clone(), sort: Sort::from_spanned(sort)? }),
            _ => Err(node.expected("a sorted variable ( ⟨symbol⟩ ⟨sort⟩ )")),
        }
    }
}

/// A pattern of a match case (§3.6.1).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Pattern {
    /// A symbol: a variable or a nullary constructor.
    Symbol(Symbol),
    /// `_`: matches anything and binds nothing (SMT-LIB 2.7).
    Wildcard,
    /// `(c x1 … xk)`: a constructor applied to variables; `None` is `_`.
    Constructor(Symbol, NonEmpty<Option<Symbol>>),
}

impl Pattern {
    /// The S-expression of this pattern.
    pub fn to_sexpr(&self) -> SExpr {
        let symbol_ = |s: &Option<Symbol>| match s {
            Some(s) => SExpr::symbol(s.clone()),
            None => SExpr::reserved(Reserved::Underscore),
        };
        match self {
            Pattern::Symbol(s) => SExpr::symbol(s.clone()),
            Pattern::Wildcard => SExpr::reserved(Reserved::Underscore),
            Pattern::Constructor(head, vars) => {
                let mut items = vec![SExpr::symbol(head.clone())];
                items.extend(vars.iter().map(symbol_));
                SExpr::List(items)
            }
        }
    }

    /// Reads a pattern.
    pub fn from_spanned(node: &Spanned) -> Result<Pattern> {
        let symbol_ = |p: &Spanned| -> Result<Option<Symbol>> {
            if p.is_reserved(Reserved::Underscore) {
                return Ok(None);
            }
            p.expect_symbol("a pattern variable or _ (patterns are not nested, §3.6.1)").map(|s| Some(s.clone()))
        };
        match node.kind() {
            SpannedKind::Atom(Atom::Symbol(s)) => Ok(Pattern::Symbol(s.clone())),
            SpannedKind::Atom(Atom::Reserved(Reserved::Underscore)) => Ok(Pattern::Wildcard),
            SpannedKind::List(parts) if parts.len() >= 2 => {
                let head = parts[0].expect_symbol("a constructor")?.clone();
                let vars = parts[1..].iter().map(symbol_).collect::<Result<Vec<_>>>()?;
                Ok(Pattern::Constructor(head, NonEmpty(vars)))
            }
            _ => Err(node.expected("a pattern: ⟨symbol_⟩ or ( ⟨symbol⟩ ⟨symbol_⟩+ )")),
        }
    }
}

/// `( ⟨pattern⟩ ⟨term⟩ )`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MatchCase {
    pattern: Pattern,
    term: Term,
}

impl MatchCase {
    /// `(pattern term)`.
    pub fn new(pattern: Pattern, term: Term) -> MatchCase {
        MatchCase { pattern, term }
    }

    /// The pattern.
    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// The term of this case.
    pub fn term(&self) -> &Term {
        &self.term
    }
}

/// A term (§3.6).
///
/// ```
/// use smtlib::{Dialect, Term};
///
/// let term: Term = "(forall ((x Int)) (! (=> (> x 0) (p x)) :pattern ((p x))))".parse().unwrap();
/// assert!(matches!(term, Term::Forall(..)));
/// // Every subterm, in pre-order; the terms of :pattern are attribute values.
/// assert_eq!(term.iter().count(), 8);
/// // The depth, folded bottom-up without recursion.
/// assert_eq!(term.fold(|_, children: Vec<usize>| 1 + children.into_iter().max().unwrap_or(0)), 5);
/// assert_eq!(term.to_string(), "(forall ((x Int)) (! (=> (> x 0) (p x)) :pattern ((p x))))");
/// ```
///
/// A term is dropped without recursion, so `Term` implements [`Drop`] and
/// cannot be destructured by move; match a reference instead:
///
/// ```
/// use smtlib::Term;
///
/// let term: Term = "(! p :named a)".parse().unwrap();
/// let Term::Annotated(inner, attributes) = &term else { unreachable!() };
/// assert_eq!((inner.to_string(), attributes.len()), ("p".to_string(), 1));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Term {
    /// A special constant.
    Constant(SpecConstant),
    /// A qualified identifier alone: a constant symbol or a variable.
    Identifier(QualIdentifier),
    /// A function symbol applied to one or more terms.
    Application(QualIdentifier, NonEmpty<Term>),
    /// `(let (bindings…) body)`.
    Let(NonEmpty<VarBinding>, Box<Term>),
    /// `(lambda (variables…) body)` (SMT-LIB 2.7, §3.6.1).
    Lambda(NonEmpty<SortedVar>, Box<Term>),
    /// `(forall (variables…) body)`.
    Forall(NonEmpty<SortedVar>, Box<Term>),
    /// `(exists (variables…) body)`.
    Exists(NonEmpty<SortedVar>, Box<Term>),
    /// `(match term (cases…))`.
    Match(Box<Term>, NonEmpty<MatchCase>),
    /// `(! term attributes…)`.
    Annotated(Box<Term>, NonEmpty<Attribute>),
    /// `(b (variables…) body)` for a binder `b` a dialect adds
    /// ([`Dialect::with_binder`]; not SMT-LIB). It prints as written in
    /// every dialect, and reads back only in a dialect with that binder.
    Binder(Symbol, NonEmpty<SortedVar>, Box<Term>),
}

/// The immediate subterms of a term, in order ([`Term::children`]).
#[derive(Debug, Clone)]
pub struct Children<'a> {
    first: Option<&'a Term>,
    terms: std::slice::Iter<'a, Term>,
    bindings: std::slice::Iter<'a, VarBinding>,
    cases: std::slice::Iter<'a, MatchCase>,
    last: Option<&'a Term>,
}

impl<'a> Iterator for Children<'a> {
    type Item = &'a Term;
    fn next(&mut self) -> Option<&'a Term> {
        if let Some(first) = self.first.take() {
            return Some(first);
        }
        self.terms.next().or_else(|| self.bindings.next().map(VarBinding::term)).or_else(|| self.cases.next().map(MatchCase::term)).or_else(|| self.last.take())
    }
}

/// What a term is without its subterms: the step that builds it from them.
enum Build<'a> {
    Application(&'a QualIdentifier),
    Let(&'a NonEmpty<VarBinding>),
    Binder(SExpr, &'a NonEmpty<SortedVar>),
    Match(&'a NonEmpty<MatchCase>),
    Annotated(&'a NonEmpty<Attribute>),
}

impl Term {
    /// The term of `symbol` alone: a constant or a variable.
    pub fn symbol(symbol: Symbol) -> Term {
        Term::Identifier(QualIdentifier::plain(Identifier::simple(symbol)))
    }

    /// The immediate subterms, in the order of the text: the arguments of
    /// an application; the terms of the bindings of a `let`, then its body;
    /// the body of a binder; the term of a `match`, then the term of each
    /// case; the term of an annotation. The terms of `:pattern` values are
    /// attribute values, not subterms.
    pub fn children(&self) -> Children<'_> {
        let mut children = Children { first: None, terms: [].iter(), bindings: [].iter(), cases: [].iter(), last: None };
        match self {
            Term::Constant(_) | Term::Identifier(_) => {}
            Term::Application(_, args) => children.terms = args.0.iter(),
            Term::Let(bindings, body) => {
                children.bindings = bindings.0.iter();
                children.last = Some(body);
            }
            Term::Lambda(_, body) | Term::Forall(_, body) | Term::Exists(_, body) | Term::Binder(_, _, body) => children.last = Some(body),
            Term::Match(term, cases) => {
                children.first = Some(term);
                children.cases = cases.0.iter();
            }
            Term::Annotated(term, _) => children.last = Some(term),
        }
        children
    }

    /// This term and every subterm ([`Term::children`]), in pre-order.
    /// Iterative.
    pub fn iter(&self) -> impl Iterator<Item = &Term> {
        let mut root = Some(self);
        let mut pending: Vec<Children<'_>> = Vec::new();
        std::iter::from_fn(move || {
            if let Some(root) = root.take() {
                pending.push(root.children());
                return Some(root);
            }
            loop {
                let children = pending.last_mut()?;
                match children.next() {
                    Some(child) => {
                        pending.push(child.children());
                        return Some(child);
                    }
                    None => {
                        pending.pop();
                    }
                }
            }
        })
    }

    /// Folds this term bottom-up: `f` gets each term with the results of
    /// its children ([`Term::children`]), in order, and the result of the
    /// whole term is returned. Iterative.
    pub fn fold<T>(&self, mut f: impl FnMut(&Term, Vec<T>) -> T) -> T {
        match self.try_fold(|term, children| Ok::<T, std::convert::Infallible>(f(term, children))) {
            Ok(value) => value,
            Err(never) => match never {},
        }
    }

    /// [`Term::fold`] with a function that can fail: the first error stops
    /// the fold and is returned.
    pub fn try_fold<T, E>(&self, mut f: impl FnMut(&Term, Vec<T>) -> std::result::Result<T, E>) -> std::result::Result<T, E> {
        let mut frames: Vec<(&Term, Children<'_>, Vec<T>)> = vec![(self, self.children(), Vec::new())];
        loop {
            let Some((_, children, _)) = frames.last_mut() else { unreachable!("the root frame is popped last") };
            if let Some(child) = children.next() {
                frames.push((child, child.children(), Vec::new()));
                continue;
            }
            let Some((term, _, results)) = frames.pop() else { unreachable!() };
            let value = f(term, results)?;
            match frames.last_mut() {
                Some((_, _, results)) => results.push(value),
                None => return Ok(value),
            }
        }
    }

    /// The S-expression of this term. Iterative.
    pub fn to_sexpr(&self) -> SExpr {
        let sorted_vars = |vars: &NonEmpty<SortedVar>| SExpr::List(vars.iter().map(SortedVar::to_sexpr).collect());
        self.fold(|term, mut children: Vec<SExpr>| {
            let build = match term {
                Term::Constant(c) => return SExpr::constant(c.clone()),
                Term::Identifier(q) => return q.to_sexpr(),
                Term::Application(q, _) => Build::Application(q),
                Term::Let(bindings, _) => Build::Let(bindings),
                Term::Lambda(vars, _) => Build::Binder(SExpr::reserved(Reserved::Lambda), vars),
                Term::Forall(vars, _) => Build::Binder(SExpr::reserved(Reserved::Forall), vars),
                Term::Exists(vars, _) => Build::Binder(SExpr::reserved(Reserved::Exists), vars),
                Term::Binder(name, vars, _) => Build::Binder(SExpr::symbol(name.clone()), vars),
                Term::Match(_, cases) => Build::Match(cases),
                Term::Annotated(_, attributes) => Build::Annotated(attributes),
            };
            match build {
                Build::Application(q) => {
                    children.insert(0, q.to_sexpr());
                    SExpr::List(children)
                }
                Build::Let(bindings) => {
                    let body = children.pop().unwrap_or_else(|| SExpr::List(Vec::new()));
                    let bindings = bindings.iter().zip(children).map(|(b, t)| SExpr::List(vec![SExpr::symbol(b.variable.clone()), t])).collect();
                    SExpr::List(vec![SExpr::reserved(Reserved::Let), SExpr::List(bindings), body])
                }
                Build::Binder(head, vars) => {
                    let body = children.pop().unwrap_or_else(|| SExpr::List(Vec::new()));
                    SExpr::List(vec![head, sorted_vars(vars), body])
                }
                Build::Match(cases) => {
                    let mut children = children.into_iter();
                    let scrutinee = children.next().unwrap_or_else(|| SExpr::List(Vec::new()));
                    let cases = cases.iter().zip(children).map(|(c, t)| SExpr::List(vec![c.pattern.to_sexpr(), t])).collect();
                    SExpr::List(vec![SExpr::reserved(Reserved::Match), scrutinee, SExpr::List(cases)])
                }
                Build::Annotated(attributes) => {
                    let inner = children.pop().unwrap_or_else(|| SExpr::List(Vec::new()));
                    let mut items = vec![SExpr::reserved(Reserved::Bang), inner];
                    for attribute in attributes {
                        attribute.push_sexprs(&mut items);
                    }
                    SExpr::List(items)
                }
            }
        })
    }

    /// Writes this term in `dialect`.
    pub fn write<W: fmt::Write + ?Sized>(&self, out: &mut W, dialect: &Dialect) -> fmt::Result {
        self.to_sexpr().write(out, dialect)
    }

    /// The text of this term in `dialect`.
    pub fn to_text(&self, dialect: &Dialect) -> String {
        self.to_sexpr().to_text(dialect)
    }

    /// Reads a term from `text` in strict SMT-LIB 2.7.
    pub fn parse(text: &str) -> Result<Term> {
        Term::parse_in(text, &Dialect::strict())
    }

    /// Reads a term from `text` in `dialect`.
    pub fn parse_in(text: &str, dialect: &Dialect) -> Result<Term> {
        Term::from_spanned_in(&read_sexpr(text, dialect)?, dialect)
    }

    /// Reads a term in strict SMT-LIB 2.7.
    pub fn from_spanned(node: &Spanned) -> Result<Term> {
        Term::from_spanned_in(node, &Dialect::strict())
    }

    /// Reads a term in `dialect`: as [`Term::from_spanned`], and a list
    /// headed by a binder of the dialect is read as [`Term::Binder`].
    /// Iterative: the depth of the tree does not grow the call stack.
    pub fn from_spanned_in(node: &Spanned, dialect: &Dialect) -> Result<Term> {
        enum Kind {
            Lambda,
            Forall,
            Exists,
            Binder(Symbol),
        }
        enum Step<'a> {
            Visit(&'a Spanned),
            Application(QualIdentifier, usize),
            Let(Vec<Symbol>),
            Binder(Kind, NonEmpty<SortedVar>),
            Match(Vec<Pattern>),
            Annotated(NonEmpty<Attribute>),
        }
        let mut steps = vec![Step::Visit(node)];
        let mut values: Vec<Term> = Vec::new();
        let take = |values: &mut Vec<Term>, n: usize| values.split_off(values.len() - n);
        while let Some(step) = steps.pop() {
            let node = match step {
                Step::Visit(node) => node,
                Step::Application(function, n) => {
                    let args = take(&mut values, n);
                    values.push(Term::Application(function, NonEmpty(args)));
                    continue;
                }
                Step::Let(variables) => {
                    let mut terms = take(&mut values, variables.len() + 1);
                    let body = terms.pop().unwrap_or_else(|| unreachable!("the body was read"));
                    let bindings = variables.into_iter().zip(terms).map(|(variable, term)| VarBinding { variable, term }).collect();
                    values.push(Term::Let(NonEmpty(bindings), Box::new(body)));
                    continue;
                }
                Step::Binder(kind, vars) => {
                    let body = Box::new(values.pop().unwrap_or_else(|| unreachable!("the body was read")));
                    values.push(match kind {
                        Kind::Lambda => Term::Lambda(vars, body),
                        Kind::Forall => Term::Forall(vars, body),
                        Kind::Exists => Term::Exists(vars, body),
                        Kind::Binder(name) => Term::Binder(name, vars, body),
                    });
                    continue;
                }
                Step::Match(patterns) => {
                    let mut terms = take(&mut values, patterns.len() + 1).into_iter();
                    let scrutinee = terms.next().unwrap_or_else(|| unreachable!("the term was read"));
                    let cases = patterns.into_iter().zip(terms).map(|(pattern, term)| MatchCase { pattern, term }).collect();
                    values.push(Term::Match(Box::new(scrutinee), NonEmpty(cases)));
                    continue;
                }
                Step::Annotated(attributes) => {
                    let inner = values.pop().unwrap_or_else(|| unreachable!("the term was read"));
                    values.push(Term::Annotated(Box::new(inner), attributes));
                    continue;
                }
            };
            let items = match node.kind() {
                SpannedKind::Atom(Atom::Constant(c)) => {
                    values.push(Term::Constant(c.clone()));
                    continue;
                }
                SpannedKind::Atom(Atom::Symbol(s)) => {
                    values.push(Term::symbol(s.clone()));
                    continue;
                }
                SpannedKind::Atom(_) => return Err(node.expected("a term")),
                SpannedKind::List(items) => items,
            };
            let Some((head, rest)) = items.split_first() else {
                return Err(node.error("() is not a term"));
            };
            match head.as_reserved() {
                Some(Reserved::Underscore | Reserved::As) => values.push(Term::Identifier(QualIdentifier::from_spanned(node)?)),
                Some(Reserved::Let) => {
                    read::arity(node, rest, 2, "let")?;
                    let bindings = rest[0].expect_list("a list of variable bindings")?;
                    if bindings.is_empty() {
                        return Err(rest[0].error("let needs at least one binding (§3.6)"));
                    }
                    let mut variables = Vec::with_capacity(bindings.len());
                    let mut terms = Vec::with_capacity(bindings.len());
                    for binding in bindings {
                        match binding.as_list() {
                            Some([variable, term]) => {
                                variables.push(variable.expect_symbol("a variable")?.clone());
                                terms.push(term);
                            }
                            _ => return Err(binding.expected("a variable binding ( ⟨symbol⟩ ⟨term⟩ )")),
                        }
                    }
                    steps.push(Step::Let(variables));
                    steps.push(Step::Visit(&rest[1]));
                    steps.extend(terms.into_iter().rev().map(Step::Visit));
                }
                Some(binder @ (Reserved::Forall | Reserved::Exists | Reserved::Lambda)) => {
                    let vars = binder_variables(node, rest, binder.as_str())?;
                    let kind = match binder {
                        Reserved::Forall => Kind::Forall,
                        Reserved::Exists => Kind::Exists,
                        _ => Kind::Lambda,
                    };
                    steps.push(Step::Binder(kind, vars));
                    steps.push(Step::Visit(&rest[1]));
                }
                Some(Reserved::Match) => {
                    read::arity(node, rest, 2, "match")?;
                    let cases = rest[1].expect_list("a list of match cases")?;
                    if cases.is_empty() {
                        return Err(rest[1].error("match needs at least one case (§3.6)"));
                    }
                    let mut patterns = Vec::with_capacity(cases.len());
                    let mut terms = Vec::with_capacity(cases.len());
                    for case in cases {
                        match case.as_list() {
                            Some([pattern, term]) => {
                                patterns.push(Pattern::from_spanned(pattern)?);
                                terms.push(term);
                            }
                            _ => return Err(case.expected("a match case ( ⟨pattern⟩ ⟨term⟩ )")),
                        }
                    }
                    steps.push(Step::Match(patterns));
                    steps.extend(terms.into_iter().rev().map(Step::Visit));
                    steps.push(Step::Visit(&rest[0]));
                }
                Some(Reserved::Bang) => {
                    let Some((inner, attributes)) = rest.split_first() else {
                        return Err(node.error("! needs a term and at least one attribute (§3.6)"));
                    };
                    let attributes = NonEmpty::new(Attribute::sequence_from_spanned(attributes)?).ok_or_else(|| node.error("! needs at least one attribute (§3.6)"))?;
                    steps.push(Step::Annotated(attributes));
                    steps.push(Step::Visit(inner));
                }
                Some(other) => return Err(head.error(format!("the reserved word {other} cannot start a term"))),
                None => match head.as_symbol() {
                    Some(name) if dialect.is_binder(name) => {
                        let vars = binder_variables(node, rest, name.as_str())?;
                        steps.push(Step::Binder(Kind::Binder(name.clone()), vars));
                        steps.push(Step::Visit(&rest[1]));
                    }
                    _ => {
                        if head.as_constant().is_some() || head.as_keyword().is_some() {
                            return Err(head.expected("a function symbol (a qualified identifier)"));
                        }
                        let function = QualIdentifier::from_spanned(head)?;
                        if rest.is_empty() {
                            return Err(node.error(format!("({}) applies a function to no arguments; a constant is written without parentheses (§3.6)", head.describe())));
                        }
                        steps.push(Step::Application(function, rest.len()));
                        steps.extend(rest.iter().rev().map(Step::Visit));
                    }
                },
            }
        }
        values.pop().ok_or_else(|| node.expected("a term"))
    }

    /// Whether a subterm of this term has subterms itself.
    fn is_nested(&self) -> bool {
        self.children().any(|child| child.children().next().is_some())
    }

    /// Moves the immediate subterms of this term to `out`, leaving holes
    /// that allocate nothing: only for a term that is being dropped.
    fn take_children(&mut self, out: &mut Vec<Term>) {
        let hole = || Term::Constant(SpecConstant::Numeral(Numeral::hole()));
        match self {
            Term::Constant(_) | Term::Identifier(_) => {}
            Term::Application(_, args) => out.append(&mut args.0),
            Term::Let(bindings, body) => {
                out.extend(bindings.0.iter_mut().map(|b| std::mem::replace(&mut b.term, hole())));
                out.push(std::mem::replace(body.as_mut(), hole()));
            }
            Term::Lambda(_, body) | Term::Forall(_, body) | Term::Exists(_, body) | Term::Binder(_, _, body) | Term::Annotated(body, _) => out.push(std::mem::replace(body.as_mut(), hole())),
            Term::Match(term, cases) => {
                out.push(std::mem::replace(term.as_mut(), hole()));
                out.extend(cases.0.iter_mut().map(|c| std::mem::replace(&mut c.term, hole())));
            }
        }
    }
}

impl Drop for Term {
    fn drop(&mut self) {
        if !self.is_nested() {
            return;
        }
        let mut pending = Vec::new();
        self.take_children(&mut pending);
        while let Some(mut term) = pending.pop() {
            term.take_children(&mut pending);
        }
    }
}

/// The variables of `(binder ( ⟨sorted_var⟩+ ) ⟨term⟩ )`.
fn binder_variables(node: &Spanned, rest: &[Spanned], binder: &str) -> Result<NonEmpty<SortedVar>> {
    read::arity(node, rest, 2, binder)?;
    let vars = rest[0].expect_list("a list of sorted variables")?.iter().map(SortedVar::from_spanned).collect::<Result<Vec<_>>>()?;
    NonEmpty::new(vars).ok_or_else(|| rest[0].error(format!("{binder} needs at least one variable (§3.6)")))
}

impl fmt::Display for Term {
    /// The text of the term in strict SMT-LIB 2.7.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write(f, &Dialect::strict())
    }
}

impl std::str::FromStr for Term {
    type Err = Error;

    /// Reads a term in strict SMT-LIB 2.7.
    fn from_str(text: &str) -> Result<Term> {
        Term::parse(text)
    }
}

impl ExtendedConstant {
    /// The SMT-LIB term the literal abbreviates: `-n` is `(- n)`, `-d` is
    /// `(- d)`, `n/m` is `(/ n m)` and `-n/m` is `(- (/ n m))`, the forms of
    /// the `:values` of Reals and of the rational coefficients of the
    /// linear real arithmetic logics. The strict printer writes this term
    /// for the literal.
    pub fn expansion(&self) -> Term {
        let operator = |name: &str| QualIdentifier::plain(Identifier::simple(Symbol::new(name).unwrap_or_else(|_| unreachable!("{name} is a symbol"))));
        let negate = |t: Term| Term::Application(operator("-"), NonEmpty::one(t));
        let numeral = |n: &Numeral| Term::Constant(SpecConstant::Numeral(n.clone()));
        match self {
            ExtendedConstant::NegativeNumeral(n) => negate(numeral(n)),
            ExtendedConstant::NegativeDecimal(d) => negate(Term::Constant(SpecConstant::Decimal(d.clone()))),
            ExtendedConstant::Fraction { negative, numerator, denominator } => {
                let quotient = Term::Application(operator("/"), NonEmpty(vec![numeral(numerator), numeral(denominator)]));
                if *negative {
                    negate(quotient)
                } else {
                    quotient
                }
            }
        }
    }
}
