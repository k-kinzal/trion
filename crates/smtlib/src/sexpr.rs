//! S-expressions (§3.2), the generic tree every SMT-LIB category specializes.
//!
//! `⟨s_expr⟩ ::= ⟨spec_constant⟩ | ⟨symbol⟩ | ⟨reserved⟩ | ⟨keyword⟩ | ( ⟨s_expr⟩* )`
//!
//! [`SExpr`] is the tree without positions; it is the value that equality,
//! printing and the attribute values of §3.4 use. [`Spanned`] is the same
//! tree with the position of every node, which the readers of this crate
//! (and of formats built on S-expressions, such as Alethe and MoXI) use to
//! report errors at a line and column; its `expect_*` methods are the
//! reading helpers those readers share. [`read`] and [`read_all`] turn text
//! into spanned trees under a [`Dialect`]; [`SExpr::write`] prints a tree so
//! that reading it back gives the same tree.
//!
//! Reading, printing, converting and dropping are iterative: a tree as
//! deep as memory allows is printed and dropped without growing the stack.
//! The reader refuses text nested deeper than [`Dialect::max_depth`].
//!
//! ```
//! use smtlib::sexpr::{read, SExpr};
//! use smtlib::Dialect;
//!
//! let node = read("(a (b \"c\") :k)", &Dialect::strict()).unwrap();
//! assert_eq!(node.expect_list("a list").unwrap().len(), 3);
//! assert_eq!(node.to_sexpr().to_string(), "(a (b \"c\") :k)");
//! ```

use crate::error::{Error, ErrorKind, Position, Result};
use crate::lexicon::{tokenize, Dialect, Keyword, Numeral, Reserved, SpecConstant, StringLiteral, Symbol, Token, TokenKind};
use std::fmt;

/// A non-parenthesis token of §3.2.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Atom {
    /// A special constant.
    Constant(SpecConstant),
    /// A symbol.
    Symbol(Symbol),
    /// A reserved word.
    Reserved(Reserved),
    /// A keyword.
    Keyword(Keyword),
}

impl Atom {
    /// Writes the token that denotes this atom in `dialect`. An extended
    /// literal ([`SpecConstant::Extended`]) in a dialect without extended
    /// literals is written as the SMT-LIB term it abbreviates
    /// ([`crate::ExtendedConstant::expansion`]).
    pub fn write<W: fmt::Write + ?Sized>(&self, out: &mut W, dialect: &Dialect) -> fmt::Result {
        match self {
            Atom::Constant(SpecConstant::Extended(e)) if !dialect.has_extended_literals() => e.expansion().to_sexpr().write(out, dialect),
            Atom::Constant(c) => write!(out, "{c}"),
            Atom::Symbol(s) if dialect.quotes(s) => write!(out, "|{}|", s.as_str()),
            Atom::Symbol(s) => out.write_str(s.as_str()),
            Atom::Reserved(r) => out.write_str(r.as_str()),
            Atom::Keyword(k) => write!(out, "{k}"),
        }
    }

    /// The token that denotes this atom in `dialect`.
    pub fn to_text(&self, dialect: &Dialect) -> String {
        let mut out = String::new();
        let _ = self.write(&mut out, dialect);
        out
    }
}

/// An S-expression (§3.2) without positions.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SExpr {
    /// A non-parenthesis token.
    Atom(Atom),
    /// A possibly empty parenthesized sequence.
    List(Vec<SExpr>),
}

impl SExpr {
    /// The atom for a symbol.
    pub fn symbol(symbol: Symbol) -> SExpr {
        SExpr::Atom(Atom::Symbol(symbol))
    }

    /// The atom for a reserved word.
    pub fn reserved(reserved: Reserved) -> SExpr {
        SExpr::Atom(Atom::Reserved(reserved))
    }

    /// The atom for a keyword.
    pub fn keyword(keyword: Keyword) -> SExpr {
        SExpr::Atom(Atom::Keyword(keyword))
    }

    /// The atom for a special constant.
    pub fn constant(constant: SpecConstant) -> SExpr {
        SExpr::Atom(Atom::Constant(constant))
    }

    /// The items, if this is a list.
    pub fn as_list(&self) -> Option<&[SExpr]> {
        match self {
            SExpr::List(items) => Some(items),
            SExpr::Atom(_) => None,
        }
    }

    /// The items, if this is a list; this value otherwise. (`SExpr`
    /// implements [`Drop`], so a list cannot be taken apart by a pattern.)
    pub fn into_list(mut self) -> std::result::Result<Vec<SExpr>, SExpr> {
        match &mut self {
            SExpr::List(items) => Ok(std::mem::take(items)),
            SExpr::Atom(_) => Err(self),
        }
    }

    /// Writes this S-expression in `dialect`: atoms separated by one space,
    /// lists in parentheses, on one line.
    pub fn write<W: fmt::Write + ?Sized>(&self, out: &mut W, dialect: &Dialect) -> fmt::Result {
        enum Step<'a> {
            Expr(&'a SExpr),
            Space,
            Close,
        }
        let mut steps = vec![Step::Expr(self)];
        while let Some(step) = steps.pop() {
            match step {
                Step::Space => out.write_char(' ')?,
                Step::Close => out.write_char(')')?,
                Step::Expr(SExpr::Atom(atom)) => atom.write(out, dialect)?,
                Step::Expr(SExpr::List(items)) => {
                    out.write_char('(')?;
                    steps.push(Step::Close);
                    for (i, item) in items.iter().enumerate().rev() {
                        steps.push(Step::Expr(item));
                        if i > 0 {
                            steps.push(Step::Space);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// The text of this S-expression in `dialect`, on one line.
    pub fn to_text(&self, dialect: &Dialect) -> String {
        let mut out = String::new();
        let _ = self.write(&mut out, dialect);
        out
    }

    /// This tree with every node at `position`, for readers that work on
    /// spanned trees.
    pub fn to_spanned(&self, position: Position) -> Spanned {
        enum Step<'a> {
            Visit(&'a SExpr),
            Build(usize),
        }
        let mut steps = vec![Step::Visit(self)];
        let mut values: Vec<Spanned> = Vec::new();
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(SExpr::Atom(atom)) => values.push(Spanned::new(position, SpannedKind::Atom(atom.clone()))),
                Step::Visit(SExpr::List(items)) => {
                    steps.push(Step::Build(items.len()));
                    steps.extend(items.iter().rev().map(Step::Visit));
                }
                Step::Build(n) => {
                    let items = values.split_off(values.len() - n);
                    values.push(Spanned::new(position, SpannedKind::List(items)));
                }
            }
        }
        values.pop().unwrap_or_else(|| Spanned::new(position, SpannedKind::List(Vec::new())))
    }
}

impl Drop for SExpr {
    fn drop(&mut self) {
        let SExpr::List(items) = self else { return };
        if items.iter().all(|i| matches!(i, SExpr::Atom(_))) {
            return;
        }
        let mut pending = std::mem::take(items);
        while let Some(mut item) = pending.pop() {
            if let SExpr::List(inner) = &mut item {
                pending.append(inner);
            }
        }
    }
}

impl fmt::Display for SExpr {
    /// The text of the S-expression in strict SMT-LIB 2.7.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write(f, &Dialect::strict())
    }
}

impl std::str::FromStr for SExpr {
    type Err = Error;

    /// Reads exactly one S-expression in strict SMT-LIB 2.7.
    fn from_str(text: &str) -> Result<SExpr> {
        Ok(read(text, &Dialect::strict())?.to_sexpr())
    }
}

/// An S-expression with the position where each node starts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned {
    position: Position,
    kind: SpannedKind,
}

/// A node of a [`Spanned`] tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpannedKind {
    /// A non-parenthesis token.
    Atom(Atom),
    /// A parenthesized sequence.
    List(Vec<Spanned>),
}

impl Spanned {
    /// The node `kind` at `position`.
    pub fn new(position: Position, kind: SpannedKind) -> Spanned {
        Spanned { position, kind }
    }

    /// Where this node starts.
    pub fn position(&self) -> Position {
        self.position
    }

    /// The node.
    pub fn kind(&self) -> &SpannedKind {
        &self.kind
    }

    /// The tree without positions.
    pub fn to_sexpr(&self) -> SExpr {
        enum Step<'a> {
            Visit(&'a Spanned),
            Build(usize),
        }
        let mut steps = vec![Step::Visit(self)];
        let mut values: Vec<SExpr> = Vec::new();
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(node) => match &node.kind {
                    SpannedKind::Atom(atom) => values.push(SExpr::Atom(atom.clone())),
                    SpannedKind::List(items) => {
                        steps.push(Step::Build(items.len()));
                        steps.extend(items.iter().rev().map(Step::Visit));
                    }
                },
                Step::Build(n) => {
                    let items = values.split_off(values.len() - n);
                    values.push(SExpr::List(items));
                }
            }
        }
        values.pop().unwrap_or_else(|| SExpr::List(Vec::new()))
    }

    /// The items, if this node is a list.
    pub fn as_list(&self) -> Option<&[Spanned]> {
        match &self.kind {
            SpannedKind::List(items) => Some(items),
            SpannedKind::Atom(_) => None,
        }
    }

    /// The atom, if this node is one.
    pub fn as_atom(&self) -> Option<&Atom> {
        match &self.kind {
            SpannedKind::Atom(atom) => Some(atom),
            SpannedKind::List(_) => None,
        }
    }

    /// The symbol, if this node is one.
    pub fn as_symbol(&self) -> Option<&Symbol> {
        match self.as_atom() {
            Some(Atom::Symbol(s)) => Some(s),
            _ => None,
        }
    }

    /// The keyword, if this node is one.
    pub fn as_keyword(&self) -> Option<&Keyword> {
        match self.as_atom() {
            Some(Atom::Keyword(k)) => Some(k),
            _ => None,
        }
    }

    /// The reserved word, if this node is one.
    pub fn as_reserved(&self) -> Option<Reserved> {
        match self.as_atom() {
            Some(Atom::Reserved(r)) => Some(*r),
            _ => None,
        }
    }

    /// Whether this node is the reserved word `reserved`.
    pub fn is_reserved(&self, reserved: Reserved) -> bool {
        self.as_reserved() == Some(reserved)
    }

    /// The special constant, if this node is one.
    pub fn as_constant(&self) -> Option<&SpecConstant> {
        match self.as_atom() {
            Some(Atom::Constant(c)) => Some(c),
            _ => None,
        }
    }

    /// The items after the head, if this node is a list whose first item is
    /// the reserved word `head`.
    pub fn headed(&self, head: Reserved) -> Option<&[Spanned]> {
        match self.as_list() {
            Some([first, rest @ ..]) if first.is_reserved(head) => Some(rest),
            _ => None,
        }
    }

    /// Writes this node in `dialect`, as [`SExpr::write`] writes the tree
    /// without positions.
    pub fn write<W: fmt::Write + ?Sized>(&self, out: &mut W, dialect: &Dialect) -> fmt::Result {
        enum Step<'a> {
            Node(&'a Spanned),
            Space,
            Close,
        }
        let mut steps = vec![Step::Node(self)];
        while let Some(step) = steps.pop() {
            match step {
                Step::Space => out.write_char(' ')?,
                Step::Close => out.write_char(')')?,
                Step::Node(node) => match &node.kind {
                    SpannedKind::Atom(atom) => atom.write(out, dialect)?,
                    SpannedKind::List(items) => {
                        out.write_char('(')?;
                        steps.push(Step::Close);
                        for (i, item) in items.iter().enumerate().rev() {
                            steps.push(Step::Node(item));
                            if i > 0 {
                                steps.push(Step::Space);
                            }
                        }
                    }
                },
            }
        }
        Ok(())
    }

    /// The text of this node, for error messages: the S-expression in
    /// strict SMT-LIB, cut to 57 characters and `...` when it is longer
    /// than 60 (the rest is not printed).
    pub fn describe(&self) -> String {
        const LIMIT: usize = 60;
        struct Bounded {
            text: String,
            chars: usize,
        }
        impl fmt::Write for Bounded {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                for c in s.chars() {
                    if self.chars == LIMIT {
                        return Err(fmt::Error);
                    }
                    self.text.push(c);
                    self.chars += 1;
                }
                Ok(())
            }
        }
        let mut out = Bounded { text: String::new(), chars: 0 };
        if self.write(&mut out, &Dialect::strict()).is_err() {
            let cut: String = out.text.chars().take(LIMIT - 3).collect();
            return format!("{cut}...");
        }
        out.text
    }

    /// A syntax error at this node.
    pub fn error(&self, message: impl Into<String>) -> Error {
        Error::at(ErrorKind::Syntax, self.position, message)
    }

    /// The syntax error "expected `what`, found …" at this node.
    pub fn expected(&self, what: &str) -> Error {
        self.error(format!("expected {what}, found {}", self.describe()))
    }

    /// The items of this node, or the error "expected `what`".
    pub fn expect_list(&self, what: &str) -> Result<&[Spanned]> {
        self.as_list().ok_or_else(|| self.expected(what))
    }

    /// The symbol of this node, or the error "expected `what`".
    pub fn expect_symbol(&self, what: &str) -> Result<&Symbol> {
        self.as_symbol().ok_or_else(|| self.expected(what))
    }

    /// The keyword of this node, or the error "expected `what`".
    pub fn expect_keyword(&self, what: &str) -> Result<&Keyword> {
        self.as_keyword().ok_or_else(|| self.expected(what))
    }

    /// The numeral of this node, or the error "expected `what`".
    pub fn expect_numeral(&self, what: &str) -> Result<&Numeral> {
        match self.as_constant() {
            Some(SpecConstant::Numeral(n)) => Ok(n),
            _ => Err(self.expected(what)),
        }
    }

    /// The string literal of this node, or the error "expected `what`".
    pub fn expect_string(&self, what: &str) -> Result<&StringLiteral> {
        match self.as_constant() {
            Some(SpecConstant::String(s)) => Ok(s),
            _ => Err(self.expected(what)),
        }
    }
}

impl Drop for Spanned {
    fn drop(&mut self) {
        let SpannedKind::List(items) = &mut self.kind else { return };
        if items.iter().all(|i| matches!(i.kind, SpannedKind::Atom(_))) {
            return;
        }
        let mut pending = std::mem::take(items);
        while let Some(mut item) = pending.pop() {
            if let SpannedKind::List(inner) = &mut item.kind {
                pending.append(inner);
            }
        }
    }
}

/// Reads every S-expression of `text` in `dialect`.
pub fn read_all(text: &str, dialect: &Dialect) -> Result<Vec<Spanned>> {
    let tokens = tokenize(text, dialect)?;
    let mut reader = Reader { tokens: &tokens, index: 0, max_depth: dialect.max_depth() };
    let mut out = Vec::new();
    while reader.index < tokens.len() {
        out.push(reader.expr()?);
    }
    Ok(out)
}

/// Reads exactly one S-expression from `text` in `dialect`.
pub fn read(text: &str, dialect: &Dialect) -> Result<Spanned> {
    let mut all = read_all(text, dialect)?;
    match all.len() {
        1 => Ok(all.remove(0)),
        0 => Err(Error::at(ErrorKind::Syntax, Position::START.advance(text), "expected an S-expression, found the end of the text")),
        _ => Err(Error::at(ErrorKind::Syntax, all[1].position, "expected one S-expression, found more")),
    }
}

struct Reader<'a> {
    tokens: &'a [Token],
    index: usize,
    max_depth: usize,
}

impl Reader<'_> {
    /// The next S-expression: the open lists are kept on a stack, so that
    /// the depth of the text does not grow the call stack.
    fn expr(&mut self) -> Result<Spanned> {
        let mut open: Vec<(Position, Vec<Spanned>)> = Vec::new();
        loop {
            let Some(token) = self.tokens.get(self.index) else {
                let position = open.last().map_or(Position::START, |(p, _)| *p);
                return Err(Error::at(ErrorKind::Syntax, position, "unbalanced (: the text ends before the matching )"));
            };
            self.index += 1;
            let position = token.position;
            let node = match &token.kind {
                TokenKind::Open => {
                    if open.len() >= self.max_depth {
                        return Err(Error::at(ErrorKind::Depth, position, format!("the text nests parentheses deeper than {}, the limit of the reader", self.max_depth)));
                    }
                    open.push((position, Vec::new()));
                    continue;
                }
                TokenKind::Close => match open.pop() {
                    Some((start, items)) => Spanned::new(start, SpannedKind::List(items)),
                    None => return Err(Error::at(ErrorKind::Syntax, position, "unexpected )")),
                },
                TokenKind::Constant(c) => Spanned::new(position, SpannedKind::Atom(Atom::Constant(c.clone()))),
                TokenKind::Symbol(s) => Spanned::new(position, SpannedKind::Atom(Atom::Symbol(s.clone()))),
                TokenKind::Keyword(k) => Spanned::new(position, SpannedKind::Atom(Atom::Keyword(k.clone()))),
                TokenKind::Reserved(r) => Spanned::new(position, SpannedKind::Atom(Atom::Reserved(*r))),
            };
            match open.last_mut() {
                Some((_, items)) => items.push(node),
                None => return Ok(node),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_and_prints_back() {
        let text = "(a (b \"c\"\"d\") :k |x y| 0 1.5 #x0F #b01 ())";
        let tree = read(text, &Dialect::strict()).unwrap().to_sexpr();
        assert_eq!(tree.to_string(), text);
    }

    #[test]
    fn unbalanced_parentheses_are_errors() {
        assert_eq!(read("(a", &Dialect::strict()).unwrap_err().kind(), ErrorKind::Syntax);
        assert_eq!(read("a)", &Dialect::strict()).unwrap_err().kind(), ErrorKind::Syntax);
    }

    #[test]
    fn depth_is_limited() {
        let deep = "(".repeat(20) + &")".repeat(20);
        let error = read(&deep, &Dialect::strict().with_max_depth(10)).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::Depth);
        assert_eq!(error.position(), Some(Position::new(1, 11)));
        assert!(read(&deep, &Dialect::strict().with_max_depth(20)).is_ok());
    }

    #[test]
    fn describe_cuts_without_printing_everything() {
        let long = format!("({})", "a ".repeat(1000));
        let node = read(&long, &Dialect::strict()).unwrap();
        let text = node.describe();
        assert_eq!(text.chars().count(), 60);
        assert!(text.ends_with("..."));
        assert_eq!(read("(a b)", &Dialect::strict()).unwrap().describe(), "(a b)");
    }
}
