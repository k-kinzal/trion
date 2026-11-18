//! The parser: text to abstract syntax, following the grammar "Full syntax
//! for Eunoia commands" of the Ethos user manual and, where the manual leaves
//! the reading open, Ethos `src/cmd_parser.cpp` and `src/expr_parser.cpp`.
//!
//! Terms are read with an explicit stack, as Ethos reads them
//! (`ExprParser::parseExpr`), so a term of any depth that fits in memory is read
//! without exhausting the call stack.
//!
//! The parser is context free: it reads every script with the same grammar
//! and does not consult declarations. Ethos instead reads a variable list
//! after the head of an application only when the head is declared with
//! `:binder`; here a first argument that begins with `((` and is not a
//! qualified head `((_ ...` or `((as ...` is read as a variable list wherever
//! it occurs. Whether the head is a binder depends on its declaration, which
//! this crate does not read; Ethos refuses a variable list after any other
//! head. Every script Ethos reads is read here to the same commands.
//!
//! Refused as unsupported (Ethos reads them, this crate does not):
//! - a quoted symbol whose content is `Bool`, `Type`, `!`, `let`, `par` or
//!   `eo::define`: Ethos reads the unquoted words as builtin tokens and the
//!   quoted ones as user symbols, a distinction the abstract syntax does not
//!   keep;
//! - the negative literals `-.5` and `-/5` without digits before the point,
//!   which Ethos's lexer classifies as literals.
//!
//! Stricter than Ethos (both are outside the manual's grammar): text after
//! `(exit)` must still be a well-formed script, and a step accepts no keyword
//! besides `:rule`, `:premises` and `:args`. `set-option` follows the manual,
//! `(set-option <keyword> <term>?)`; Ethos reads an arbitrary s-expression after
//! the keyword (`CmdParser::parseNextCommand`, `SET_OPTION`).

use crate::ast::*;
use crate::error::{AstError, AstErrorKind, Found, LiteralProblem, ParseError, ParseErrorKind, Position, SyntaxProblem, UnsupportedConstruct};
use crate::lexer::{tokenize_from, Tok, Token};

/// Parses a whole script.
///
/// ```
/// let script = eunoia::parse_script("(declare-const a Bool) (assume @p0 a)")?;
/// assert_eq!(script.len(), 2);
/// assert_eq!(script.to_string(), "(declare-const a Bool)\n(assume @p0 a)\n");
/// # Ok::<(), eunoia::ParseError>(())
/// ```
pub fn parse_script(text: &str) -> Result<Script, ParseError> {
    parse_script_at(text, Position::START)
}

/// Parses a script that is a part of a larger text, beginning at `start` in
/// it: positions, in errors and in the script, are positions in the larger
/// text. A reader of a larger format (a solver's output that holds proofs, for
/// instance) passes each part with its position, without copying or
/// re-reading the rest.
///
/// ```
/// use eunoia::Position;
/// let output = "unsat\n(assume @p0 false)";
/// let script = eunoia::parse_script_at(&output[6..], Position::new(2, 1))?;
/// assert_eq!(script.position(0), Some(Position::new(2, 1)));
/// # Ok::<(), eunoia::ParseError>(())
/// ```
pub fn parse_script_at(text: &str, start: Position) -> Result<Script, ParseError> {
    let mut p = Parser::new(text, start)?;
    let mut commands = Vec::new();
    let mut positions = Vec::new();
    while p.peek().is_some() {
        positions.push(Some(p.position()));
        commands.push(p.command()?);
    }
    Ok(Script::with_positions(commands, positions))
}

/// Parses one term that makes up the whole text.
///
/// ```
/// let t = eunoia::parse_term("(or a (not b))")?;
/// assert_eq!(t.depth(), 3);
/// # Ok::<(), eunoia::ParseError>(())
/// ```
pub fn parse_term(text: &str) -> Result<Term, ParseError> {
    let mut p = Parser::new(text, Position::START)?;
    let t = p.term()?;
    if let Some(tok) = p.peek() {
        return Err(p.unexpected("the end of the term", tok.clone()));
    }
    Ok(t)
}

struct Parser {
    toks: Vec<Token>,
    at: usize,
    /// Where the text ends.
    end: Position,
}

const UNSUPPORTED_QUOTED: [&str; 6] = ["Bool", "Type", "!", "let", "par", "eo::define"];

/// Where an application is in its reading.
enum AppMode {
    /// Right after the head: a variable list may follow.
    Start,
    /// In the variable list of the binder (the head), with the variables read
    /// so far; the last is `Some` while the type of that variable is read.
    Vars(Symbol, Vec<(Symbol, Term)>, Option<Symbol>),
    /// In the arguments.
    Args,
}

/// A parenthesized term being read.
enum Frame {
    /// `(head ...)`: `head` is `None` while a qualified head `(_ ...)` is read.
    /// `binder` is the head with the variable list once one has been read;
    /// `head` is the head otherwise.
    App { pos: Position, head: Option<Term>, mode: AppMode, binder: Option<(Symbol, Vec<(Symbol, Term)>)>, args: Vec<Term> },
    /// `(let (...) body)`; `pending` is the variable whose value is read,
    /// `body_next` is set after the bindings.
    Let { form: LetForm, bindings: Vec<(Symbol, Term)>, pending: Option<Symbol>, body_next: bool },
    /// `(! term attr...)`; `term` is `None` while the term is read, `pending`
    /// the keyword whose value is read.
    Annot { term: Option<Term>, attributes: Vec<Attribute>, pending: Option<Keyword> },
}

/// What a frame needs next.
enum Need {
    Term,
    Done(Term),
}

impl Parser {
    fn new(text: &str, start: Position) -> Result<Parser, ParseError> {
        let (toks, end) = tokenize_from(text, start)?;
        Ok(Parser { toks, at: 0, end })
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.at).map(|t| &t.tok)
    }

    fn peek_at(&self, k: usize) -> Option<&Tok> {
        self.toks.get(self.at + k).map(|t| &t.tok)
    }

    fn position(&self) -> Position {
        match self.toks.get(self.at) {
            Some(t) => t.pos,
            None => self.end,
        }
    }

    fn error(&self, kind: ParseErrorKind) -> ParseError {
        ParseError::new(self.position(), kind)
    }

    fn unexpected(&self, expected: &'static str, found: Tok) -> ParseError {
        self.error(ParseErrorKind::UnexpectedToken { expected, found: found.describe() })
    }

    fn next(&mut self, expected: &'static str) -> Result<Tok, ParseError> {
        match self.toks.get(self.at) {
            Some(t) => {
                self.at += 1;
                Ok(t.tok.clone())
            }
            None => Err(self.error(ParseErrorKind::UnexpectedEnd { expected })),
        }
    }

    fn expect(&mut self, want: Tok, expected: &'static str) -> Result<(), ParseError> {
        let pos = self.position();
        let tok = self.next(expected)?;
        if tok == want {
            Ok(())
        } else {
            Err(ParseError::new(pos, ParseErrorKind::UnexpectedToken { expected, found: tok.describe() }))
        }
    }

    fn lparen(&mut self) -> Result<(), ParseError> {
        self.expect(Tok::LParen, "`(`")
    }

    fn rparen(&mut self) -> Result<(), ParseError> {
        self.expect(Tok::RParen, "`)`")
    }

    fn eat(&mut self, want: &Tok) -> bool {
        if self.peek() == Some(want) {
            self.at += 1;
            true
        } else {
            false
        }
    }

    fn symbol(&mut self) -> Result<Symbol, ParseError> {
        let pos = self.position();
        match self.next("a symbol")? {
            Tok::Symbol(s) => Ok(Symbol::unchecked(s)),
            Tok::Quoted(s) => quoted_symbol(s, pos),
            other => Err(ParseError::new(pos, ParseErrorKind::UnexpectedToken { expected: "a symbol", found: other.describe() })),
        }
    }

    fn keyword(&mut self) -> Result<Keyword, ParseError> {
        let pos = self.position();
        match self.next("a keyword")? {
            Tok::Keyword(k) => Ok(Keyword::unchecked(k)),
            other => Err(ParseError::new(pos, ParseErrorKind::UnexpectedToken { expected: "a keyword", found: other.describe() })),
        }
    }

    fn string(&mut self) -> Result<StrLit, ParseError> {
        let pos = self.position();
        match self.next("a string literal")? {
            Tok::Str(s) => StrLit::new(s).map_err(|_| ParseError::new(pos, ParseErrorKind::InvalidLiteral(LiteralProblem::NonAsciiString))),
            other => Err(ParseError::new(pos, ParseErrorKind::UnexpectedToken { expected: "a string literal", found: other.describe() })),
        }
    }

    /// A numeral that fits in 32 bits and has no leading zero
    /// (Ethos `ExprParser::tokenStrToUnsigned`).
    fn small_numeral(&mut self) -> Result<u32, ParseError> {
        let pos = self.position();
        match self.next("a numeral")? {
            Tok::Numeral(s) if !s.starts_with('-') => {
                if s.len() > 1 && s.starts_with('0') {
                    return Err(ParseError::new(pos, ParseErrorKind::InvalidLiteral(LiteralProblem::LeadingZero)));
                }
                s.parse::<u32>().map_err(|_| ParseError::new(pos, ParseErrorKind::InvalidLiteral(LiteralProblem::TooLarge)))
            }
            other => Err(ParseError::new(pos, ParseErrorKind::UnexpectedToken { expected: "a numeral", found: other.describe() })),
        }
    }

    fn literal(category: LiteralCategory, text: String, pos: Position) -> Result<Term, ParseError> {
        if matches!(category, LiteralCategory::Decimal | LiteralCategory::Rational) && (text.starts_with("-.") || text.starts_with("-/")) {
            return Err(ParseError::new(pos, ParseErrorKind::Unsupported(UnsupportedConstruct::LiteralWithoutLeadingDigits(text))));
        }
        Literal::new(category, text).map(Term::Literal).map_err(|e| {
            let kind = match e.kind() {
                AstErrorKind::ZeroDenominator => ParseErrorKind::InvalidLiteral(LiteralProblem::ZeroDenominator),
                AstErrorKind::NonAsciiString => ParseErrorKind::InvalidLiteral(LiteralProblem::NonAsciiString),
                other => ParseErrorKind::Syntax(SyntaxProblem::Invalid(other)),
            };
            ParseError::new(pos, kind)
        })
    }

    /// Reads a term with an explicit stack of the parenthesized terms open.
    fn term(&mut self) -> Result<Term, ParseError> {
        let mut stack: Vec<Frame> = Vec::new();
        loop {
            let mut value = self.begin(&mut stack)?;
            loop {
                let Some(top) = stack.last_mut() else {
                    match value {
                        Some(t) => return Ok(t),
                        None => break,
                    }
                };
                match self.advance(top, value.take())? {
                    Need::Term => break,
                    Need::Done(t) => {
                        stack.pop();
                        value = Some(t);
                    }
                }
            }
        }
    }

    /// Begins a term: an atom is returned, a parenthesized term is pushed.
    fn begin(&mut self, stack: &mut Vec<Frame>) -> Result<Option<Term>, ParseError> {
        let pos = self.position();
        let atom = match self.next("a term")? {
            Tok::Symbol(s) => Term::Symbol(Symbol::unchecked(s)),
            Tok::Quoted(s) => Term::Symbol(quoted_symbol(s, pos)?),
            Tok::Numeral(s) => Parser::literal(LiteralCategory::Numeral, s, pos)?,
            Tok::Decimal(s) => Parser::literal(LiteralCategory::Decimal, s, pos)?,
            Tok::Rational(s) => Parser::literal(LiteralCategory::Rational, s, pos)?,
            Tok::Binary(s) => Parser::literal(LiteralCategory::Binary, s, pos)?,
            Tok::Hexadecimal(s) => Parser::literal(LiteralCategory::Hexadecimal, s, pos)?,
            Tok::Str(s) => Parser::literal(LiteralCategory::String, s, pos)?,
            Tok::LParen => {
                self.open(pos, stack)?;
                return Ok(None);
            }
            other => return Err(ParseError::new(pos, ParseErrorKind::UnexpectedToken { expected: "a term", found: other.describe() })),
        };
        Ok(Some(atom))
    }

    /// Pushes the frame of a parenthesized term, after its `(`.
    fn open(&mut self, pos: Position, stack: &mut Vec<Frame>) -> Result<(), ParseError> {
        let hpos = self.position();
        match self.next("an operator")? {
            Tok::Reserved("let") => {
                self.lparen()?;
                stack.push(Frame::Let { form: LetForm::Let, bindings: Vec::new(), pending: None, body_next: false });
            }
            Tok::Reserved("eo::define") => {
                self.lparen()?;
                stack.push(Frame::Let { form: LetForm::EoDefine, bindings: Vec::new(), pending: None, body_next: false });
            }
            Tok::Reserved("!") => {
                if self.peek() == Some(&Tok::RParen) {
                    return Err(self.error(ParseErrorKind::Syntax(SyntaxProblem::AnnotationWithoutTerm)));
                }
                stack.push(Frame::Annot { term: None, attributes: Vec::new(), pending: None });
            }
            Tok::RParen => return Err(ParseError::new(pos, ParseErrorKind::Syntax(SyntaxProblem::MissingHead))),
            Tok::LParen => {
                // ((_ ...) args) or ((as ...) args): a qualified head.
                let qpos = self.position();
                let head = self.symbol()?;
                if head.as_str() != "_" && head.as_str() != "as" {
                    return Err(ParseError::new(qpos, ParseErrorKind::Syntax(SyntaxProblem::QualifierHead)));
                }
                stack.push(Frame::App { pos, head: None, mode: AppMode::Args, binder: None, args: Vec::new() });
                stack.push(Frame::App { pos: hpos, head: Some(Term::Symbol(head)), mode: AppMode::Start, binder: None, args: Vec::new() });
            }
            Tok::Symbol(s) => {
                stack.push(Frame::App { pos, head: Some(Term::Symbol(Symbol::unchecked(s))), mode: AppMode::Start, binder: None, args: Vec::new() });
            }
            Tok::Quoted(s) => {
                let head = quoted_symbol(s, hpos)?;
                stack.push(Frame::App { pos, head: Some(Term::Symbol(head)), mode: AppMode::Start, binder: None, args: Vec::new() });
            }
            other => return Err(ParseError::new(hpos, ParseErrorKind::UnexpectedToken { expected: "an operator", found: other.describe() })),
        }
        Ok(())
    }

    /// Gives a frame the term just read, if any, and reads its structural
    /// tokens up to the next term it needs or its `)`.
    fn advance(&mut self, frame: &mut Frame, value: Option<Term>) -> Result<Need, ParseError> {
        match frame {
            Frame::App { pos, head, mode, binder, args } => {
                if let Some(v) = value {
                    match mode {
                        AppMode::Vars(_, vars, pending) => {
                            let Some(x) = pending.take() else { return Err(self.error(ParseErrorKind::Syntax(SyntaxProblem::VariablePair))) };
                            vars.push((x, v));
                            self.rparen()?;
                        }
                        _ if head.is_none() && binder.is_none() => *head = Some(v),
                        _ => args.push(v),
                    }
                }
                if matches!(mode, AppMode::Start) {
                    let starts_var_list = self.peek() == Some(&Tok::LParen) && self.peek_at(1) == Some(&Tok::LParen) && !matches!(self.peek_at(2), Some(Tok::Symbol(s)) | Some(Tok::Quoted(s)) if s == "_" || s == "as");
                    *mode = AppMode::Args;
                    if starts_var_list {
                        match head.take() {
                            Some(Term::Symbol(h)) => {
                                self.lparen()?;
                                *mode = AppMode::Vars(h, Vec::new(), None);
                            }
                            other => *head = other,
                        }
                    }
                }
                if let AppMode::Vars(_, _, pending) = mode {
                    if self.eat(&Tok::LParen) {
                        *pending = Some(self.symbol()?);
                        if self.peek() == Some(&Tok::RParen) {
                            return Err(self.error(ParseErrorKind::Syntax(SyntaxProblem::VariablePair)));
                        }
                        return Ok(Need::Term);
                    }
                    self.rparen()?;
                    if let AppMode::Vars(h, vars, _) = std::mem::replace(mode, AppMode::Args) {
                        *binder = Some((h, vars));
                    }
                }
                if !self.eat(&Tok::RParen) {
                    return Ok(Need::Term);
                }
                let at = *pos;
                let syntax = |e: AstError| ParseError::new(at, ParseErrorKind::Syntax(SyntaxProblem::Invalid(e.kind())));
                let args = std::mem::take(args);
                let app = match (binder.take(), head.take()) {
                    (Some((h, vars)), _) => Application::binder(h, vars, args),
                    (None, Some(head)) => Application::new(head, args),
                    (None, None) => return Err(ParseError::new(at, ParseErrorKind::Syntax(SyntaxProblem::MissingHead))),
                };
                Ok(Need::Done(Term::Apply(app.map_err(syntax)?)))
            }
            Frame::Let { form, bindings, pending, body_next } => {
                if *body_next {
                    let Some(body) = value else { return Ok(Need::Term) };
                    self.rparen()?;
                    return Ok(Need::Done(Term::Let(LetTerm::new(*form, std::mem::take(bindings), body))));
                }
                if let Some(v) = value {
                    let Some(x) = pending.take() else { return Err(self.error(ParseErrorKind::Syntax(SyntaxProblem::BindingPair))) };
                    bindings.push((x, v));
                    self.rparen()?;
                }
                if self.eat(&Tok::LParen) {
                    *pending = Some(self.symbol()?);
                    if self.peek() == Some(&Tok::RParen) {
                        return Err(self.error(ParseErrorKind::Syntax(SyntaxProblem::BindingPair)));
                    }
                    return Ok(Need::Term);
                }
                self.rparen()?;
                *body_next = true;
                Ok(Need::Term)
            }
            Frame::Annot { term, attributes, pending } => {
                if let Some(v) = value {
                    match pending.take() {
                        Some(keyword) => attributes.push(Attribute { keyword, value: Some(v) }),
                        None => *term = Some(v),
                    }
                }
                let Some(t) = term.take() else { return Ok(Need::Term) };
                *term = Some(t);
                while matches!(self.peek(), Some(Tok::Keyword(_))) {
                    let keyword = self.keyword()?;
                    match self.peek() {
                        Some(Tok::Keyword(_)) | Some(Tok::RParen) | None => attributes.push(Attribute { keyword, value: None }),
                        Some(_) => {
                            *pending = Some(keyword);
                            return Ok(Need::Term);
                        }
                    }
                }
                let close = self.position();
                self.rparen()?;
                let Some(t) = term.take() else { return Err(self.error(ParseErrorKind::Syntax(SyntaxProblem::AnnotationWithoutTerm))) };
                let Ok(attributes) = NonEmpty::from_vec(std::mem::take(attributes)) else { return Err(ParseError::new(close, ParseErrorKind::Syntax(SyntaxProblem::AnnotationWithoutAttribute))) };
                Ok(Need::Done(Term::Annotated(Annotation::new(t, attributes))))
            }
        }
    }

    fn terms_until_rparen(&mut self) -> Result<Vec<Term>, ParseError> {
        let mut out = Vec::new();
        while !self.eat(&Tok::RParen) {
            out.push(self.term()?);
        }
        Ok(out)
    }

    fn term_list(&mut self) -> Result<Vec<Term>, ParseError> {
        self.lparen()?;
        self.terms_until_rparen()
    }

    fn attributes(&mut self) -> Result<Vec<Attribute>, ParseError> {
        let mut out = Vec::new();
        while matches!(self.peek(), Some(Tok::Keyword(_))) {
            let keyword = self.keyword()?;
            let value = match self.peek() {
                Some(Tok::Keyword(_)) | Some(Tok::RParen) | None => None,
                Some(_) => Some(self.term()?),
            };
            out.push(Attribute { keyword, value });
        }
        Ok(out)
    }

    fn params(&mut self) -> Result<Vec<TypedParam>, ParseError> {
        self.lparen()?;
        let mut out = Vec::new();
        while self.eat(&Tok::LParen) {
            let name = self.symbol()?;
            let ty = self.term()?;
            let attributes = self.attributes()?;
            self.rparen()?;
            out.push(TypedParam { name, ty, attributes });
        }
        self.rparen()?;
        Ok(out)
    }

    fn pairs(&mut self) -> Result<Vec<(Term, Term)>, ParseError> {
        self.lparen()?;
        let mut out = Vec::new();
        while self.eat(&Tok::LParen) {
            let a = self.term()?;
            let b = self.term()?;
            self.rparen()?;
            out.push((a, b));
        }
        self.rparen()?;
        Ok(out)
    }

    fn datatype_dec(&mut self) -> Result<DatatypeDec, ParseError> {
        self.lparen()?;
        let params = if self.eat(&Tok::Reserved("par")) {
            let list = self.position();
            self.lparen()?;
            let mut ps = Vec::new();
            while !self.eat(&Tok::RParen) {
                ps.push(self.symbol()?);
            }
            if ps.is_empty() {
                return Err(ParseError::new(list, ParseErrorKind::Syntax(SyntaxProblem::EmptyParameterList)));
            }
            self.lparen()?;
            ps
        } else {
            Vec::new()
        };
        let mut constructors = Vec::new();
        while self.eat(&Tok::LParen) {
            let name = self.symbol()?;
            let mut selectors = Vec::new();
            while self.eat(&Tok::LParen) {
                let s = self.symbol()?;
                let t = self.term()?;
                self.rparen()?;
                selectors.push((s, t));
            }
            self.rparen()?;
            constructors.push(ConstructorDec { name, selectors });
        }
        let close = self.position();
        self.rparen()?;
        let Ok(constructors) = NonEmpty::from_vec(constructors) else { return Err(ParseError::new(close, ParseErrorKind::Syntax(SyntaxProblem::DatatypeWithoutConstructor))) };
        if !params.is_empty() {
            self.rparen()?;
        }
        Ok(DatatypeDec { params, constructors })
    }

    fn step(&mut self) -> Result<Step, ParseError> {
        let name = self.symbol()?;
        let conclusion = if matches!(self.peek(), Some(Tok::Keyword(_))) { None } else { Some(self.term()?) };
        let pos = self.position();
        let kw = self.keyword()?;
        if kw.as_str() != "rule" {
            return Err(ParseError::new(pos, ParseErrorKind::Syntax(SyntaxProblem::StepWithoutRule)));
        }
        let rule = self.symbol()?;
        let mut premises = None;
        let mut args = None;
        if matches!(self.peek(), Some(Tok::Keyword(k)) if k == "premises") {
            self.at += 1;
            premises = Some(self.term_list()?);
        }
        if matches!(self.peek(), Some(Tok::Keyword(k)) if k == "args") {
            self.at += 1;
            args = Some(self.term_list()?);
        }
        Ok(Step { name, conclusion, rule, premises, args })
    }

    fn rule(&mut self) -> Result<RuleDecl, ParseError> {
        let name = self.symbol()?;
        let params = self.params()?;
        let mut assumption = None;
        let mut premises = None;
        let mut args = None;
        let mut requires = None;
        let mut pos = self.position();
        let mut kw = self.keyword()?;
        if kw.as_str() == "assumption" {
            assumption = Some(self.term()?);
            pos = self.position();
            kw = self.keyword()?;
        }
        if kw.as_str() == "premises" {
            premises = Some(RulePremises::Premises(self.term_list()?));
            pos = self.position();
            kw = self.keyword()?;
        } else if kw.as_str() == "premise-list" {
            let pattern = self.term()?;
            let constructor = self.term()?;
            premises = Some(RulePremises::PremiseList { pattern, constructor });
            pos = self.position();
            kw = self.keyword()?;
        }
        if kw.as_str() == "args" {
            args = Some(self.term_list()?);
            pos = self.position();
            kw = self.keyword()?;
        }
        if kw.as_str() == "requires" {
            requires = Some(self.pairs()?);
            pos = self.position();
            kw = self.keyword()?;
        }
        let conclusion = match kw.as_str() {
            "conclusion" => RuleConclusion::Conclusion(self.term()?),
            "conclusion-explicit" => RuleConclusion::Explicit(self.term()?),
            _ => return Err(ParseError::new(pos, ParseErrorKind::Syntax(SyntaxProblem::RuleField(kw)))),
        };
        let attributes = self.attributes()?;
        Ok(RuleDecl { name, params, assumption, premises, args, requires, conclusion, attributes })
    }

    fn command(&mut self) -> Result<Command, ParseError> {
        self.lparen()?;
        let pos = self.position();
        let name = match self.next("a command")? {
            Tok::Symbol(s) => s,
            other => return Err(ParseError::new(pos, ParseErrorKind::UnexpectedToken { expected: "a Eunoia command", found: other.describe() })),
        };
        let cmd = match name.as_str() {
            "assume" => Command::Assume { name: self.symbol()?, formula: self.term()? },
            "assume-push" => Command::AssumePush { name: self.symbol()?, formula: self.term()? },
            "step" => Command::Step(self.step()?),
            "step-pop" => Command::StepPop(self.step()?),
            "declare-const" => {
                let name = self.symbol()?;
                let ty = self.term()?;
                Command::DeclareConst { name, ty, attributes: self.attributes()? }
            }
            "declare-parameterized-const" => {
                let name = self.symbol()?;
                let params = self.params()?;
                let ty = self.term()?;
                Command::DeclareParameterizedConst { name, params, ty, attributes: self.attributes()? }
            }
            "declare-consts" => {
                let cpos = self.position();
                let cat = self.symbol()?;
                let category = LiteralCategory::from_name(cat.as_str()).ok_or_else(|| ParseError::new(cpos, ParseErrorKind::Syntax(SyntaxProblem::UnknownLiteralCategory(cat.as_str().to_string()))))?;
                Command::DeclareConsts { category, ty: self.term()? }
            }
            "declare-datatype" => {
                let name = self.symbol()?;
                Command::DeclareDatatype { name, datatype: self.datatype_dec()? }
            }
            "declare-datatypes" => {
                self.lparen()?;
                let mut sorts = Vec::new();
                while self.eat(&Tok::LParen) {
                    let s = self.symbol()?;
                    let n = self.small_numeral()?;
                    self.rparen()?;
                    sorts.push((s, n));
                }
                self.rparen()?;
                self.lparen()?;
                let mut decs = Vec::new();
                while self.peek() == Some(&Tok::LParen) {
                    decs.push(self.datatype_dec()?);
                }
                self.rparen()?;
                if decs.len() != sorts.len() {
                    return Err(self.error(ParseErrorKind::Syntax(SyntaxProblem::DatatypeCount { sorts: sorts.len(), datatypes: decs.len() })));
                }
                Command::DeclareDatatypes(sorts.into_iter().zip(decs).map(|((s, n), d)| (s, n, d)).collect())
            }
            "declare-sort" => Command::DeclareSort { name: self.symbol()?, arity: self.small_numeral()? },
            "declare-rule" => Command::DeclareRule(self.rule()?),
            "define" => {
                let name = self.symbol()?;
                let params = self.params()?;
                let body = self.term()?;
                Command::Define { name, params, body, attributes: self.attributes()? }
            }
            "program" => {
                let name = self.symbol()?;
                let params = self.params()?;
                let kpos = self.position();
                let kw = self.keyword()?;
                if kw.as_str() != "signature" {
                    return Err(ParseError::new(kpos, ParseErrorKind::Syntax(SyntaxProblem::ProgramWithoutSignature(kw))));
                }
                let tpos = self.position();
                let Ok(arg_types) = NonEmpty::from_vec(self.term_list()?) else { return Err(ParseError::new(tpos, ParseErrorKind::Syntax(SyntaxProblem::ProgramWithoutArgumentType))) };
                let return_type = self.term()?;
                let cases = if self.peek() == Some(&Tok::LParen) { Some(self.pairs()?) } else { None };
                Command::Program(ProgramDecl { name, params, arg_types, return_type, cases })
            }
            "include" => Command::Include(self.string()?),
            "reference" => {
                let file = self.string()?;
                let normalize = if self.peek() == Some(&Tok::RParen) { None } else { Some(self.term()?) };
                Command::Reference { file, normalize }
            }
            "echo" => Command::Echo(if matches!(self.peek(), Some(Tok::Str(_))) { Some(self.string()?) } else { None }),
            "exit" => Command::Exit,
            "reset" => Command::Reset,
            "set-option" => {
                let keyword = self.keyword()?;
                let value = if self.peek() == Some(&Tok::RParen) { None } else { Some(self.term()?) };
                Command::SetOption { keyword, value }
            }
            _ => return Err(ParseError::new(pos, ParseErrorKind::UnexpectedToken { expected: "a Eunoia command", found: Found::Symbol(name) })),
        };
        self.rparen()?;
        Ok(cmd)
    }
}

fn quoted_symbol(s: String, pos: Position) -> Result<Symbol, ParseError> {
    if let Some(word) = UNSUPPORTED_QUOTED.iter().find(|w| **w == s) {
        return Err(ParseError::new(pos, ParseErrorKind::Unsupported(UnsupportedConstruct::QuotedBuiltinWord(word))));
    }
    Ok(Symbol::unchecked(s))
}
