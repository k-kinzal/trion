//! The notation-based object parser: a port of the term construction of
//! `api/parser/NotationBasedParser.scala` and of the notation extensions
//! `MixfixNotation` and `HOASNotation` (`api/notations/NotationExtension.scala`,
//! `api/notations/Pragmatics.scala`).
//!
//! An object is tokenized with the lexer extensions in scope and scanned with
//! the notations in scope (the private module `scanner`); the scanned tree is turned into
//! a term. A token that no notation matched is a bound variable, a free or
//! context variable, `_` (a fresh unknown), a qualified identifier (a token
//! with `?` or `/`, resolved against the namespace map, with MMT's heuristics
//! `Thy?sym` → `?Thy?sym` and `prefix/rest` → `prefix:/rest`), or, if it starts
//! with an upper-case letter, a free variable; otherwise it is an error. Several
//! unmatched elements in a row are the default application of the first to the
//! others. A notation of a constant builds a term according to the notation
//! extension applicable at the level of the notation (its `meta` theory, or
//! the meta-theory of the constant's theory): under LF's higher-order abstract
//! syntax (the rule `LFHOAS`) an application `apply(c, args)` and a binding
//! `apply(c, lambda(ctx, args))`, otherwise OMA and OMBINDC.
//!
//! Not supported: label arguments (OML), arguments before bound variables,
//! local notations, and ambiguity resolution (several constants with agreeing
//! notations, which MMT turns into a `oneOf` term resolved by type checking):
//! these are reported as errors.
//!
//! The term is built recursively, one level per notation (brackets
//! included) and per interpolated string; a text that nests more than
//! [`crate::Limits::depth`] levels is rejected with [`ErrorKind::Limit`]
//! before the stack runs out.

use crate::error::{Error, ErrorKind, Pos, Result};
use crate::lexer::{tokenize, External, InterpolationPart};
use crate::library::Scope;
use crate::notation::Marker;
use crate::paths;
use crate::lexer::Token;
use crate::scanner::{Elem, FoundContent, Matched, Unmatched};
use crate::term::{LitValue, Literal, Term, VarDecl};
use crate::uri::{GlobalName, LNStep, LocalName, NamespaceMap, Path};

/// The result of reading an object (`ParseResult`): the term, the unknowns
/// it contains (what the text leaves open, for a type checker to solve), and
/// the free variables with the unknowns standing for their types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseResult {
    term: Term,
    unknowns: Vec<LocalName>,
    free: Vec<(LocalName, Term)>,
}

impl ParseResult {
    /// A term without unknowns and free variables.
    pub fn plain(term: Term) -> ParseResult {
        ParseResult { term, unknowns: Vec::new(), free: Vec::new() }
    }

    /// The term.
    pub fn term(&self) -> &Term {
        &self.term
    }

    /// The term, consuming the result.
    pub fn into_term(self) -> Term {
        self.term
    }

    /// The unknowns in order of creation.
    pub fn unknowns(&self) -> &[LocalName] {
        &self.unknowns
    }

    /// The free variables and the unknowns for their types.
    pub fn free(&self) -> &[(LocalName, Term)] {
        &self.free
    }

    /// Whether the term has neither unknowns nor free variables.
    pub fn is_plain(&self) -> bool {
        self.unknowns.is_empty() && self.free.is_empty()
    }
}

impl From<Term> for ParseResult {
    fn from(term: Term) -> ParseResult {
        ParseResult::plain(term)
    }
}

struct Variables {
    unknowns: Vec<LocalName>,
    free: Vec<LocalName>,
    counter: usize,
}

impl Variables {
    fn next(&mut self) -> String {
        let s = self.counter.to_string();
        self.counter += 1;
        s
    }
    fn new_unknown(&mut self, name: LocalName, bound: &[LocalName]) -> Term {
        self.unknowns.push(name.clone());
        if bound.is_empty() {
            Term::Var(name)
        } else {
            Term::app(Term::Var(name), bound.iter().map(|b| Term::Var(b.clone())).collect())
        }
    }
    fn implicit_arg(&mut self) -> LocalName {
        LocalName::simple_steps(["", "I", &self.next()])
    }
    fn explicit_unknown(&mut self) -> LocalName {
        LocalName::simple_steps(["", "_", &self.next()])
    }
    fn type_of(&mut self, name: &LocalName) -> LocalName {
        let mut steps = vec![LNStep::Simple(String::new())];
        steps.extend(name.steps().iter().cloned());
        steps.push(LNStep::Simple(self.next()));
        LocalName::new(steps)
    }
}

fn is_letter_or_number(c: char) -> bool {
    crate::chars::is_letter_or_number(c)
}

/// `mayBeName`: a letter followed by letters, numbers and connectors.
fn may_be_name(n: &str) -> bool {
    let mut cs = n.chars();
    match cs.next() {
        Some(c) if crate::chars::is_letter(c) => cs.all(|c| is_letter_or_number(c) || crate::chars::is_connector(c)),
        _ => false,
    }
}

/// Java's `String.split` on `?`: trailing empty strings are removed (`utils.stringToList`).
fn split_question(s: &str) -> Vec<String> {
    let mut v: Vec<String> = s.split('?').map(str::to_string).collect();
    while v.len() > 1 && v.last().is_some_and(String::is_empty) {
        v.pop();
    }
    if v == [""] {
        v.clear();
    }
    v
}

struct Parser<'a> {
    scope: &'a Scope,
    context: &'a [LocalName],
    vars: Variables,
    /// The levels of notations and interpolations entered.
    depth: usize,
}

/// Parses an object in a scope; `context` are variables bound outside the object.
pub(crate) fn parse_object(scope: &Scope, text: &str, pos: Pos, context: &[LocalName]) -> Result<ParseResult> {
    let mut p = Parser { scope, context, vars: Variables { unknowns: Vec::new(), free: Vec::new(), counter: 0 }, depth: 0 };
    let term = p.parse_text(text, pos, &[])?;
    let free_names = std::mem::take(&mut p.vars.free);
    let mut free = Vec::new();
    for n in free_names {
        let tn = p.vars.type_of(&n);
        let t = p.vars.new_unknown(tn, &[]);
        free.push((n, t));
    }
    Ok(ParseResult { term, unknowns: p.vars.unknowns, free })
}

impl<'a> Parser<'a> {
    /// Enters one more level; fails beyond the depth limit.
    fn enter(&mut self, pos: Pos) -> Result<()> {
        self.depth += 1;
        let limit = self.scope.limits.depth();
        if self.depth > limit {
            return Err(Error::at(ErrorKind::Limit, pos, format!("the object nests more than {limit} notations")));
        }
        Ok(())
    }

    fn parse_text(&mut self, text: &str, pos: Pos, bound: &[LocalName]) -> Result<Term> {
        let lexed = tokenize(text, pos, &self.scope.lexers, self.scope.limits.depth())?;
        if lexed.is_empty() {
            return Err(Error::at(ErrorKind::Object, pos, format!("no tokens found: {text}")));
        }
        let ul = Unmatched::from_lexed(lexed, self.scope.table.clone());
        self.make_term(Elem::Unmatched(Box::new(ul)), bound, false)
    }

    fn ns(&self) -> &NamespaceMap {
        &self.scope.ns
    }

    // The functions on the recursion (`make_term`, `make_unmatched`,
    // `make_term_from_matched`, `make_oml`) keep their own state small and leave
    // the rest to helpers, so that one level of nesting costs little stack even
    // in an unoptimized build, where every temporary has its own slot.

    /// Builds the term of an element. Brackets and a list that scans to a
    /// single element are followed in a loop, not by recursion; a notation
    /// with arguments and a default application are one level each.
    fn make_term(&mut self, mut te: Elem, bound: &[LocalName], attrib: bool) -> Result<Term> {
        loop {
            match te {
                Elem::Token(t) => return self.make_token(t, bound, attrib),
                Elem::External(External::Term(t, _)) => return Ok(t),
                Elem::External(External::Interpolation { parts, string, concat, pos }) => return self.make_interpolation(parts, string, concat, pos, bound),
                Elem::Matched(mut ml) => {
                    if let Some(inner) = bracket_content(&mut ml) {
                        te = Elem::Unmatched(Box::new(inner));
                        continue;
                    }
                    if ml.tokens.is_empty() {
                        // a constant notation: no argument, no recursion
                        return self.make_term_from_matched(*ml, bound, attrib);
                    }
                    self.enter(ml.pos)?;
                    let t = self.make_term_from_matched(*ml, bound, attrib);
                    self.depth -= 1;
                    return t;
                }
                Elem::Unmatched(mut ul) => {
                    if attrib {
                        if let Some(r) = single_variable(&ul) {
                            return r;
                        }
                    }
                    ul.scan(self.scope.limits.max_open())?;
                    let mut tl = std::mem::take(&mut ul.tl);
                    if tl.len() == 1 {
                        let Some(e) = tl.pop() else { unreachable!("a list of one element") };
                        te = e;
                        continue;
                    }
                    self.enter(tl.first().map(Elem::pos).unwrap_or_default())?;
                    let t = self.make_application(tl, bound);
                    self.depth -= 1;
                    return t;
                }
            }
        }
    }

    /// Several elements in a row: the default application of the first to the others.
    fn make_application(&mut self, tl: Vec<Elem>, bound: &[LocalName]) -> Result<Term> {
        let mut terms = Vec::with_capacity(tl.len());
        for e in tl {
            terms.push(self.make_term(e, bound, false)?);
        }
        self.default_application_of(terms)
    }

    fn default_application_of(&self, mut terms: Vec<Term>) -> Result<Term> {
        if terms.is_empty() {
            return Err(Error::at(ErrorKind::Object, Pos::START, "an empty object"));
        }
        let head = terms.remove(0);
        Ok(self.default_application(head, terms))
    }

    fn make_token(&mut self, t: Token, bound: &[LocalName], attrib: bool) -> Result<Term> {
        let word = t.word;
        let pos = t.pos;
        let name = LocalName::parse(&word, &NamespaceMap::empty()).map_err(|e| e.or_at(pos))?;
        if attrib {
            if bound.contains(&name) {
                return Err(Error::at(ErrorKind::Object, pos, format!("variable {word} shadows a bound name")));
            }
            if may_be_name(&word) {
                return Ok(Term::Var(LocalName::simple(word)));
            }
            return Err(Error::at(ErrorKind::Object, pos, format!("fresh variable name expected; found: {word}")));
        }
        if bound.iter().rev().any(|b| *b == name) {
            return Ok(Term::Var(name));
        }
        if self.vars.free.contains(&name) || self.context.contains(&name) {
            return Ok(Term::Var(name));
        }
        if word == "_" {
            let n = self.vars.explicit_unknown();
            return Ok(self.vars.new_unknown(n, bound));
        }
        if word.contains('?') || word.contains('/') {
            return self.make_identifier(&word, pos);
        }
        if may_be_name(&word) && word.chars().next().is_some_and(char::is_uppercase) {
            self.vars.free.push(name.clone());
            return Ok(Term::Var(name));
        }
        Err(Error::at(ErrorKind::Unresolved, pos, format!("unbound token: {word}")))
    }

    fn make_interpolation(&mut self, parts: Vec<InterpolationPart>, string: Term, concat: Term, pos: Pos, bound: &[LocalName]) -> Result<Term> {
        let mut terms = Vec::new();
        for p in parts {
            match p {
                InterpolationPart::Str(s) => terms.push(Term::Lit(Literal::new(LitValue::String(s), string.clone()))),
                InterpolationPart::Mmt(s, ppos) => {
                    self.enter(ppos)?;
                    let inner_ctx: Vec<LocalName> = self.context.iter().chain(bound.iter()).cloned().collect();
                    let mut inner = Parser { scope: self.scope, context: &inner_ctx, vars: std::mem::replace(&mut self.vars, Variables { unknowns: vec![], free: vec![], counter: 0 }), depth: self.depth };
                    let t = inner.parse_text(&s, ppos, &[]);
                    self.vars = inner.vars;
                    self.depth -= 1;
                    terms.push(t?);
                }
            }
        }
        let mut it = terms.into_iter();
        let first = it.next().ok_or_else(|| Error::at(ErrorKind::Object, pos, "empty string interpolation"))?;
        Ok(it.fold(first, |acc, t| Term::app(Term::sym(&paths::apply()), vec![concat.clone(), acc, t])))
    }

    /// `Pragmatics.defaultApplication` at the level of the current theory.
    fn default_application(&self, fun: Term, args: Vec<Term>) -> Term {
        if matches!(fun, Term::Module(_)) {
            return Term::app(fun, args);
        }
        if self.scope.hoas_at(&self.scope.theory) {
            let mut all = vec![fun];
            all.extend(args);
            Term::app(Term::sym(&paths::apply()), all)
        } else {
            Term::app(fun, args)
        }
    }

    /// `makeIdentifier`.
    fn make_identifier(&self, word: &str, pos: Pos) -> Result<Term> {
        let segments = split_question(word);
        let mut word = word.to_string();
        if segments.len() == 1 {
            let ln = LocalName::parse(&word, &NamespaceMap::empty()).map_err(|e| e.or_at(pos))?;
            let options = self.scope.resolve_name(&ln);
            return match options.len() {
                0 => Err(Error::at(ErrorKind::Unresolved, pos, format!("ill-formed constant reference {ln}"))),
                1 => Ok(Term::Sym(options[0].clone())),
                _ => Err(Error::at(ErrorKind::Ambiguous, pos, format!("ambiguous constant reference {ln}"))),
            };
        }
        if segments.len() == 2 {
            let fst = &segments[0];
            if !fst.contains(':') && fst.chars().next().is_some_and(char::is_uppercase) {
                word = format!("?{word}");
            }
        }
        let head = segments.first().cloned().unwrap_or_else(|| word.clone());
        let before_first_slash: String = head.chars().take_while(|&c| c != '/').collect();
        if !before_first_slash.contains(':') && self.ns().get(&before_first_slash).is_some() {
            word = format!("{before_first_slash}:{}", &word[before_first_slash.len()..]);
        }
        match Path::parse(&word, self.ns()).map_err(|e| e.or_at(pos))? {
            Path::Symbol(g) => Ok(Term::Sym(g)),
            Path::Module(m) => Ok(Term::Module(m)),
            p => Err(Error::at(ErrorKind::Object, pos, format!("content path expected: {p}"))),
        }
    }

    fn make_term_from_matched(&mut self, ml: Matched, bound: &[LocalName], attrib: bool) -> Result<Term> {
        let mut b = Building::plan(ml, attrib)?;
        while let Some(job) = b.jobs.pop() {
            match job {
                Job::Implicit(n) => {
                    let t = self.implicit(&b, bound);
                    b.put(n, t);
                }
                Job::Var(ul, typed) => {
                    let vd = self.make_oml(ul, &b.bound(bound), typed)?;
                    b.new_bound.push(vd.name.clone());
                    b.vars.push(vd);
                }
                Job::Arg(ul, n, attrib) => {
                    let t = self.make_term(Elem::Unmatched(Box::new(ul)), &b.bound(bound), attrib)?;
                    b.put(n, t);
                }
            }
        }
        self.assemble(*b)
    }

    fn implicit(&mut self, b: &Building, bound: &[LocalName]) -> Term {
        let name = self.vars.implicit_arg();
        self.vars.new_unknown(name, &b.bound(bound))
    }

    /// The term of a notation whose arguments and variables are built.
    fn assemble(&self, b: Building) -> Result<Term> {
        let Building { rules, pos, subs, vars, mut args, is_constant, .. } = b;
        let mut cons: Vec<GlobalName> = Vec::new();
        for r in &rules {
            if !cons.contains(&r.name) {
                cons.push(r.name.clone());
            }
        }
        if cons.len() == 1 && paths::brackets().contains(&cons[0]) {
            return if args.is_empty() { Err(Error::at(ErrorKind::Object, pos, "empty brackets")) } else { Ok(args.swap_remove(0)) };
        }
        if cons.len() > 1 {
            let names: Vec<String> = cons.iter().map(|c| c.to_string()).collect();
            return Err(Error::at(ErrorKind::Ambiguous, pos, format!("several constants have this notation; MMT would build an ambiguous term to be resolved by type checking, which is not supported: {}", names.join(", "))));
        }
        let Some(con) = cons.first() else { return Err(Error::at(ErrorKind::Object, pos, "a notation of no constant")) };
        if is_constant && subs.is_empty() && args.is_empty() && vars.is_empty() {
            return Ok(Term::Sym(con.clone()));
        }
        let rule = &rules[0];
        if !subs.is_empty() {
            return Err(Error::at(ErrorKind::Unsupported, pos, format!("notations with arguments before the bound variables are not supported: {} # {}", con, rule.notation)));
        }
        let level = rule.notation.meta().cloned().or_else(|| self.scope.home_meta(con.module()));
        let hoas = level.as_ref().is_some_and(|l| self.scope.hoas_at(l));
        let op = Term::Sym(con.clone());
        Ok(if hoas {
            if vars.is_empty() {
                let mut all = vec![op];
                all.extend(args);
                Term::app(Term::sym(&paths::apply()), all)
            } else {
                Term::app(Term::sym(&paths::apply()), vec![op, Term::Bind(Box::new(Term::sym(&paths::lambda())), vars, args)])
            }
        } else if vars.is_empty() {
            if args.is_empty() { op } else { Term::app(op, args) }
        } else {
            Term::Bind(Box::new(op), vars, args)
        })
    }

    /// `makeOML` for variables: `x`, `x : A`, `x := d`, in any combination.
    fn make_oml(&mut self, ul: Unmatched, bound: &[LocalName], typed: bool) -> Result<VarDecl> {
        let pos = ul.tl.first().map(Elem::pos).unwrap_or_default();
        let t = self.make_term(Elem::Unmatched(Box::new(ul)), bound, true)?;
        self.var_decl(t, pos, bound, typed)
    }

    fn var_decl(&mut self, t: Term, pos: Pos, bound: &[LocalName], typed: bool) -> Result<VarDecl> {
        let mut tp = None;
        let mut df = None;
        let mut cur = t.clone();
        let name = loop {
            let (f, a, b) = match &cur {
                Term::Var(n) => break Some(n.clone()),
                Term::App(f, xs) => match (&**f, xs.as_slice()) {
                    (Term::Sym(f), [a, b]) => (f.clone(), a.clone(), b.clone()),
                    (Term::Sym(ap), [Term::Sym(f), a, b]) if *ap == paths::apply() => (f.clone(), a.clone(), b.clone()),
                    _ => break None,
                },
                _ => break None,
            };
            match self.scope.role(&f) {
                Some("Type") if tp.is_none() => tp = Some(b),
                Some("Def") if df.is_none() => df = Some(b),
                Some("Notation") => return Err(Error::at(ErrorKind::Unsupported, pos, "notations of bound variables are not supported")),
                _ => break None,
            }
            cur = a;
        };
        let Some(name) = name else {
            return Err(Error::at(ErrorKind::Object, pos, format!("expected declaration, found other term: {t}")));
        };
        if tp.is_none() && typed {
            let n = self.vars.type_of(&name);
            tp = Some(self.vars.new_unknown(n, bound));
        }
        Ok(VarDecl { name, tp, df })
    }
}

/// The content of brackets (`mmt?mmt?brackets` and the Andrews dots), which
/// are not part of the term.
fn bracket_content(ml: &mut Matched) -> Option<Unmatched> {
    let first = ml.rules.first()?;
    if !paths::brackets().contains(&first.name) || ml.rules.iter().any(|r| r.name != first.name) || first.arity.components().count() != 1 {
        return None;
    }
    match ml.tokens.as_mut_slice() {
        [(FoundContent::Simp(Marker::Arg(_)), uls)] if uls.len() == 1 => uls.pop(),
        _ => None,
    }
}

/// `attrib` with a single token: the name of a variable.
fn single_variable(ul: &Unmatched) -> Option<Result<Term>> {
    match ul.tl.as_slice() {
        [Elem::Token(t)] => Some(LocalName::parse(&t.word, &NamespaceMap::empty()).map(Term::Var).map_err(|e| e.or_at(t.pos))),
        _ => None,
    }
}

/// What remains to be built for one notation, in reverse order.
enum Job {
    /// An implicit argument with this number.
    Implicit(usize),
    /// A variable declaration; whether the marker is typed.
    Var(Unmatched, bool),
    /// An argument with this number, read as a variable (`attrib`) or not.
    Arg(Unmatched, usize, bool),
}

/// The state of building the term of one notation (`makeTermFromMatched`),
/// kept on the heap.
struct Building {
    rules: Vec<std::rc::Rc<crate::scanner::ParsingRule>>,
    pos: Pos,
    first_var: usize,
    is_constant: bool,
    jobs: Vec<Job>,
    subs: Vec<Term>,
    vars: Vec<VarDecl>,
    args: Vec<Term>,
    new_bound: Vec<LocalName>,
}

impl Building {
    /// Assigns the found tokens to the markers of the notation in order.
    fn plan(ml: Matched, attrib: bool) -> Result<Box<Building>> {
        let pos = ml.pos;
        let Some(rule) = ml.rules.first().cloned() else { return Err(Error::at(ErrorKind::Object, pos, "a notation without rule")) };
        let arity = &rule.arity;
        if arity.components().any(|m| matches!(m, Marker::LabelArg(..) | Marker::LabelSeqArg(..))) {
            return Err(Error::at(ErrorKind::Unsupported, pos, format!("notations with label arguments (OML) are not supported: {} # {}", rule.name, rule.notation)));
        }
        let mut jobs = Vec::new();
        let mut tokens: Vec<Option<(FoundContent, Vec<Unmatched>)>> = ml.tokens.into_iter().map(Some).collect();
        let mut processed = 0;
        for comp in arity.components() {
            let n = comp.number().unwrap_or(0) as usize;
            if let Marker::ImplicitArg(_) = comp {
                jobs.push(Job::Implicit(n));
                continue;
            }
            for slot in tokens.iter_mut() {
                let Some((fc, uls)) = slot.take_if(|(fc, _)| fc.marker().number() == Some(n as u32)) else { continue };
                processed += 1;
                match (&fc, fc.marker()) {
                    (FoundContent::Simp(_), Marker::Var { typed, .. }) | (FoundContent::Seq(_), Marker::Var { typed, .. }) => jobs.extend(uls.into_iter().map(|ul| Job::Var(ul, *typed))),
                    (FoundContent::Simp(_), Marker::Arg(m)) => {
                        let ul = uls.into_iter().next().ok_or_else(|| Error::at(ErrorKind::Object, pos, "missing argument"))?;
                        jobs.push(Job::Arg(ul, n, attrib && *m == 1));
                    }
                    (FoundContent::Seq(_), Marker::SeqArg(..)) => jobs.extend(uls.into_iter().map(|ul| Job::Arg(ul, n, false))),
                    _ => return Err(Error::at(ErrorKind::Object, pos, "unexpected found object")),
                }
            }
        }
        if processed != tokens.len() {
            return Err(Error::at(ErrorKind::Object, pos, "unprocessed tokens"));
        }
        jobs.reverse();
        let first_var = arity.first_var_number() as usize;
        let is_constant = arity.is_constant();
        Ok(Box::new(Building { rules: ml.rules, pos, first_var, is_constant, jobs, subs: Vec::new(), vars: Vec::new(), args: Vec::new(), new_bound: Vec::new() }))
    }

    /// The variables bound outside and by the variables built so far.
    fn bound(&self, outer: &[LocalName]) -> Vec<LocalName> {
        outer.iter().chain(self.new_bound.iter()).cloned().collect()
    }

    /// Records an argument: before the first variable it is a substitution.
    fn put(&mut self, n: usize, t: Term) {
        if n < self.first_var {
            self.subs.push(t)
        } else {
            self.args.push(t)
        }
    }
}
