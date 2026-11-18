//! The printer: terms and theories back to MMT's surface syntax
//! (doc/language/objects.md, doc/language/declarations.md section Notations; the inverse of
//! `api/parser/NotationBasedParser.scala` as implemented in [`crate::objparser`]).
//!
//! A term is printed in the scope it is read in. A constant is printed by its
//! name if that name is a single token, refers to it alone and is no
//! delimiter of a notation in scope, and otherwise by a qualified reference:
//! `?Theory?name` within the namespace of the scope, `p/seg?Theory?name` or
//! `p/?Theory?name` with a namespace prefix `p` of the scope (the parser's
//! `prefix/rest` heuristic), or `☞URI` if the URI lexer is in scope. A
//! literal is printed with the lexer of its type (`"…"`, digits, `nt"…"`). An
//! application or binding is printed with the notation of its head constant
//! if the notation extension of the notation's level built it (OMA/OMBINDC
//! for mixfix, `apply`/`lambda` under LF's higher-order abstract syntax) and
//! its shape fits the notation, and otherwise as a default application
//! (juxtaposition) where the parser would build that term. Every compound
//! argument is put in brackets `( … )`, so that precedences never decide the
//! reading; brackets must therefore be in scope (they are wherever
//! `mmt?mmt` is, which LF includes).
//!
//! The printer does not trust itself: every printed object is read back in
//! the same scope and compared with the original (term, unknowns and free
//! variables). A term that cannot be printed so that it reads back as itself
//! is an error of kind [`ErrorKind::Print`], never a different text. Known
//! cases: solved implicit arguments of a notation (the notation would make
//! them unknowns again; the term is printed as a default application where
//! that builds it), negative integers (no lexer reads them), strings that
//! the quote lexer cannot read back, and terms whose head is neither a
//! constant with a fitting notation nor printable as a default application.
//!
//! Theories are printed as a document ([`Library::print_theories`]): one `namespace`
//! instruction per change of namespace, one `import` per namespace that
//! objects refer to, the document rules, and each theory with its meta-theory
//! as an absolute URI. The objects of a declaration are printed in the scope
//! that elaboration of the printed document will read them in (the
//! declarations before it), so reading the document back yields the same
//! theories.

use std::collections::HashMap;

use crate::error::{Error, ErrorKind, Pos, Result};
use crate::lexer::{tokenize, Lexed, LexerRule, SemType};
use crate::library::{Constant, Declaration, Library, Metadatum, Scope, Seen, Theory};
use crate::notation::{Marker, Notation};
use crate::objparser::{parse_object, ParseResult};
use crate::paths;
use crate::scanner::ParsingRule;
use crate::syntax::{self, Component, Decl, DocItem, Document, ObjectText, Word};
use crate::term::{LitValue, Literal, Term, VarDecl};
use crate::uri::{DPath, GlobalName, LNStep, LocalName, MPath, NamespaceMap, Path, Uri};

fn print_error(msg: impl Into<String>) -> Error {
    Error::new(ErrorKind::Print, msg)
}

impl Library {
    /// Prints theories (with their nested theories) as one document that
    /// elaborates to the same theories (see the module documentation).
    pub fn print_theories(&self, theories: &[MPath]) -> Result<String> {
        Ok(self.document_of(theories)?.to_string())
    }

    /// The document that [`Library::print_theories`] prints.
    pub fn document_of(&self, theories: &[MPath]) -> Result<Document> {
        document(self, theories)
    }
}

/// Prints an object and checks that it reads back as itself.
pub(crate) fn object(scope: &Scope, r: &ParseResult) -> Result<String> {
    check_depth(scope, r.term())?;
    let mut p = Render { scope };
    let text = p.top(r.term())?;
    let back = parse_object(scope, &text, Pos::START, &[]).map_err(|e| print_error(format!("the printed object `{text}` does not read back: {e}")))?;
    if back != *r {
        return Err(print_error(format!("the printed object `{text}` reads back as {} instead of {}", back.term(), r.term())));
    }
    Ok(text)
}

/// A term nests one level less than its depth: a symbol nests none.
pub(crate) fn check_depth(scope: &Scope, t: &Term) -> Result<()> {
    let limit = scope.limits.depth();
    if t.depth() > limit.saturating_add(1) {
        return Err(Error::new(ErrorKind::Limit, format!("the object nests more than {limit} levels")));
    }
    Ok(())
}

fn is_unknown(n: &LocalName) -> bool {
    matches!(n.steps().first(), Some(LNStep::Simple(s)) if s.is_empty()) && n.len() > 1
}

fn unknown_kind(n: &LocalName) -> Option<&str> {
    if !is_unknown(n) {
        return None;
    }
    match n.steps().get(1) {
        Some(LNStep::Simple(s)) if s == "I" && n.len() == 3 => Some("I"),
        Some(LNStep::Simple(s)) if s == "_" && n.len() == 3 => Some("_"),
        _ => Some("type"),
    }
}

/// If a term is an unknown applied to exactly the given bound variables, its name.
fn unknown_over<'t>(t: &'t Term, bound: &[LocalName]) -> Option<&'t LocalName> {
    match t {
        Term::Var(n) if is_unknown(n) && bound.is_empty() => Some(n),
        Term::App(f, xs) => match &**f {
            Term::Var(n) if is_unknown(n) && xs.len() == bound.len() && xs.iter().zip(bound).all(|(x, b)| matches!(x, Term::Var(y) if y == b)) => Some(n),
            _ => None,
        },
        _ => None,
    }
}

struct Render<'s> {
    scope: &'s Scope,
}

impl<'s> Render<'s> {
    /// Whether a word is read as exactly one token.
    fn one_token(&self, w: &str) -> bool {
        match tokenize(w, Pos::START, &self.scope.lexers, self.scope.limits.depth()) {
            Ok(ts) => matches!(ts.as_slice(), [Lexed::Token(t)] if t.word == w),
            Err(_) => false,
        }
    }

    fn top(&mut self, t: &Term) -> Result<String> {
        Ok(self.render(t, &[])?.0)
    }

    /// Renders a term in argument position: atoms as they are, everything else in brackets.
    fn arg(&mut self, t: &Term, bound: &[LocalName]) -> Result<String> {
        let (s, atomic) = self.render(t, bound)?;
        if atomic {
            Ok(s)
        } else if self.scope.has_constant(&paths::brackets_sym()) {
            Ok(format!("({s})"))
        } else {
            Err(print_error(format!("no brackets are in scope to print the argument {t}")))
        }
    }

    /// Renders a term; the flag says whether the text is a single atom.
    fn render(&mut self, t: &Term, bound: &[LocalName]) -> Result<(String, bool)> {
        if let Some(u) = unknown_over(t, bound) {
            return match unknown_kind(u) {
                Some("_") => Ok(("_".into(), true)),
                _ => Err(print_error(format!("the unknown {u} cannot be printed outside an implicit argument of a notation"))),
            };
        }
        match t {
            Term::Var(n) => Ok((n.to_path(), true)),
            Term::Sym(c) => Ok((self.sym(c, bound)?, true)),
            Term::Module(m) => Ok((self.module(m)?, true)),
            Term::Lit(l) => Ok((self.literal(l)?, true)),
            Term::App(f, args) => {
                if let Term::Sym(ap) = &**f {
                    if *ap == paths::apply() && !args.is_empty() {
                        if let Term::Sym(c) = &args[0] {
                            if let Some(s) = self.hoas_notation(c, &args[1..], bound)? {
                                return Ok((s, false));
                            }
                        }
                        if self.scope.hoas_at(&self.scope.theory) {
                            return Ok((self.juxtapose(&args[0], &args[1..], bound)?, false));
                        }
                    }
                    if let Some(s) = self.mixfix_notation(ap, &[], args, bound)? {
                        return Ok((s, false));
                    }
                }
                let default_oma = matches!(&**f, Term::Module(_)) || !self.scope.hoas_at(&self.scope.theory);
                if default_oma {
                    return Ok((self.juxtapose(f, args, bound)?, false));
                }
                Err(print_error(format!("no notation fits the application {t}, and juxtaposition would build an LF application here")))
            }
            Term::Bind(b, vars, args) => {
                if let Term::Sym(c) = &**b {
                    if let Some(s) = self.mixfix_notation(c, vars, args, bound)? {
                        return Ok((s, false));
                    }
                }
                Err(print_error(format!("no notation fits the binding {t}")))
            }
        }
    }

    fn juxtapose(&mut self, f: &Term, args: &[Term], bound: &[LocalName]) -> Result<String> {
        let mut parts = vec![self.arg(f, bound)?];
        for a in args {
            parts.push(self.arg(a, bound)?);
        }
        Ok(parts.join(" "))
    }

    /// The notation extension of a constant's notation builds HOAS terms.
    fn is_hoas(&self, c: &GlobalName, n: &Notation) -> bool {
        let level = n.meta().cloned().or_else(|| self.scope.home_meta(c.module()));
        level.is_some_and(|l| self.scope.hoas_at(&l))
    }

    fn hoas_notation(&mut self, c: &GlobalName, rest: &[Term], bound: &[LocalName]) -> Result<Option<String>> {
        let Some(rule) = self.scope.print.notations.get(c).cloned() else { return Ok(None) };
        if !self.is_hoas(c, &rule.notation) {
            return Ok(None);
        }
        if rule.arity.variables.is_empty() {
            return self.with_notation(&rule, &[], rest, bound);
        }
        match rest {
            [Term::Bind(l, vars, args)] if matches!(&**l, Term::Sym(p) if *p == paths::lambda()) => self.with_notation(&rule, vars, args, bound),
            _ => Ok(None),
        }
    }

    fn mixfix_notation(&mut self, c: &GlobalName, vars: &[VarDecl], args: &[Term], bound: &[LocalName]) -> Result<Option<String>> {
        let Some(rule) = self.scope.print.notations.get(c).cloned() else { return Ok(None) };
        if self.is_hoas(c, &rule.notation) {
            return Ok(None);
        }
        if vars.is_empty() != rule.arity.variables.is_empty() {
            return Ok(None);
        }
        self.with_notation(&rule, vars, args, bound)
    }

    /// Renders with a notation if the variables and arguments fit its arity.
    fn with_notation(&mut self, rule: &ParsingRule, vars: &[VarDecl], args: &[Term], bound: &[LocalName]) -> Result<Option<String>> {
        let arity = &rule.arity;
        if !arity.subargs.is_empty() || args.is_empty() && vars.is_empty() {
            return Ok(None);
        }
        // distribute variables over the variable markers
        let seq_vars = arity.variables.iter().filter(|m| matches!(m, Marker::Var { sep: Some(_), .. })).count();
        let single_vars = arity.variables.len() - seq_vars;
        if seq_vars > 1 || (seq_vars == 0 && vars.len() != single_vars) || vars.len() < single_vars {
            return Ok(None);
        }
        let mut var_slots: HashMap<u32, &[VarDecl]> = HashMap::new();
        let mut i = 0;
        for m in &arity.variables {
            let k = if matches!(m, Marker::Var { sep: Some(_), .. }) { vars.len() - single_vars } else { 1 };
            var_slots.insert(m.number().unwrap_or(0), &vars[i..i + k]);
            i += k;
        }
        // distribute arguments
        let seq_args = arity.arguments.iter().filter(|m| matches!(m, Marker::SeqArg(..))).count();
        let single_args = arity.arguments.len() - seq_args;
        if seq_args > 1 || (seq_args == 0 && args.len() != single_args) || args.len() < single_args {
            return Ok(None);
        }
        let mut new_bound: Vec<LocalName> = bound.to_vec();
        let mut var_texts: HashMap<u32, Vec<String>> = HashMap::new();
        for m in &arity.variables {
            let n = m.number().unwrap_or(0);
            let typed = matches!(m, Marker::Var { typed: true, .. });
            let mut texts = Vec::new();
            for vd in var_slots.get(&n).copied().unwrap_or(&[]) {
                texts.push(self.var_decl(vd, &new_bound, typed)?);
                new_bound.push(vd.name.clone());
            }
            var_texts.insert(n, texts);
        }
        let mut arg_texts: HashMap<u32, Vec<String>> = HashMap::new();
        let mut j = 0;
        for m in &arity.arguments {
            let n = m.number().unwrap_or(0);
            match m {
                Marker::ImplicitArg(_) => {
                    let a = &args[j];
                    j += 1;
                    if unknown_over(a, &new_bound).and_then(unknown_kind) != Some("I") {
                        return Ok(None);
                    }
                }
                Marker::SeqArg(..) => {
                    let k = args.len() - single_args;
                    let mut texts = Vec::new();
                    for a in &args[j..j + k] {
                        texts.push(self.arg(a, &new_bound)?);
                    }
                    j += k;
                    arg_texts.insert(n, texts);
                }
                _ => {
                    let a = &args[j];
                    j += 1;
                    arg_texts.insert(n, vec![self.arg(a, &new_bound)?]);
                }
            }
        }
        let mut out: Vec<String> = Vec::new();
        for m in &rule.markers {
            match m {
                Marker::Delim(d) | Marker::InstanceName(d) => {
                    if d.matched_text().trim().is_empty() {
                        continue;
                    }
                    out.push(d.matched_text().to_string());
                }
                Marker::Arg(n) => match arg_texts.get(n).map(Vec::as_slice) {
                    Some([s]) => out.push(s.clone()),
                    _ => return Ok(None),
                },
                Marker::SeqArg(n, sep) => {
                    let Some(ts) = arg_texts.get(n) else { return Ok(None) };
                    let sep = sep.matched_text().trim();
                    out.push(ts.join(&if sep.is_empty() { " ".to_string() } else { format!(" {sep} ") }));
                }
                Marker::Var { number, sep, .. } => {
                    let Some(ts) = var_texts.get(number) else { return Ok(None) };
                    let sep = sep.as_ref().map(|d| d.matched_text().trim().to_string()).unwrap_or_default();
                    out.push(ts.join(&if sep.is_empty() { " ".to_string() } else { format!(" {sep} ") }));
                }
                Marker::ImplicitArg(_) => {}
                _ => return Ok(None),
            }
        }
        Ok(Some(out.join(" ")))
    }

    fn var_decl(&mut self, vd: &VarDecl, bound: &[LocalName], typed: bool) -> Result<String> {
        let mut s = vd.name.to_path();
        match &vd.tp {
            Some(tp) if unknown_over(tp, bound).and_then(unknown_kind) == Some("type") && typed => {}
            Some(tp) => {
                let d = self.scope.print.type_delim.clone().ok_or_else(|| print_error("no notation with role Type is in scope to print the type of a bound variable"))?;
                s = format!("{s} {d} {}", self.arg(tp, bound)?);
            }
            None => {}
        }
        if let Some(df) = &vd.df {
            let d = self.scope.print.def_delim.clone().ok_or_else(|| print_error("no notation with role Def is in scope to print the definiens of a bound variable"))?;
            s = format!("{s} {d} {}", self.arg(df, bound)?);
        }
        Ok(s)
    }

    fn sym(&self, c: &GlobalName, bound: &[LocalName]) -> Result<String> {
        let name = c.name().to_path();
        if !bound.contains(c.name()) && !self.scope.print.delims.contains(&name) && self.scope.resolve_name(c.name()) == [c.clone()] && self.one_token(&name) && !name.contains('?') && !name.contains('/') && name != "_" {
            return Ok(name);
        }
        let rel = format!("?{}?{}", c.module().name().to_path(), name);
        self.qualified(c.module().doc(), &rel, &format!("{c}"))
    }

    fn module(&self, m: &MPath) -> Result<String> {
        let rel = format!("?{}", m.name().to_path());
        self.qualified(m.doc(), &rel, &format!("{m}"))
    }

    /// A reference `REL` (starting with `?`) relative to a namespace.
    fn qualified(&self, doc: &DPath, rel: &str, full: &str) -> Result<String> {
        let ns = &self.scope.ns;
        let mut candidates = Vec::new();
        if *ns.base().doc() == *doc {
            candidates.push(rel.to_string());
        }
        let segs = doc.uri().path_no_trailing_slash();
        for (p, u) in ns.prefixes() {
            let Ok(pd) = DPath::new(u.clone()) else { continue };
            if let Some(last) = segs.last() {
                if pd.slash(std::slice::from_ref(last)) == *doc {
                    candidates.push(format!("{p}/{last}{rel}"));
                }
            }
            if pd == *doc {
                candidates.push(format!("{p}/{rel}"));
            }
        }
        if self.scope.lexers.contains(&LexerRule::Uri) {
            candidates.push(format!("☞{full}"));
        }
        for c in candidates {
            if c.starts_with('☞') || self.one_token(&c) {
                return Ok(c);
            }
        }
        Err(print_error(format!("{full} cannot be referred to in this scope: its namespace has no prefix and no URI lexer is in scope")))
    }

    fn literal(&self, l: &Literal) -> Result<String> {
        for lx in &self.scope.lexers {
            if let LexerRule::Literal { sem, tp } = lx {
                if *tp != *l.tp || !sem.contains(&l.value) {
                    continue;
                }
                let text = match (&l.value, sem) {
                    (LitValue::String(s), SemType::String) => format!("\"{s}\""),
                    (LitValue::Int(i), _) if !i.is_negative() => i.as_str().to_string(),
                    (LitValue::Bool(b), SemType::Bool) => b.to_string(),
                    (LitValue::Notation(n), SemType::Notation) => format!("nt\"{n}\""),
                    _ => continue,
                };
                return Ok(text);
            }
        }
        Err(print_error(format!("no lexer in scope reads the literal {} of type {} back", l.value.text(), l.tp)))
    }
}

// ---------------------------------------------------------------- documents

/// Collects the namespaces that objects of a theory refer to.
fn namespaces_of(lib: &Library, t: &Theory, out: &mut Namespaces) {
    let add_term = |term: &Term, out: &mut Namespaces| {
        term.visit(&mut |s| match s {
            Term::Sym(g) => out.push(g.module().doc()),
            Term::Module(m) => out.push(m.doc()),
            _ => {}
        })
    };
    let mut stack = vec![t];
    while let Some(t) = stack.pop() {
        for d in t.declarations() {
            match d {
                Declaration::Constant(c) => {
                    for r in c.tp().into_iter().chain(c.df()) {
                        add_term(r.term(), out);
                        for (_, ft) in r.free() {
                            add_term(ft, out);
                        }
                    }
                    for m in c.metadata() {
                        if let Metadatum::Meta(_, v) = m {
                            add_term(v, out);
                        }
                    }
                }
                Declaration::Include(p) => out.push(p.doc()),
                Declaration::Rule(r) => add_term(r.term(), out),
                Declaration::Theory(n) => stack.extend(lib.theory(n)),
            }
        }
        for m in t.metadata() {
            if let Metadatum::Meta(_, v) = m {
                add_term(v, out);
            }
        }
    }
}

/// The namespaces that objects refer to, in order of first reference.
#[derive(Default)]
struct Namespaces {
    order: Vec<DPath>,
    seen: std::collections::HashSet<DPath>,
}

impl Namespaces {
    fn push(&mut self, d: &DPath) {
        if self.seen.insert(d.clone()) {
            self.order.push(d.clone());
        }
    }
}

/// The URI a prefix stands for: the namespace without its last segment if that segment can be part of a token.
fn prefix_uri(d: &DPath) -> Uri {
    let mut u: Uri = d.uri().clone();
    u.path = u.path_no_trailing_slash().to_vec();
    u.query = None;
    u.fragment = None;
    match u.path.last() {
        Some(last) if last.chars().next().is_some_and(crate::chars::is_letter) && last.chars().all(|c| crate::chars::is_letter_or_number(c) || c == '_') => {
            u.path.pop();
            if u.path.is_empty() {
                u.absolute = false;
            }
            u
        }
        _ => u,
    }
}

fn word(s: impl Into<String>) -> Result<Word> {
    let s = s.into();
    Word::new(s.clone()).map_err(|e| print_error(format!("{s} cannot be printed as a word: {e}")))
}

fn obj_text(s: impl Into<String>) -> Result<ObjectText> {
    let s = s.into();
    ObjectText::new(s.clone()).map_err(|e| print_error(format!("`{s}` contains a delimiter: {e}")))
}

fn document(lib: &Library, roots: &[MPath]) -> Result<Document> {
    let mut theories = Vec::new();
    for p in roots {
        let t = lib.theory(p).ok_or_else(|| print_error(format!("theory {p} is not in the library")))?;
        if t.parent().is_some() {
            return Err(print_error(format!("{p} is a nested theory; print its enclosing theory")));
        }
        theories.push(t);
    }
    let mut namespaces = Namespaces::default();
    for t in &theories {
        namespaces_of(lib, t, &mut namespaces);
    }
    let mut items = Vec::new();
    let mut ns = NamespaceMap::empty();
    let mut prefix_uris: Vec<Uri> = Vec::new();
    for d in &namespaces.order {
        let u = prefix_uri(d);
        if !prefix_uris.contains(&u) {
            let p = format!("ns{}", prefix_uris.len());
            items.push(DocItem::Import { prefix: word(&p)?, uri: word(u.to_string())? });
            ns = ns.add(&p, &u);
            prefix_uris.push(u);
        }
    }
    let mut current: Option<DPath> = None;
    let mut doc_rules: Vec<MPath> = Vec::new();
    for t in theories {
        if current.as_ref() != Some(t.path().doc()) {
            items.push(DocItem::Namespace(word(t.path().doc().to_string())?));
            ns = ns.rebase(Path::Doc(t.path().doc().clone()));
            current = Some(t.path().doc().clone());
        }
        let wanted: Vec<MPath> = t
            .document_rules()
            .iter()
            .map(|r| match r.term() {
                Term::Module(m) => Ok(m.clone()),
                o => Err(print_error(format!("document rule {o} is not a module reference"))),
            })
            .collect::<Result<_>>()?;
        if !wanted.starts_with(&doc_rules) {
            return Err(print_error(format!("the document rules of {} differ from those of the theories before it; print it in a document of its own", t.path())));
        }
        for m in &wanted[doc_rules.len()..] {
            items.push(DocItem::Rule(word(m.to_string())?));
        }
        doc_rules = wanted;
        items.push(DocItem::Theory(theory(lib, t, &ns)?));
    }
    Ok(Document { items })
}

/// A theory as a declaration of a document, with its nested theories,
/// printed without recursion: each theory on the stack is printed up to its
/// next nested theory, which is printed before the rest.
fn theory(lib: &Library, root: &Theory, ns: &NamespaceMap) -> Result<syntax::TheoryItem> {
    struct Frame<'t> {
        t: &'t Theory,
        scope: Scope,
        next: usize,
        body: Vec<Decl>,
    }
    let mut seen = Seen::new();
    let start = |t: &Theory, seen: &mut Seen| -> Result<Scope> {
        seen.insert(t.path().clone(), 0);
        lib.new_scope(t.path(), ns.clone(), seen)
    };
    let mut stack = vec![Frame { t: root, scope: start(root, &mut seen)?, next: 0, body: Vec::new() }];
    loop {
        let Some(top) = stack.last_mut() else { unreachable!("the root is popped last") };
        let t = top.t;
        if let Some(d) = t.declarations().get(top.next) {
            let i = top.next;
            top.next += 1;
            match d {
                Declaration::Constant(c) => {
                    top.body.push(Decl::Constant(constant(&top.scope, ns, c)?));
                    seen.insert(t.path().clone(), i + 1);
                    lib.advance(&mut top.scope, c, &seen)?;
                }
                Declaration::Include(p) => {
                    let text = Render { scope: &top.scope }.module(p)?;
                    let back = parse_object(&top.scope, &text, Pos::START, &[])?;
                    if *back.term() != Term::Module(p.clone()) {
                        return Err(print_error(format!("the include of {p} prints as `{text}`, which reads back as {}", back.term())));
                    }
                    top.body.push(Decl::Include(obj_text(text)?));
                    seen.insert(t.path().clone(), i + 1);
                    lib.extend_scope(&mut top.scope, p, &seen)?;
                }
                Declaration::Rule(r) => {
                    let text = object(&top.scope, &ParseResult::plain(r.term().clone()))?;
                    top.body.push(Decl::Rule(obj_text(text)?));
                    seen.insert(t.path().clone(), i + 1);
                    lib.add_rule_to_scope(&mut top.scope, r, &seen);
                }
                Declaration::Theory(n) => {
                    let nt = lib.theory(n).ok_or_else(|| print_error(format!("nested theory {n} is not in the library")))?;
                    // the parent is seen up to the nested theory
                    seen.insert(t.path().clone(), i);
                    let scope = start(nt, &mut seen)?;
                    stack.push(Frame { t: nt, scope, next: 0, body: Vec::new() });
                }
            }
            continue;
        }
        let Some(done) = stack.pop() else { unreachable!("the stack is not empty") };
        let mut body = done.body;
        for m in done.t.metadata() {
            body.push(match m {
                Metadatum::Meta(k, v) => Decl::Meta { key: word(k.to_string())?, value: obj_text(object(&done.scope, &ParseResult::plain(v.clone()))?)? },
                Metadatum::Tag(k) => Decl::Tag(word(k.to_string())?),
            });
        }
        seen.remove(done.t.path());
        let name = match (done.t.parent(), stack.last()) {
            (Some(p), Some(_)) => done.t.path().name().drop_prefix(p.name().len()),
            _ => done.t.path().name().clone(),
        };
        let meta = done.t.meta().map(|m| word(m.to_string())).transpose()?;
        let item = syntax::TheoryItem { name: word(name.to_path())?, meta, body };
        match stack.last_mut() {
            Some(parent) => {
                parent.body.push(Decl::Theory(item));
                let next = parent.next;
                seen.insert(parent.t.path().clone(), next);
            }
            None => return Ok(item),
        }
    }
}

fn constant(scope: &Scope, ns: &NamespaceMap, c: &Constant) -> Result<syntax::ConstantItem> {
    constant_item(scope, ns, c).map_err(|e| e.context(format!("constant {}", c.path())))
}

fn constant_item(scope: &Scope, ns: &NamespaceMap, c: &Constant) -> Result<syntax::ConstantItem> {
    let name = c.path().name().to_path();
    let back = LocalName::parse(&name, ns)?;
    if back != *c.path().name() {
        return Err(print_error(format!("the name {} of {} does not read back", name, c.path())));
    }
    let mut components = Vec::new();
    if let Some(r) = c.tp() {
        components.push(Component::Type(obj_text(object(scope, r)?)?));
    }
    if let Some(r) = c.df() {
        components.push(Component::Definiens(obj_text(object(scope, r)?)?));
    }
    for (n, f) in [(c.notation(), Component::Notation as fn(ObjectText) -> Component), (c.presentation_notation(), Component::PresentationNotation)] {
        if let Some(n) = n {
            let text = n.to_string();
            if Notation::parse(&text, ns).ok().as_ref() != Some(n) {
                return Err(print_error(format!("the notation `{text}` of {} does not read back", c.path())));
            }
            components.push(f(obj_text(text)?));
        }
    }
    if !c.aliases().is_empty() {
        let text: Vec<String> = c.aliases().iter().map(LocalName::to_path).collect();
        components.push(Component::Alias(obj_text(text.join(" "))?));
    }
    if let Some(r) = c.role() {
        components.push(Component::Role(obj_text(r)?));
    }
    for m in c.metadata() {
        components.push(match m {
            Metadatum::Meta(k, v) => Component::Meta { key: word(k.to_string())?, value: obj_text(object(scope, &ParseResult::plain(v.clone()))?)? },
            Metadatum::Tag(k) => Component::Tag(word(k.to_string())?),
        });
    }
    syntax::ConstantItem::new(word(name)?, components)
}
