//! The library: theories elaborated from documents or built as objects, and
//! the scope in which the objects of a declaration are read
//! (doc/language/modules.md, doc/language/declarations.md;
//! `api/parser/StructureParser.scala`, `api/parser/ProcessingInstruction.scala`,
//! `api/libraries/Lookup.scala`).
//!
//! Elaborating a document processes its items in order. `namespace` sets the
//! namespace of the following theories, `import` defines a CURIE prefix and
//! `fixmeta` the default meta-theory. A theory is elaborated declaration by
//! declaration: the components of a constant are read as objects in the scope
//! of the theory at that point, which consists of the meta-theory, the
//! theories included so far (both transitively), the enclosing theory of a
//! nested theory, and the declarations before the constant. The scope
//! provides the notations (each constant can also be referred to by its name
//! and its aliases), the lexer extensions of the rules, the notation
//! extension (LF's higher-order abstract syntax where the rule `LFHOAS` is
//! visible) and the roles of constants.
//!
//! Elaboration reads; it does not type-check and does not check that a
//! symbol that an object refers to by URI exists. What it refuses is what
//! reading refuses: text that does not read with the notations in scope, a
//! name declared twice, a theory declared twice, an include or meta-theory
//! that is not loaded, a cyclic include, and nesting beyond [`Limits`].
//!
//! [`Library::object_scope`] gives the scope at the end of a theory, built
//! once and reused for every object read or printed in it.
//!
//! A theory in which an error occurs is not added to the library; the
//! elaboration of the document continues with the next item, so that one
//! report lists the errors of all theories. Theories can be registered
//! without being elaborated ([`Library::register_source`]); a registered
//! theory is elaborated when a theory elaborated later refers to it.

use std::collections::{HashMap, HashSet};
use std::path::{Path as FsPath, PathBuf};
use std::rc::Rc;

use crate::error::{Error, ErrorKind, Pos, Result};
use crate::lexer::LexerRule;
use crate::notation::{Marker, Notation};
use crate::objparser::{parse_object, ParseResult};
use crate::paths;
use crate::rules::{interpret, RuleKind};
use crate::scanner::{ParsingRule, RuleTable};
use crate::syntax::{self, Component, Decl, DocItem, Document, ObjectText, Word};
use crate::term::Term;
use crate::uri::{DPath, GlobalName, LNStep, LocalName, MPath, NamespaceMap, Path};
use crate::Limits;

/// Limits on the declarations of theories that are seen: a theory in the
/// map contributes only its first declarations (the state while it is
/// elaborated or printed).
pub(crate) type Seen = HashMap<MPath, usize>;

/// A theory.
#[derive(Clone, Debug, PartialEq)]
pub struct Theory {
    path: MPath,
    meta: Option<MPath>,
    parent: Option<MPath>,
    decls: Vec<Declaration>,
    metadata: Vec<Metadatum>,
    document_rules: Vec<RuleDecl>,
}

impl Theory {
    /// A theory without meta-theory and declarations, to be built with the
    /// `with_` methods and added with [`Library::add_theory`].
    pub fn new(path: MPath) -> Theory {
        Theory { path, meta: None, parent: None, decls: Vec::new(), metadata: Vec::new(), document_rules: Vec::new() }
    }

    /// The same theory with a meta-theory.
    pub fn with_meta(mut self, meta: MPath) -> Theory {
        self.meta = Some(meta);
        self
    }

    /// The same theory with one more declaration at the end.
    pub fn with_declaration(mut self, d: Declaration) -> Theory {
        self.decls.push(d);
        self
    }

    /// The same theory with one more metadatum.
    pub fn with_metadatum(mut self, m: Metadatum) -> Theory {
        self.metadata.push(m);
        self
    }

    /// The URI.
    pub fn path(&self) -> &MPath {
        &self.path
    }

    /// The meta-theory.
    pub fn meta(&self) -> Option<&MPath> {
        self.meta.as_ref()
    }

    /// The enclosing theory of a nested theory.
    pub fn parent(&self) -> Option<&MPath> {
        self.parent.as_ref()
    }

    /// The declarations in order.
    pub fn declarations(&self) -> &[Declaration] {
        &self.decls
    }

    /// The constants in order.
    pub fn constants(&self) -> impl Iterator<Item = &Constant> {
        self.decls.iter().filter_map(|d| match d {
            Declaration::Constant(c) => Some(c),
            _ => None,
        })
    }

    /// The metadata of the theory.
    pub fn metadata(&self) -> &[Metadatum] {
        &self.metadata
    }

    /// The rules declared at document level before the theory; their lexer extensions apply to the objects of the theory.
    pub fn document_rules(&self) -> &[RuleDecl] {
        &self.document_rules
    }
}

/// A declaration in a theory.
#[derive(Clone, Debug, PartialEq)]
#[non_exhaustive]
#[allow(clippy::large_enum_variant)] // most declarations are constants
pub enum Declaration {
    /// A constant.
    Constant(Constant),
    /// An include of a theory.
    Include(MPath),
    /// A rule.
    Rule(RuleDecl),
    /// A nested theory (elaborated as a theory of its own with this theory as parent).
    Theory(MPath),
}

/// A rule declaration: the object and what it does to reading.
#[derive(Clone, Debug, PartialEq)]
pub struct RuleDecl {
    term: Term,
    kind: RuleKind,
}

impl RuleDecl {
    /// The rule of an object: a module reference, or an application of one to arguments (see [`crate::rules`]).
    pub fn new(term: Term) -> Result<RuleDecl> {
        let kind = interpret(&term)?;
        Ok(RuleDecl { term, kind })
    }

    /// The object.
    pub fn term(&self) -> &Term {
        &self.term
    }

    /// What the rule does to reading.
    pub fn kind(&self) -> &RuleKind {
        &self.kind
    }
}

/// A metadatum: a key with a value, or a tag.
#[derive(Clone, Debug, PartialEq)]
#[non_exhaustive]
pub enum Metadatum {
    /// `meta KEY VALUE`.
    Meta(GlobalName, Term),
    /// `tag KEY`.
    Tag(GlobalName),
}

/// A constant.
#[derive(Clone, Debug, PartialEq)]
pub struct Constant {
    path: GlobalName,
    tp: Option<ParseResult>,
    df: Option<ParseResult>,
    notation: Option<Notation>,
    presentation_notation: Option<Notation>,
    aliases: Vec<LocalName>,
    role: Option<String>,
    metadata: Vec<Metadatum>,
}

impl Constant {
    /// A constant without components, to be built with the `with_` methods.
    pub fn new(path: GlobalName) -> Constant {
        Constant { path, tp: None, df: None, notation: None, presentation_notation: None, aliases: Vec::new(), role: None, metadata: Vec::new() }
    }

    /// The same constant with a type.
    pub fn with_type(mut self, tp: impl Into<ParseResult>) -> Constant {
        self.tp = Some(tp.into());
        self
    }

    /// The same constant with a definiens.
    pub fn with_definiens(mut self, df: impl Into<ParseResult>) -> Constant {
        self.df = Some(df.into());
        self
    }

    /// The same constant with a notation.
    pub fn with_notation(mut self, n: Notation) -> Constant {
        self.notation = Some(n);
        self
    }

    /// The same constant with a presentation notation (`##`).
    pub fn with_presentation_notation(mut self, n: Notation) -> Constant {
        self.presentation_notation = Some(n);
        self
    }

    /// The same constant with one more alias.
    pub fn with_alias(mut self, a: LocalName) -> Constant {
        self.aliases.push(a);
        self
    }

    /// The same constant with a role.
    pub fn with_role(mut self, role: impl Into<String>) -> Constant {
        self.role = Some(role.into());
        self
    }

    /// The same constant with one more metadatum.
    pub fn with_metadatum(mut self, m: Metadatum) -> Constant {
        self.metadata.push(m);
        self
    }

    /// The URI.
    pub fn path(&self) -> &GlobalName {
        &self.path
    }

    /// The type as read (with its unknowns and free variables).
    pub fn tp(&self) -> Option<&ParseResult> {
        self.tp.as_ref()
    }

    /// The definiens as read (with its unknowns and free variables).
    pub fn df(&self) -> Option<&ParseResult> {
        self.df.as_ref()
    }

    /// The notation used for reading and printing.
    pub fn notation(&self) -> Option<&Notation> {
        self.notation.as_ref()
    }

    /// The notation given with `##`, kept but not used.
    pub fn presentation_notation(&self) -> Option<&Notation> {
        self.presentation_notation.as_ref()
    }

    /// Alternative names.
    pub fn aliases(&self) -> &[LocalName] {
        &self.aliases
    }

    /// The role.
    pub fn role(&self) -> Option<&str> {
        self.role.as_deref()
    }

    /// Metadata.
    pub fn metadata(&self) -> &[Metadatum] {
        &self.metadata
    }
}

/// A collection of theories.
#[derive(Clone, Debug, Default)]
pub struct Library {
    /// The theories by index; a removed theory leaves `None`.
    theories: Vec<Option<Theory>>,
    index: HashMap<MPath, usize>,
    files: HashMap<MPath, PathBuf>,
    units: Vec<UnitState>,
    pending: HashMap<MPath, usize>,
    /// The position of each constant among the declarations of its theory.
    constants: HashMap<GlobalName, usize>,
    /// The source position of the name of each constant that was read from a document.
    positions: HashMap<GlobalName, Pos>,
    limits: Limits,
    /// The theories being elaborated, each inside the previous one (nested,
    /// or required by it as meta-theory or include).
    elaborating: usize,
}

/// What a printer needs to know about the notations in scope.
#[derive(Clone, Debug, Default)]
pub(crate) struct PrintInfo {
    /// The delimiters of the notations in scope (not the names of constants).
    pub(crate) delims: HashSet<String>,
    /// The first notation of each constant.
    pub(crate) notations: HashMap<GlobalName, Rc<ParsingRule>>,
    /// The delimiter of a notation `1 D 2` with role Type, for typed variables.
    pub(crate) type_delim: Option<String>,
    /// The delimiter of a notation `1 D 2` with role Def, for defined variables.
    pub(crate) def_delim: Option<String>,
}

/// The scope of an object (see the module documentation).
#[derive(Clone, Debug)]
pub(crate) struct Scope {
    pub(crate) theory: MPath,
    pub(crate) ns: NamespaceMap,
    pub(crate) limits: Limits,
    visible: HashSet<MPath>,
    pub(crate) table: Rc<RuleTable>,
    pub(crate) lexers: Vec<LexerRule>,
    roles: HashMap<GlobalName, Option<String>>,
    /// The constants of each name, in the order their theories became visible.
    names: HashMap<LocalName, Vec<GlobalName>>,
    /// The constants whose names have complex steps, by their names without them.
    complex: HashMap<LocalName, Vec<GlobalName>>,
    metas: HashMap<MPath, Option<MPath>>,
    hoas: HashMap<MPath, bool>,
    /// The rules of the theories in scope.
    rules: Vec<RuleKind>,
    pub(crate) print: PrintInfo,
}

impl Scope {
    fn empty(theory: &MPath, ns: NamespaceMap, limits: Limits) -> Scope {
        Scope {
            theory: theory.clone(),
            ns,
            limits,
            visible: HashSet::new(),
            table: Rc::new(RuleTable::default()),
            lexers: Vec::new(),
            roles: HashMap::new(),
            names: HashMap::new(),
            complex: HashMap::new(),
            metas: HashMap::new(),
            hoas: HashMap::new(),
            rules: Vec::new(),
            print: PrintInfo::default(),
        }
    }

    pub(crate) fn hoas_at(&self, level: &MPath) -> bool {
        self.hoas.get(level).copied().unwrap_or(false)
    }

    pub(crate) fn home_meta(&self, m: &MPath) -> Option<MPath> {
        self.metas.get(m).cloned().flatten()
    }

    pub(crate) fn role(&self, c: &GlobalName) -> Option<&str> {
        self.roles.get(c).and_then(|r| r.as_deref())
    }

    pub(crate) fn has_constant(&self, c: &GlobalName) -> bool {
        self.roles.contains_key(c)
    }

    /// `Lookup.resolveName` over the visible theories: in each theory, the
    /// constant of exactly this name, or else those whose names are this
    /// name with complex steps.
    pub(crate) fn resolve_name(&self, name: &LocalName) -> Vec<GlobalName> {
        let exact = self.names.get(name).cloned().unwrap_or_default();
        let mut out = exact.clone();
        for g in self.complex.get(name).into_iter().flatten() {
            if !exact.iter().any(|e| e.module() == g.module()) {
                out.push(g.clone());
            }
        }
        out
    }

    fn add_constant(&mut self, c: &Constant) -> Result<()> {
        self.roles.insert(c.path.clone(), c.role.clone());
        self.names.entry(c.path.name().clone()).or_default().push(c.path.clone());
        if c.path.name().steps().iter().any(|s| matches!(s, LNStep::Complex(_))) {
            self.complex.entry(c.path.name().drop_complex()).or_default().push(c.path.clone());
        }
        let table = Rc::make_mut(&mut self.table);
        for (r, unapplied) in parsing_rules(c)? {
            let r = Rc::new(r);
            if !unapplied {
                for m in &r.markers {
                    match m {
                        Marker::Delim(d) | Marker::SeqArg(_, d) | Marker::InstanceName(d) => {
                            self.print.delims.insert(d.matched_text().to_string());
                        }
                        Marker::Var { sep: Some(d), .. } => {
                            self.print.delims.insert(d.matched_text().to_string());
                        }
                        _ => {}
                    }
                }
                if let [Marker::Arg(1), Marker::Delim(d), Marker::Arg(2)] = r.markers.as_slice() {
                    match c.role.as_deref() {
                        Some("Type") if self.print.type_delim.is_none() => self.print.type_delim = Some(d.matched_text().to_string()),
                        Some("Def") if self.print.def_delim.is_none() => self.print.def_delim = Some(d.matched_text().to_string()),
                        _ => {}
                    }
                }
                self.print.notations.entry(r.name.clone()).or_insert_with(|| r.clone());
            }
            table.add(r);
        }
        Ok(())
    }

    fn add_rule(&mut self, kind: &RuleKind) {
        self.rules.push(kind.clone());
        if let Some(l) = LexerRule::of(kind) {
            if !self.lexers.contains(&l) {
                self.lexers.push(l);
                self.lexers.sort_by_key(|l| std::cmp::Reverse(l.priority()));
            }
        }
    }
}

/// The parsing rules of a constant: its name and aliases as notations of
/// infinite precedence (flagged as unapplied), and its notation.
fn parsing_rules(c: &Constant) -> Result<Vec<(ParsingRule, bool)>> {
    let name = c.path.name();
    let mut names: Vec<String> = std::iter::once(name).chain(c.aliases.iter()).map(LocalName::to_path).collect();
    if name.len() > 1 && name.last_simple() == Some("_") {
        names.insert(0, name.init().to_path());
    }
    let mut out = Vec::new();
    for n in names {
        out.push((ParsingRule::new(c.path.clone(), c.aliases.clone(), Rc::new(Notation::name_only(n)))?, true));
    }
    if let Some(n) = &c.notation {
        out.push((ParsingRule::new(c.path.clone(), c.aliases.clone(), Rc::new(n.clone()))?, false));
    }
    Ok(out)
}

/// The outcome of elaborating a document.
#[derive(Debug, Default)]
pub struct Elaboration {
    theories: Vec<MPath>,
    errors: Vec<Error>,
}

impl Elaboration {
    /// The theories added, in order.
    pub fn theories(&self) -> &[MPath] {
        &self.theories
    }

    /// The errors, each attributed to the file if one was given.
    pub fn errors(&self) -> &[Error] {
        &self.errors
    }

    /// Whether there are no errors.
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }

    /// The errors, consuming the outcome.
    pub fn into_errors(self) -> Vec<Error> {
        self.errors
    }

    pub(crate) fn push_error(&mut self, e: Error) {
        self.errors.push(e);
    }
}

/// A theory of a document together with the state of the document before it.
#[derive(Clone, Debug)]
struct Unit {
    ns: NamespaceMap,
    fixmeta: Option<MPath>,
    rules: Vec<RuleDecl>,
    file: Option<PathBuf>,
    theory: syntax::TheoryItem,
}

#[derive(Clone, Debug)]
enum UnitState {
    Pending(Box<Unit>),
    Loading,
    Done(std::result::Result<Vec<MPath>, Error>),
}

/// The theories a unit declares (the theory and its nested theories), without recursion.
fn declared_paths(t: &syntax::TheoryItem, ns: &NamespaceMap, out: &mut Vec<MPath>) -> Result<()> {
    let mut stack: Vec<(&syntax::TheoryItem, Option<MPath>)> = vec![(t, None)];
    while let Some((t, parent)) = stack.pop() {
        let name = LocalName::parse(t.name.as_str(), ns).map_err(|e| e.or_at(t.name.pos()))?;
        let path = match &parent {
            Some(p) => p.doc().module(p.name().join(&name)),
            None => ns.base().doc().module(name),
        };
        out.push(path.clone());
        for d in t.body.iter().rev() {
            if let Decl::Theory(n) = d {
                stack.push((n, Some(path.clone())));
            }
        }
    }
    Ok(())
}

fn attribute(e: Error, file: Option<&FsPath>) -> Error {
    match file {
        Some(f) => e.in_file(f),
        None => e,
    }
}

/// Whether a name can be written as one word that reads back as the name.
fn printable_name(name: &LocalName) -> Result<()> {
    let text = name.to_path();
    Word::new(text.clone())?;
    if LocalName::parse_plain(&text)? != *name {
        return Err(Error::new(ErrorKind::Uri, format!("the name {text} does not read back as itself")));
    }
    Ok(())
}

/// Whether a symbol URI can be written as a word (a metadata key).
fn printable_uri(g: &GlobalName) -> Result<()> {
    let text = g.to_string();
    Word::new(text.clone())?;
    if GlobalName::parse_plain(&text)? != *g {
        return Err(Error::new(ErrorKind::Uri, format!("the URI {text} does not read back as itself")));
    }
    Ok(())
}

impl Library {
    /// An empty library with the default limits.
    pub fn new() -> Library {
        Library::default()
    }

    /// An empty library with the given limits for the documents and objects it reads and the theories it adds.
    pub fn with_limits(limits: Limits) -> Library {
        Library { limits, ..Library::default() }
    }

    /// The limits.
    pub fn limits(&self) -> Limits {
        self.limits
    }

    /// The theory of a URI, if it is elaborated.
    pub fn theory(&self, p: &MPath) -> Option<&Theory> {
        self.index.get(p).and_then(|&i| self.theories[i].as_ref())
    }

    /// The elaborated theories in the order they were added. A theory that
    /// is only registered ([`Library::register_source`]) is not among them
    /// until a theory that refers to it is elaborated.
    pub fn theories(&self) -> impl Iterator<Item = &Theory> {
        self.theories.iter().flatten()
    }

    /// The file a theory was read from, if known.
    pub fn file_of(&self, p: &MPath) -> Option<&FsPath> {
        self.files.get(p).map(PathBuf::as_path)
    }

    /// The constant of a URI.
    pub fn constant(&self, p: &GlobalName) -> Option<&Constant> {
        match self.theory(p.module())?.decls.get(*self.constants.get(p)?)? {
            Declaration::Constant(c) => Some(c),
            _ => None,
        }
    }

    /// The source position of the name of a constant that was read from a document.
    pub fn position_of(&self, p: &GlobalName) -> Option<Pos> {
        self.positions.get(p).copied()
    }

    /// Reads a source text and elaborates it; the namespace before any
    /// `namespace` instruction is `base`, and errors are attributed to `file`.
    pub fn add_source(&mut self, text: &str, base: &DPath, file: Option<&FsPath>) -> Elaboration {
        match Document::parse_with_limits(text, self.limits) {
            Ok(doc) => self.add_document(&doc, base, file),
            Err(e) => Elaboration { theories: vec![], errors: vec![attribute(e, file)] },
        }
    }

    /// Registers the theories of a source text without elaborating them: each
    /// is elaborated when a theory elaborated later refers to it (as a
    /// meta-theory or an include). Returns the errors of reading the text and
    /// of registering its theories; the errors of elaborating a theory are
    /// reported where it is referred to.
    pub fn register_source(&mut self, text: &str, base: &DPath, file: Option<&FsPath>) -> Vec<Error> {
        match Document::parse_with_limits(text, self.limits) {
            Ok(doc) => {
                let mut errors = Vec::new();
                self.register_document(&doc, base, file, &mut errors);
                errors
            }
            Err(e) => vec![attribute(e, file)],
        }
    }

    /// Adds a theory built as objects instead of read from a document. It is
    /// accepted under the conditions that elaboration ensures for a theory
    /// that it reads, and so that [`Library::print_theories`] can write it:
    ///
    /// - its URI is not declared yet, and its name can be written;
    /// - its meta-theory and includes are in the library (registered
    ///   theories are elaborated), and no include is cyclic;
    /// - it has no nested theory (unsupported);
    /// - every constant belongs to it, has a new name, and its name, aliases,
    ///   role and metadata keys can be written;
    /// - every notation yields a parsing rule;
    /// - no object nests more than [`Limits::depth`] levels.
    ///
    /// Errors about a constant name it. On an error, nothing is added. The
    /// objects are not type-checked, and whether they can be printed with
    /// the notations in scope is found when they are printed.
    pub fn add_theory(&mut self, theory: Theory) -> Result<MPath> {
        let path = theory.path.clone();
        let failed = self.pending.get(&path).is_some_and(|&u| matches!(self.units[u], UnitState::Done(Err(_))));
        if self.index.contains_key(&path) || (self.pending.contains_key(&path) && !failed) {
            return Err(Error::new(ErrorKind::Structure, format!("theory {path} is already declared")));
        }
        printable_name(path.name()).map_err(|e| e.context(format!("theory {path}")))?;
        let unpositioned = Error::unpositioned;
        if let Some(m) = &theory.meta {
            self.require(m, Pos::START, "meta-theory").map_err(unpositioned)?;
        }
        let depth = self.limits.depth();
        let check_depth = |t: &Term| -> Result<()> {
            if t.depth() > depth.saturating_add(1) {
                return Err(Error::new(ErrorKind::Limit, format!("an object nests more than {depth} levels")));
            }
            Ok(())
        };
        let check_metadata = |ms: &[Metadatum]| -> Result<()> {
            for m in ms {
                match m {
                    Metadatum::Meta(k, v) => {
                        printable_uri(k)?;
                        check_depth(v)?;
                    }
                    Metadatum::Tag(k) => printable_uri(k)?,
                }
            }
            Ok(())
        };
        check_metadata(&theory.metadata).map_err(|e| e.context(format!("theory {path}")))?;
        let mut names: HashSet<LocalName> = HashSet::new();
        for d in &theory.decls {
            match d {
                Declaration::Include(p) => {
                    self.require(p, Pos::START, "included theory").map_err(unpositioned)?;
                    if *p == path || self.closure(p).contains(&path) {
                        return Err(Error::new(ErrorKind::Structure, format!("cyclic include of {p}")));
                    }
                }
                Declaration::Rule(r) => check_depth(&r.term)?,
                Declaration::Theory(n) => return Err(Error::new(ErrorKind::Unsupported, format!("theory {path}: the nested theory {n} cannot be added as objects"))),
                Declaration::Constant(c) => {
                    let at = |e: Error| e.context(format!("constant {}", c.path));
                    if *c.path.module() != path {
                        return Err(at(Error::new(ErrorKind::Structure, format!("it does not belong to {path}"))));
                    }
                    if !names.insert(c.path.name().clone()) {
                        return Err(at(Error::new(ErrorKind::Structure, format!("a declaration for the name {} already exists in {path}", c.path.name()))));
                    }
                    printable_name(c.path.name()).map_err(at)?;
                    for a in &c.aliases {
                        printable_name(a).map_err(at)?;
                    }
                    if let Some(r) = &c.role {
                        ObjectText::new(r.clone()).map_err(at)?;
                    }
                    for r in c.tp.iter().chain(c.df.iter()) {
                        check_depth(r.term()).map_err(at)?;
                    }
                    check_metadata(&c.metadata).map_err(at)?;
                    parsing_rules(c).map_err(at)?;
                }
            }
        }
        for (at, d) in theory.decls.iter().enumerate() {
            if let Declaration::Constant(c) = d {
                self.constants.insert(c.path.clone(), at);
            }
        }
        self.index.insert(path.clone(), self.theories.len());
        self.theories.push(Some(theory));
        Ok(path)
    }

    /// Elaborates a document; the namespace before any `namespace`
    /// instruction is `base`, and errors are attributed to `file`.
    pub fn add_document(&mut self, doc: &Document, base: &DPath, file: Option<&FsPath>) -> Elaboration {
        let mut out = Elaboration::default();
        let units = self.register_document(doc, base, file, &mut out.errors);
        for i in units {
            match self.load_unit(i) {
                Ok(ps) => out.theories.extend(ps),
                Err(e) => out.errors.push(e),
            }
        }
        out
    }

    /// Splits a document into units and registers them as pending; returns their indices.
    pub(crate) fn register_document(&mut self, doc: &Document, base: &DPath, file: Option<&FsPath>, errors: &mut Vec<Error>) -> Vec<usize> {
        let mut ns = NamespaceMap::empty().rebase(Path::Doc(base.clone()));
        let mut fixmeta: Option<MPath> = None;
        let mut rules: Vec<RuleDecl> = Vec::new();
        let mut out = Vec::new();
        for item in &doc.items {
            let r: Result<()> = (|| {
                match item {
                    DocItem::Namespace(u) => {
                        let d = Path::parse_doc(u.as_str(), &ns).map_err(|e| e.or_at(u.pos()))?;
                        ns = ns.rebase(Path::Doc(d));
                    }
                    DocItem::Import { prefix, uri } => {
                        ns = ns.add(prefix.as_str(), &crate::uri::Uri::parse(uri.as_str()));
                    }
                    DocItem::FixMeta(u) => {
                        fixmeta = Some(Path::parse_module(u.as_str(), &ns).map_err(|e| e.or_at(u.pos()))?);
                    }
                    DocItem::Rule(u) => {
                        // `InterpretationInstruction.parse`: the rule is a module; NotationBasedParser.getRules uses the lexer extensions among document rules
                        let p = Path::parse_module(u.as_str(), &ns).map_err(|e| e.or_at(u.pos()))?;
                        rules.push(RuleDecl::new(Term::Module(p)).map_err(|e| e.or_at(u.pos()))?);
                    }
                    DocItem::Comment(_) | DocItem::Text(_) => {}
                    DocItem::Theory(t) => {
                        let mut paths = Vec::new();
                        declared_paths(t, &ns, &mut paths)?;
                        let mut seen = HashSet::new();
                        for p in &paths {
                            let failed = self.pending.get(p).is_some_and(|&u| matches!(self.units[u], UnitState::Done(Err(_))));
                            if !seen.insert(p) || self.index.contains_key(p) || (self.pending.contains_key(p) && !failed) {
                                return Err(Error::at(ErrorKind::Structure, t.name.pos(), format!("theory {p} is already declared")));
                            }
                        }
                        let i = self.units.len();
                        self.units.push(UnitState::Pending(Box::new(Unit { ns: ns.clone(), fixmeta: fixmeta.clone(), rules: rules.clone(), file: file.map(FsPath::to_path_buf), theory: t.clone() })));
                        for p in paths {
                            self.pending.insert(p, i);
                        }
                        out.push(i);
                    }
                }
                Ok(())
            })();
            if let Err(e) = r {
                errors.push(attribute(e, file));
            }
        }
        out
    }

    /// Elaborates a registered unit unless it is elaborated already.
    pub(crate) fn load_unit(&mut self, i: usize) -> std::result::Result<Vec<MPath>, Error> {
        let unit = match std::mem::replace(&mut self.units[i], UnitState::Loading) {
            UnitState::Pending(u) => u,
            UnitState::Loading => {
                return Err(Error::new(ErrorKind::Structure, "cyclic dependency between theories"));
            }
            UnitState::Done(r) => {
                self.units[i] = UnitState::Done(r.clone());
                return r;
            }
        };
        let mut added = Vec::new();
        let r = self.elaborate_theory(&unit.theory, &unit.ns, unit.fixmeta.as_ref(), &unit.rules, None, &mut added);
        let r = match r {
            Ok(_) => {
                if let Some(f) = &unit.file {
                    for p in &added {
                        self.files.insert(p.clone(), f.clone());
                    }
                }
                Ok(added)
            }
            Err(e) => {
                for p in added.iter().rev() {
                    self.remove(p);
                }
                Err(attribute(e, unit.file.as_deref()))
            }
        };
        self.units[i] = UnitState::Done(r.clone());
        r
    }

    /// Makes sure a theory is elaborated if it is declared in a registered unit.
    fn require(&mut self, p: &MPath, pos: Pos, what: &str) -> Result<()> {
        if self.index.contains_key(p) {
            return Ok(());
        }
        match self.pending.get(p).copied() {
            Some(i) => match self.load_unit(i) {
                Ok(_) if self.index.contains_key(p) => Ok(()),
                Ok(_) => Err(Error::at(ErrorKind::Unresolved, pos, format!("{what} {p} is not loaded"))),
                Err(e) => {
                    let at = match (e.file(), e.pos()) {
                        (Some(f), Some(q)) => format!(" ({}:{q})", f.display()),
                        (Some(f), None) => format!(" ({})", f.display()),
                        _ => String::new(),
                    };
                    Err(Error::at(ErrorKind::Unresolved, pos, format!("{what} {p} could not be loaded because of the error reported for it{at}")))
                }
            },
            None => Err(Error::at(ErrorKind::Unresolved, pos, format!("{what} {p} is not loaded"))),
        }
    }

    fn remove(&mut self, p: &MPath) {
        if let Some(i) = self.index.remove(p) {
            if let Some(t) = self.theories[i].take() {
                for c in t.constants() {
                    self.constants.remove(&c.path);
                    self.positions.remove(&c.path);
                }
            }
        }
    }

    fn theory_mut(&mut self, p: &MPath) -> Result<&mut Theory> {
        let i = *self.index.get(p).ok_or_else(|| Error::new(ErrorKind::Unresolved, format!("theory {p} is not in the library")))?;
        self.theories[i].as_mut().ok_or_else(|| Error::new(ErrorKind::Unresolved, format!("theory {p} is not in the library")))
    }

    /// The theories visible from a theory: itself, its meta-theory, its includes and its parent, transitively.
    pub fn closure(&self, p: &MPath) -> Vec<MPath> {
        self.closure_limited(p, &Seen::new())
    }

    /// The closure in depth-first order, where a theory in `seen` contributes only its first declarations.
    fn closure_limited(&self, p: &MPath, seen: &Seen) -> Vec<MPath> {
        let mut out = Vec::new();
        let mut visited = HashSet::new();
        let mut stack = vec![p.clone()];
        while let Some(p) = stack.pop() {
            if !visited.insert(p.clone()) {
                continue;
            }
            out.push(p.clone());
            let Some(t) = self.theory(&p) else { continue };
            let mut next: Vec<MPath> = t.meta.iter().cloned().collect();
            for d in self.decls_limited(t, seen) {
                if let Declaration::Include(i) = d {
                    next.push(i.clone());
                }
            }
            next.extend(t.parent.iter().cloned());
            stack.extend(next.into_iter().rev());
        }
        out
    }

    /// The declarations of a theory, restricted by `seen`.
    fn decls_limited<'a>(&self, t: &'a Theory, seen: &Seen) -> &'a [Declaration] {
        match seen.get(&t.path) {
            Some(&n) => &t.decls[..n.min(t.decls.len())],
            None => &t.decls,
        }
    }

    fn has_hoas(&self, level: &MPath, seen: &Seen) -> bool {
        self.closure_limited(level, seen).iter().filter_map(|q| self.theory(q)).flat_map(|t| self.decls_limited(t, seen)).any(|d| matches!(d, Declaration::Rule(r) if r.kind == RuleKind::Hoas))
    }

    /// Records whether the notation extension at a level is LF's.
    fn level(&self, scope: &mut Scope, level: &MPath, seen: &Seen) {
        if level == &scope.theory {
            let h = scope.rules.contains(&RuleKind::Hoas);
            scope.hoas.insert(level.clone(), h);
        } else if !scope.hoas.contains_key(level) {
            let h = self.has_hoas(level, seen);
            scope.hoas.insert(level.clone(), h);
        }
    }

    /// The scope of a theory at the point given by `seen`.
    pub(crate) fn new_scope(&self, theory: &MPath, ns: NamespaceMap, seen: &Seen) -> Result<Scope> {
        let mut scope = Scope::empty(theory, ns, self.limits);
        if let Some(t) = self.theory(theory) {
            for r in &t.document_rules {
                if let Some(l) = LexerRule::of(&r.kind) {
                    if !scope.lexers.contains(&l) {
                        scope.lexers.push(l);
                    }
                }
            }
        }
        self.extend_scope(&mut scope, theory, seen)?;
        Ok(scope)
    }

    /// Adds the theories visible from `from` that the scope does not have yet.
    pub(crate) fn extend_scope(&self, scope: &mut Scope, from: &MPath, seen: &Seen) -> Result<()> {
        let mut levels = vec![scope.theory.clone()];
        for p in self.closure_limited(from, seen) {
            if !scope.visible.insert(p.clone()) {
                continue;
            }
            let Some(t) = self.theory(&p) else { continue };
            scope.metas.insert(p.clone(), t.meta.clone());
            levels.extend(t.meta.iter().cloned());
            for d in self.decls_limited(t, seen) {
                match d {
                    Declaration::Constant(c) => {
                        scope.add_constant(c)?;
                        levels.extend(c.notation.as_ref().and_then(|n| n.meta()).cloned());
                    }
                    Declaration::Rule(r) => scope.add_rule(&r.kind),
                    _ => {}
                }
            }
        }
        scope.lexers.sort_by_key(|l| std::cmp::Reverse(l.priority()));
        for l in levels {
            self.level(scope, &l, seen);
        }
        Ok(())
    }

    /// Adds a constant of the scope's theory to the scope, as elaboration does after each constant.
    pub(crate) fn advance(&self, scope: &mut Scope, c: &Constant, seen: &Seen) -> Result<()> {
        scope.add_constant(c)?;
        if let Some(m) = c.notation.as_ref().and_then(|n| n.meta()) {
            self.level(scope, m, seen);
        }
        Ok(())
    }

    /// Adds a rule of the scope's theory to the scope.
    pub(crate) fn add_rule_to_scope(&self, scope: &mut Scope, r: &RuleDecl, seen: &Seen) {
        scope.add_rule(&r.kind);
        let t = scope.theory.clone();
        self.level(scope, &t, seen);
    }

    /// The scope at the end of a theory: what reading and printing an object of the theory see.
    pub fn object_scope(&self, theory: &MPath) -> Result<ObjectScope> {
        let t = self.theory(theory).ok_or_else(|| Error::new(ErrorKind::Unresolved, format!("theory {theory} is not in the library")))?;
        let ns = NamespaceMap::empty().rebase(Path::Doc(t.path.doc().clone()));
        Ok(ObjectScope { scope: self.new_scope(theory, ns, &Seen::new())? })
    }

    /// Elaborates a theory; theories elaborated inside one another (nested,
    /// or required as meta-theory or include before they were elaborated)
    /// may be at most [`Limits::depth`] deep.
    fn elaborate_theory(&mut self, t: &syntax::TheoryItem, ns: &NamespaceMap, fixmeta: Option<&MPath>, doc_rules: &[RuleDecl], parent: Option<&MPath>, added: &mut Vec<MPath>) -> Result<MPath> {
        if self.elaborating >= self.limits.depth() {
            return Err(too_deep(t, self.limits));
        }
        self.elaborating += 1;
        let r = self.elaborate_theory_body(t, ns, fixmeta, doc_rules, parent, added);
        self.elaborating -= 1;
        r
    }

    // `elaborate_theory_body` and the functions it calls where theories are
    // required (`require`, `load_unit`) are on the recursion of elaboration;
    // they leave the work to helpers so that a level costs little stack.

    fn elaborate_theory_body(&mut self, t: &syntax::TheoryItem, ns: &NamespaceMap, fixmeta: Option<&MPath>, doc_rules: &[RuleDecl], parent: Option<&MPath>, added: &mut Vec<MPath>) -> Result<MPath> {
        let (path, meta) = self.theory_header(t, ns, fixmeta, parent)?;
        if let Some(m) = &meta {
            self.require(m, t.meta.as_ref().map_or(t.name.pos(), |w| w.pos()), "meta-theory")?;
        }
        let mut state = self.open_theory(path, meta, ns, doc_rules, parent, added)?;
        for d in &t.body {
            match d {
                Decl::Theory(nested) => {
                    let n = self.elaborate_theory(nested, &state.ns, fixmeta, doc_rules, Some(&state.path), added)?;
                    self.theory_mut(&state.path)?.decls.push(Declaration::Theory(n));
                }
                Decl::Include(text) => {
                    let p = include_target(&state.scope, text)?;
                    self.require(&p, text.pos(), "included theory")?;
                    self.add_include(&mut state, p, text.pos())?;
                }
                d => self.elaborate_decl(&mut state, d)?,
            }
        }
        Ok(state.path)
    }

    /// The URI and the meta-theory of a theory to be elaborated.
    fn theory_header(&self, t: &syntax::TheoryItem, ns: &NamespaceMap, fixmeta: Option<&MPath>, parent: Option<&MPath>) -> Result<(MPath, Option<MPath>)> {
        let name = LocalName::parse(t.name.as_str(), ns).map_err(|e| e.or_at(t.name.pos()))?;
        let path = match parent {
            Some(p) => p.doc().module(p.name().join(&name)),
            None => ns.base().doc().module(name),
        };
        if self.index.contains_key(&path) {
            return Err(Error::at(ErrorKind::Structure, t.name.pos(), format!("theory {path} is already declared")));
        }
        let meta = match &t.meta {
            // `readMPath(tpath)`: the meta-theory is resolved against the theory being declared
            Some(m) => Some(Path::parse_module(m.as_str(), &ns.rebase(Path::Module(path.clone()))).map_err(|e| e.or_at(m.pos()))?),
            None => fixmeta.cloned(),
        };
        Ok((path, meta))
    }

    /// Adds the empty theory and the state for elaborating its body.
    fn open_theory(&mut self, path: MPath, meta: Option<MPath>, ns: &NamespaceMap, doc_rules: &[RuleDecl], parent: Option<&MPath>, added: &mut Vec<MPath>) -> Result<Box<Body>> {
        self.index.insert(path.clone(), self.theories.len());
        self.theories.push(Some(Theory { path: path.clone(), meta, parent: parent.cloned(), decls: vec![], metadata: vec![], document_rules: doc_rules.to_vec() }));
        added.push(path.clone());
        // objects, notations and metadata keys are read with the namespace map of the document (`ParserState.namespaces`)
        let scope = self.new_scope(&path, ns.clone(), &Seen::new())?;
        Ok(Box::new(Body { scope, names: HashSet::new(), ns: ns.clone(), path }))
    }

    /// Adds an include of a theory that is elaborated already.
    fn add_include(&mut self, b: &mut Body, p: MPath, pos: Pos) -> Result<()> {
        if p == b.path || self.closure(&p).contains(&b.path) {
            return Err(Error::at(ErrorKind::Structure, pos, format!("cyclic include of {p}")));
        }
        self.theory_mut(&b.path)?.decls.push(Declaration::Include(p.clone()));
        self.extend_scope(&mut b.scope, &p, &Seen::new())
    }
}

#[cold]
fn too_deep(t: &syntax::TheoryItem, limits: Limits) -> Error {
    Error::at(ErrorKind::Limit, t.name.pos(), format!("more than {} theories are elaborated inside one another (nested, or required before they were elaborated)", limits.depth()))
}

/// The theory that an include names.
fn include_target(scope: &Scope, text: &ObjectText) -> Result<MPath> {
    let r = parse_object(scope, text.as_str(), text.pos(), &[])?;
    match (r.term(), r.is_plain()) {
        (Term::Module(p), true) => Ok(p.clone()),
        _ => Err(Error::at(ErrorKind::Unsupported, text.pos(), format!("only includes of named theories are supported, found {}", r.term()))),
    }
}

/// The state of elaborating the body of a theory.
struct Body {
    scope: Scope,
    names: HashSet<LocalName>,
    ns: NamespaceMap,
    path: MPath,
}

impl Library {
    /// Elaborates a declaration other than a nested theory.
    fn elaborate_decl(&mut self, b: &mut Body, d: &Decl) -> Result<()> {
        let seen = Seen::new();
        let (scope, body_ns, path) = (&mut b.scope, &b.ns, &b.path);
        match d {
            Decl::Constant(c) => {
                let pos = c.name().pos();
                let name = LocalName::parse(c.name().as_str(), body_ns).map_err(|e| e.or_at(pos))?;
                if !b.names.insert(name.clone()) {
                    return Err(Error::at(ErrorKind::Structure, pos, format!("a declaration for the name {name} already exists in {path}")));
                }
                let k = elaborate_constant(scope, body_ns, path.symbol(name), c)?;
                self.advance(scope, &k, &seen).map_err(|e| e.or_at(pos))?;
                let cp = k.path.clone();
                let decls = &mut self.theory_mut(path)?.decls;
                let at = decls.len();
                decls.push(Declaration::Constant(k));
                self.positions.insert(cp.clone(), pos);
                self.constants.insert(cp, at);
            }
            Decl::Rule(text) => {
                let r = parse_object(scope, text.as_str(), text.pos(), &[])?;
                if !r.is_plain() {
                    return Err(Error::at(ErrorKind::Structure, text.pos(), "can only interpret plain terms as rules"));
                }
                let rule = RuleDecl::new(r.into_term()).map_err(|e| e.or_at(text.pos()))?;
                self.add_rule_to_scope(scope, &rule, &seen);
                self.theory_mut(path)?.decls.push(Declaration::Rule(rule));
            }
            Decl::Meta { key, value } => {
                let k = symbol_path(key, body_ns)?;
                let v = parse_object(scope, value.as_str(), value.pos(), &[])?;
                self.theory_mut(path)?.metadata.push(Metadatum::Meta(k, v.into_term()));
            }
            Decl::Tag(key) => {
                let k = symbol_path(key, body_ns)?;
                self.theory_mut(path)?.metadata.push(Metadatum::Tag(k));
            }
            Decl::Comment(_) | Decl::Text(_) | Decl::Theory(_) | Decl::Include(_) => {}
        }
        Ok(())
    }
}

fn elaborate_constant(scope: &Scope, ns: &NamespaceMap, path: GlobalName, c: &syntax::ConstantItem) -> Result<Constant> {
    let mut k = Constant::new(path);
    for comp in c.components() {
        match comp {
            Component::Type(t) => k.tp = Some(parse_object(scope, t.as_str(), t.pos(), &[])?),
            Component::Definiens(t) => k.df = Some(parse_object(scope, t.as_str(), t.pos(), &[])?),
            Component::Notation(t) => k.notation = Some(Notation::parse(t.as_str(), ns).map_err(|e| e.or_at(t.pos()))?),
            Component::PresentationNotation(t) => k.presentation_notation = Some(Notation::parse(t.as_str(), ns).map_err(|e| e.or_at(t.pos()))?),
            Component::Alias(t) => {
                for a in t.as_str().split_whitespace() {
                    k.aliases.push(LocalName::parse(a, ns).map_err(|e| e.or_at(t.pos()))?);
                }
            }
            Component::Role(t) => k.role = Some(t.as_str().to_string()),
            Component::Meta { key, value } => {
                let kp = symbol_path(key, ns)?;
                let v = parse_object(scope, value.as_str(), value.pos(), &[])?;
                k.metadata.push(Metadatum::Meta(kp, v.into_term()));
            }
            Component::Tag(key) => k.metadata.push(Metadatum::Tag(symbol_path(key, ns)?)),
            Component::Comment(_) => {}
        }
    }
    Ok(k)
}

fn symbol_path(w: &Word, ns: &NamespaceMap) -> Result<GlobalName> {
    match Path::parse(w.as_str(), ns).map_err(|e| e.or_at(w.pos()))? {
        Path::Symbol(g) => Ok(g),
        p => Err(Error::at(ErrorKind::Uri, w.pos(), format!("symbol URI expected as metadata key: {p}"))),
    }
}

impl LexerRule {
    /// The lexer extension a rule contributes, if any.
    pub(crate) fn of(k: &RuleKind) -> Option<LexerRule> {
        match k {
            RuleKind::Literal { syn, sem } => Some(LexerRule::Literal { sem: *sem, tp: Term::Sym(syn.clone()) }),
            RuleKind::StringInterpolation { string, concat } => Some(LexerRule::Interpolation { string: Term::Sym(string.clone()), concat: Term::Sym(concat.clone()) }),
            RuleKind::UriLexer => Some(LexerRule::Uri),
            RuleKind::NotationLiteral => Some(LexerRule::Literal { sem: crate::lexer::SemType::Notation, tp: Term::Sym(paths::notation_type()) }),
            _ => None,
        }
    }
}

/// The scope at the end of a theory, for reading and printing any number of
/// objects of that theory without building the scope again (see
/// [`Library::object_scope`]).
#[derive(Clone, Debug)]
pub struct ObjectScope {
    scope: Scope,
}

impl ObjectScope {
    /// The theory.
    pub fn theory(&self) -> &MPath {
        &self.scope.theory
    }

    /// Reads an object; positions in errors count from the start of `text`.
    pub fn parse(&self, text: &str) -> Result<ParseResult> {
        parse_object(&self.scope, text, Pos::START, &[])
    }

    /// Prints an object so that it reads back as itself in this scope: the notations in scope where they read back to the same object, the abstract form otherwise; an object that no text reads back as is an error of kind [`ErrorKind::Print`].
    pub fn print(&self, r: &ParseResult) -> Result<String> {
        crate::printer::object(&self.scope, r)
    }

    /// Prints a term without unknowns and free variables.
    pub fn print_term(&self, t: &Term) -> Result<String> {
        crate::printer::check_depth(&self.scope, t)?;
        self.print(&ParseResult::plain(t.clone()))
    }
}
