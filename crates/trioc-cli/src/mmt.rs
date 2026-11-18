//! The MMT form of a package: what `trion` writes and `trioc` proves from.
//!
//! The form is an MMT archive (<https://uniformal.github.io/>): a manifest
//! and one source file in the surface syntax of MMT. The file declares the
//! meta-theory of trion contracts, `http://trion.dev/meta?Contracts`, over
//! LF (`MMT/urtheories`), and a theory of the package whose meta-theory it
//! is. MMT reads the archive and type-checks every declaration
//! (`build <archive> mmt-omdoc`). The theory of the package holds
//!
//! - the subject: the package, the revision of its texts, the version of the
//!   rules that read them and the bounds of the obligations;
//! - the actors of the system and of the environment;
//! - for each statement, its one contract by responsibility (`A`, `G`):
//!   schematic in the individuals of its parameters, with its timing (when
//!   it applies and when its response must come) and, for an assumption,
//!   the scope of the guarantees that it is distributed to;
//! - every formula that an obligation names, and the statement it belongs to;
//! - the proof obligations, each with its property, its bounded proposition
//!   and the question that proves it.
//!
//! The form is written and read with the `mmt` crate, which reads and
//! writes the MMT language of MMT v27.0.0 without a JVM and models its
//! grammar only: it neither type-checks nor knows any theory of its own. The
//! meta-theory is MMT text, read by that crate over the declarations of LF's
//! notations below; the theory of the package is built as MMT objects
//! (constants whose types and definitions are terms of the meta-theory) and
//! printed with the notations that the theories declare. Writing reads the
//! text back and compares; a form that does not read back as itself is an
//! internal error of trion and is not written. `trioc` reads the form with
//! the same crate and takes the obligations from the objects that it read; a
//! form that does not read, or whose objects are not the ones the meta-theory
//! describes, is refused with the line and column of the declaration.
//!
//! Whether the form is well-typed in LF is MMT's verdict: the tests run every
//! form that trion writes through MMT itself (`crates/trion-cli/tests/mmt_form.rs`).
//! No type check runs when a form is written or read, and none is needed for
//! what trioc takes from it: the reader accepts exactly the shapes that the
//! writer produces.
//!
//! Lists are written balanced (runs of at most eight items joined by a
//! `join` constant), so that reading a form never nests deeper than its
//! formulas and the logarithm of its longest list.
//!
//! The declarations of LF's notations ([`LF`]) are written for trion: they
//! declare the URIs of MMT/urtheories (<https://gl.mathhub.info/MMT/urtheories>)
//! with the notations and roles that the form uses, as that archive declares
//! them, so that MMT reads the form over the real archive. No file of that
//! archive is part of trion; a test compares the two where `.tools/urtheories`
//! is present.

use mmt::rules::hoas_apply;
use mmt::term::{Integer, LitValue, Literal, Term};
use mmt::uri::{DPath, GlobalName, MPath};
use mmt::{Constant, Declaration, Error, Library, Theory};
use serde::Serialize;
use std::collections::BTreeMap;
use std::sync::OnceLock;
use trion_solver::{Atom, Cmp, Formula};
use trion_verification::{ObligationQuestion, ProofObligation, ProofObligations};

/// The source file of the MMT form in the archive that `trion --out` writes.
pub const FILE: &str = "source/specification.mmt";

/// The manifest of the archive.
pub const MANIFEST: &str = "META-INF/MANIFEST.MF";

/// The namespace of the meta-theory.
const META: &str = "http://trion.dev/meta";

/// The declarations of LF that the form uses, written for trion: MMT's
/// brackets (`mmt?mmt`), LF's types, kinds, application, λ, Π and function
/// types with their notations and roles, and the rule `LFHOAS` by which
/// notations build LF applications. The URIs, notations and roles are those
/// of MMT/urtheories (`source/meta.mmt`, `source/lf.mmt`); the theories hold
/// only what the form needs.
pub const LF: &str = "namespace http://cds.omdoc.org/mmt❚

theory mmt =
  brackets # ( 1 ) prec -1000005❙
❚

namespace http://cds.omdoc.org/urtheories❚
import meta http://cds.omdoc.org/mmt❚
import rules scala://lf.mmt.kwarc.info❚

theory Typed =
  type❙
  oftype # 1 : 2 prec -9997 ❘ role Type❙
  definedas # 1 := 2 prec -9998 ❘ role Def❙
❚

theory Kinded =
  include ?Typed❙
  kind❙
❚

theory LambdaPi =
  include ?Kinded❙
  Pi # { V1T,… } 2 prec -10000❙
  lambda # [ V1T,… ] 2 prec -10000❙
  apply # 1%w… prec -10❙
  arrow # 1⟶… prec -9990❙
❚

theory LF =
  include meta?mmt❙
  include ?LambdaPi❙
  rule rules?LFHOAS❙
❚
";

/// The meta-theory of trion contracts: the sorts, the formulas over a trace,
/// the contracts and the obligations, over LF.
const META_THEORY: &str = "namespace http://trion.dev/meta❚
import ur http://cds.omdoc.org/urtheories❚
import rules scala://mmt.kwarc.info❚

// The language of the MMT form of a trion package.   ❚

theory Contracts : ur:?LF =
  string : type❙
  concat : string ⟶ string ⟶ string❙
  rule rules/lf?Realize string rules/api/uom?StandardString❙
  rule rules/lf?Realize concat rules/api/uom?StringOperations/Concat❙
  rule rules/literals?StandardStringInterpolation string concat❙
  int : type❙
  rule rules/lf?Realize int rules/api/uom?StandardInt❙
  neg : int ⟶ int❙
  strings : type❙
  snil : strings❙
  scons : string ⟶ strings ⟶ strings❙
  sjoin : strings ⟶ strings ⟶ strings❙
  cmp : type❙
  eq : cmp❙
  geq : cmp❙
  leq : cmp❙
  gt : cmp❙
  lt : cmp❙
  lterm : type❙
  term : string ⟶ int ⟶ lterm❙
  lterms : type❙
  tnil : lterms❙
  tcons : lterm ⟶ lterms ⟶ lterms❙
  tjoin : lterms ⟶ lterms ⟶ lterms❙
  prop : type❙
  props : type❙
  pnil : props❙
  pcons : prop ⟶ props ⟶ props❙
  pjoin : props ⟶ props ⟶ props❙
  true : prop❙
  not : prop ⟶ prop❙
  and : props ⟶ prop❙
  or : props ⟶ prop❙
  implies : prop ⟶ prop ⟶ prop❙
  Dom : string ⟶ string ⟶ prop❙
  Val : string ⟶ string ⟶ prop❙
  Act : string ⟶ prop❙
  Forbid : string ⟶ prop❙
  Discouraged : string ⟶ prop❙
  Event : string ⟶ prop❙
  Config : string ⟶ prop❙
  Role : string ⟶ string ⟶ prop❙
  Num : string ⟶ string ⟶ cmp ⟶ int ⟶ prop❙
  Lin : lterms ⟶ string ⟶ cmp ⟶ int ⟶ prop❙
  Before : string ⟶ string ⟶ prop❙
  Rel : string ⟶ strings ⟶ prop❙
  domain : type❙
  individuals : int ⟶ domain❙
  no_individuals : domain❙
  subject : type❙
  about : string ⟶ string ⟶ string ⟶ string ⟶ int ⟶ domain ⟶ subject❙
  actor : type❙
  system : string ⟶ actor❙
  environment : string ⟶ actor❙
  ctr : type❙
  contract : prop ⟶ prop ⟶ ctr❙
  parameter : type❙
  variable : string ⟶ string ⟶ parameter❙
  chosen_variable : string ⟶ string ⟶ parameter❙
  parameters : type❙
  vnil : parameters❙
  vcons : parameter ⟶ parameters ⟶ parameters❙
  vjoin : parameters ⟶ parameters ⟶ parameters❙
  timing : type❙
  timed : strings ⟶ timing❙
  scope : type❙
  unscoped : scope❙
  in_document : scope❙
  in_block : string ⟶ string ⟶ int ⟶ scope❙
  role : type❙
  as_guarantee : role❙
  as_assumption : role❙
  as_axiom : role❙
  as_permission : role❙
  as_recommendation : role❙
  as_form : role❙
  statement : type❙
  stated : string ⟶ string ⟶ int ⟶ string ⟶ role ⟶ parameters ⟶ timing ⟶ scope ⟶ ctr ⟶ statement❙
  ownership : type❙
  owns : string ⟶ prop ⟶ ownership❙
  question : type❙
  questions : type❙
  qnil : questions❙
  qcons : question ⟶ questions ⟶ questions❙
  qjoin : questions ⟶ questions ⟶ questions❙
  forall_exists : props ⟶ props ⟶ props ⟶ strings ⟶ question❙
  satisfiable : props ⟶ question❙
  unsatisfiable : props ⟶ question❙
  all : questions ⟶ question❙
  any : questions ⟶ question❙
  negation : question ⟶ question❙
  property : type❙
  consistency : property❙
  compatibility : property❙
  correctness : property❙
  completeness : property❙
  realizability : property❙
  recommendation : property❙
  choice : property❙
  check : property❙
  example : property❙
  scenario : property❙
  obligation : type❙
  obliged : string ⟶ property ⟶ string ⟶ strings ⟶ question ⟶ obligation❙
❚
";

/// The roles of a contract, as the meta-theory names them.
const ROLES: &[&str] = &["guarantee", "assumption", "axiom", "permission", "recommendation", "form"];

/// The contract of one statement in the MMT form.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Contract {
    pub id: String,
    pub file: String,
    pub line: usize,
    pub text: String,
    pub role: String,
    /// Each variable of the schematic contract with its type.
    pub parameters: Vec<(String, String)>,
    /// Each variable that the response chooses, with its type.
    pub chosen: Vec<(String, String)>,
    pub assume: Formula,
    pub guarantee: Formula,
    /// The temporal shape: when the contract applies and when its response comes.
    pub timing: Vec<String>,
    /// The scope of an assumption.
    pub scope: Scope,
}

/// The guarantees that an assumption is distributed to.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Scope {
    /// No assumption.
    Unscoped,
    /// Every guarantee of the document.
    Document,
    /// The guarantees of the shared condition block with this head, file
    /// and line, and of the blocks inside it.
    Block { head: String, file: String, line: usize },
}

/// The MMT form of a package.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Form {
    pub package: String,
    pub revision: String,
    pub semantics: String,
    pub tool: String,
    pub system: Vec<String>,
    pub environment: Vec<String>,
    pub contracts: Vec<Contract>,
    pub obligations: ProofObligations,
}

// ---------------------------------------------------------------- the libraries

/// The meta-theory as a URI.
fn contracts() -> MPath {
    static PATH: OnceLock<MPath> = OnceLock::new();
    PATH.get_or_init(|| MPath::parse_plain(&format!("{META}?Contracts")).expect("the meta-theory has a module URI")).clone()
}

/// Each error of the `mmt` crate on its line, with its position.
fn shown(errors: &[Error]) -> String {
    errors.iter().map(ToString::to_string).collect::<Vec<_>>().join("; ")
}

/// A library with the declarations of LF.
fn lf() -> Result<Library, String> {
    let mut lib = Library::new();
    let document: DPath = "http://trion.dev/lf.mmt".parse().map_err(|e: Error| e.to_string())?;
    let read = lib.add_source(LF, &document, None);
    if !read.is_ok() {
        return Err(format!("the declarations of LF do not read: {}", shown(read.errors())));
    }
    Ok(lib)
}

/// The library with LF and the meta-theory, read once.
fn base() -> Result<&'static Library, String> {
    static BASE: OnceLock<Result<Library, String>> = OnceLock::new();
    BASE.get_or_init(|| {
        let mut lib = lf()?;
        let document: DPath = format!("{META}.mmt").parse().map_err(|e: Error| e.to_string())?;
        let read = lib.add_source(META_THEORY, &document, None);
        if !read.is_ok() {
            return Err(format!("the meta-theory does not read: {}", shown(read.errors())));
        }
        Ok(lib)
    })
    .as_ref()
    .map_err(Clone::clone)
}

// ---------------------------------------------------------------- writing

/// The text of a string literal. MMT reads a string literal up to the next
/// quote and reads `$` as interpolation in `s"…"`, so these characters, the
/// percent sign, line breaks and the delimiters of MMT are written as `%XX`
/// of their UTF-8 bytes.
fn escaped(text: &str) -> String {
    let mut out = String::new();
    for c in text.chars() {
        if matches!(c, '%' | '"' | '\\' | '$' | '{' | '}' | '\n' | '\r' | '\t' | '❘' | '❙' | '❚') {
            let mut bytes = [0u8; 4];
            for b in c.encode_utf8(&mut bytes).bytes() {
                out.push_str(&format!("%{b:02X}"));
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// A constant of the meta-theory.
fn meta(name: &str) -> Term {
    Term::Sym(contracts().sym(name))
}

/// A constant of the meta-theory applied to arguments, in LF.
fn apply(head: &str, args: Vec<Term>) -> Term {
    Term::app(Term::Sym(hoas_apply()), std::iter::once(meta(head)).chain(args).collect())
}

fn literal(text: &str) -> Term {
    Term::lit(LitValue::String(escaped(text)), meta("string"))
}

fn natural(n: u64) -> Term {
    Term::lit(LitValue::Int(Integer::from(n)), meta("int"))
}

fn integer(n: i64) -> Term {
    if n < 0 { apply("neg", vec![natural(n.unsigned_abs())]) } else { natural(n.unsigned_abs()) }
}

fn count(n: usize) -> Term {
    natural(n as u64)
}

/// The longest run of a list written as `cons a (cons b … nil)`.
const RUN: usize = 8;

/// A kind of list of the meta-theory: its `cons`, `nil` and `join`.
#[derive(Clone, Copy)]
struct Kind {
    cons: &'static str,
    nil: &'static str,
    join: &'static str,
}

const STRINGS: Kind = Kind { cons: "scons", nil: "snil", join: "sjoin" };
const TERMS: Kind = Kind { cons: "tcons", nil: "tnil", join: "tjoin" };
const PROPS: Kind = Kind { cons: "pcons", nil: "pnil", join: "pjoin" };
const PARAMETERS: Kind = Kind { cons: "vcons", nil: "vnil", join: "vjoin" };
const QUESTIONS: Kind = Kind { cons: "qcons", nil: "qnil", join: "qjoin" };

/// A list: `cons a (cons b nil)` for at most [`RUN`] items, and otherwise
/// `join` of the lists of the two halves, so that the term of a list of `n`
/// items nests at most `RUN + log2(n)` levels.
fn list(kind: Kind, mut items: Vec<Term>) -> Term {
    if items.len() > RUN {
        let second = items.split_off(items.len() / 2);
        return apply(kind.join, vec![list(kind, items), list(kind, second)]);
    }
    let mut out = meta(kind.nil);
    for item in items.into_iter().rev() {
        out = apply(kind.cons, vec![item, out]);
    }
    out
}

fn strings<'a>(items: impl IntoIterator<Item = &'a String>) -> Term {
    list(STRINGS, items.into_iter().map(|s| literal(s)).collect())
}

fn cmp_name(cmp: Cmp) -> &'static str {
    match cmp {
        Cmp::Eq => "eq",
        Cmp::Ge => "geq",
        Cmp::Le => "leq",
        Cmp::Gt => "gt",
        Cmp::Lt => "lt",
    }
}

fn atom_term(atom: &Atom) -> Term {
    match atom {
        Atom::Dom { attr, value } => apply("Dom", vec![literal(attr), literal(value)]),
        Atom::Val { attr, value } => apply("Val", vec![literal(attr), literal(value)]),
        Atom::Act { key } => apply("Act", vec![literal(key)]),
        Atom::Forbid { key } => apply("Forbid", vec![literal(key)]),
        Atom::Discouraged { key } => apply("Discouraged", vec![literal(key)]),
        Atom::Event { key } => apply("Event", vec![literal(key)]),
        Atom::Config { key } => apply("Config", vec![literal(key)]),
        Atom::Role { subject, role } => apply("Role", vec![literal(subject), literal(role)]),
        Atom::Num { attr, unit, cmp, n } => apply("Num", vec![literal(attr), literal(unit), meta(cmp_name(*cmp)), integer(*n)]),
        Atom::Lin { terms, unit, cmp, n } => apply("Lin", vec![list(TERMS, terms.iter().map(|(attr, k)| apply("term", vec![literal(attr), integer(*k)])).collect()), literal(unit), meta(cmp_name(*cmp)), integer(*n)]),
        Atom::Before { first, second } => apply("Before", vec![literal(first), literal(second)]),
        Atom::Rel { name, args } => apply("Rel", vec![literal(name), strings(args)]),
    }
}

/// A formula as a term of the meta-theory.
pub fn term(formula: &Formula) -> Term {
    match formula {
        Formula::True => meta("true"),
        Formula::Atom(atom) => atom_term(atom),
        Formula::Not(inner) => apply("not", vec![term(inner)]),
        Formula::And(parts) => apply("and", vec![list(PROPS, parts.iter().map(term).collect())]),
        Formula::Or(parts) => apply("or", vec![list(PROPS, parts.iter().map(term).collect())]),
        Formula::Implies(a, b) => apply("implies", vec![term(a), term(b)]),
    }
}

/// The name of formula `n` of the pool: `f` and the digits of `n` written
/// as the letters `a` to `j`. MMT reads digits after a declared name as a
/// number (`f690` as `f6 90`), and a name of letters only as itself.
fn formula_name(n: usize) -> String {
    let digits: String = n.to_string().bytes().map(|d| char::from(b'a' + (d - b'0'))).collect();
    format!("f{digits}")
}

/// The number of a formula from its name.
fn formula_number(name: &str) -> Option<usize> {
    let letters = name.strip_prefix('f')?;
    if letters.is_empty() || !letters.bytes().all(|c| (b'a'..=b'j').contains(&c)) || (letters.len() > 1 && letters.starts_with('a')) {
        return None;
    }
    letters.bytes().map(|c| char::from(b'0' + (c - b'a'))).collect::<String>().parse().ok()
}

fn question_term(theory: &MPath, question: &ObligationQuestion) -> Term {
    let refs = |ids: &[usize]| list(PROPS, ids.iter().map(|&id| Term::Sym(theory.sym(&formula_name(id)))).collect());
    match question {
        ObligationQuestion::ForAllExists { premises, standing, conclusions, chosen } => apply("forall_exists", vec![refs(premises), refs(standing), refs(conclusions), strings(chosen)]),
        ObligationQuestion::Satisfiable { query } => apply("satisfiable", vec![refs(query)]),
        ObligationQuestion::Unsatisfiable { query } => apply("unsatisfiable", vec![refs(query)]),
        ObligationQuestion::All { parts } => apply("all", vec![list(QUESTIONS, parts.iter().map(|p| question_term(theory, p)).collect())]),
        ObligationQuestion::Any { parts } => apply("any", vec![list(QUESTIONS, parts.iter().map(|p| question_term(theory, p)).collect())]),
        ObligationQuestion::Not { part } => apply("negation", vec![question_term(theory, part)]),
    }
}

/// The properties of the obligations that trion states. A form that names
/// another is not read: no result could say what it means.
pub const PROPERTIES: &[&str] = &["consistency", "compatibility", "correctness", "completeness", "realizability", "recommendation", "choice", "check", "example", "scenario"];

/// The name of the theory of a package: a symbol of MMT.
fn theory_name(package: &str) -> String {
    let name: String = package.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' }).collect();
    if name.chars().next().is_some_and(|c| c.is_ascii_alphabetic()) { name } else { format!("p_{name}") }
}

/// A constant of the theory of a package: its name, the sort of the
/// meta-theory that is its type, and its definition.
fn constant(theory: &MPath, name: &str, sort: &str, definition: Term) -> Declaration {
    Declaration::Constant(Constant::new(theory.sym(name)).with_type(meta(sort)).with_definiens(definition))
}

impl Form {
    /// The URI of the theory of the package.
    fn theory_path(&self) -> MPath {
        let name = theory_name(&self.package);
        MPath::parse_plain(&format!("http://trion.dev/form/{name}?{name}")).expect("the name of a package theory is a symbol")
    }

    /// The manifest of the archive of the form.
    pub fn manifest(&self) -> String {
        let name = theory_name(&self.package);
        format!("id: trion/{name}\nsource-base: http://trion.dev/form/{name}\nnarration-base: http://trion.dev/form/{name}\ndependencies: MMT/urtheories\n")
    }

    /// The theory of the package as MMT objects.
    pub fn theory(&self) -> Theory {
        let path = self.theory_path();
        let mut theory = Theory::new(path.clone()).with_meta(contracts());
        let mut decls = Vec::new();
        let domain = self.obligations.individuals.map_or(meta("no_individuals"), |n| apply("individuals", vec![count(n)]));
        decls.push(constant(&path, "the_subject", "subject", apply("about", vec![literal(&self.package), literal(&self.revision), literal(&self.semantics), literal(&self.tool), count(self.obligations.moments), domain])));
        for (number, actor) in self.system.iter().enumerate() {
            decls.push(constant(&path, &format!("system{number}"), "actor", apply("system", vec![literal(actor)])));
        }
        for (number, actor) in self.environment.iter().enumerate() {
            decls.push(constant(&path, &format!("environment{number}"), "actor", apply("environment", vec![literal(actor)])));
        }
        for (number, contract) in self.contracts.iter().enumerate() {
            let variables = contract.parameters.iter().map(|(variable, kind)| apply("variable", vec![literal(variable), literal(kind)])).chain(contract.chosen.iter().map(|(variable, kind)| apply("chosen_variable", vec![literal(variable), literal(kind)])));
            let scope = match &contract.scope {
                Scope::Unscoped => meta("unscoped"),
                Scope::Document => meta("in_document"),
                Scope::Block { head, file, line } => apply("in_block", vec![literal(head), literal(file), count(*line)]),
            };
            let stated = apply(
                "stated",
                vec![
                    literal(&contract.id),
                    literal(&contract.file),
                    count(contract.line),
                    literal(&contract.text),
                    // A role that the meta-theory does not name is not visible, and the theory is not added.
                    meta(&format!("as_{}", contract.role)),
                    list(PARAMETERS, variables.collect()),
                    apply("timed", vec![strings(&contract.timing)]),
                    scope,
                    apply("contract", vec![term(&contract.assume), term(&contract.guarantee)]),
                ],
            );
            decls.push(constant(&path, &format!("contract{number}"), "statement", stated));
        }
        for (number, formula) in self.obligations.pool.iter().enumerate() {
            decls.push(constant(&path, &formula_name(number), "prop", term(formula)));
        }
        for (number, owner) in &self.obligations.owners {
            decls.push(constant(&path, &format!("owner{number}"), "ownership", apply("owns", vec![literal(owner), Term::Sym(path.sym(&formula_name(*number)))])));
        }
        for (number, obligation) in self.obligations.obligations.iter().enumerate() {
            let obliged = apply("obliged", vec![literal(&obligation.name), meta(&obligation.property), literal(&obligation.proposition), strings(&obligation.statements), question_term(&path, &obligation.question)]);
            decls.push(constant(&path, &format!("obligation{number}"), "obligation", obliged));
        }
        for d in decls {
            theory = theory.with_declaration(d);
        }
        theory
    }

    /// The form as the source file of an MMT archive: the meta-theory and
    /// the theory of the package, printed by the notations of their
    /// theories, and read back as this form. A form that is not added, not
    /// printed or not read back as itself is an error of trion, and no text
    /// is returned for it.
    pub fn write(&self) -> Result<String, String> {
        let mut lib = base()?.clone();
        let path = lib.add_theory(self.theory()).map_err(|e| format!("the theory of the package is not an MMT theory over the meta-theory: {e}"))?;
        let text = lib.print_theories(&[contracts(), path]).map_err(|e| format!("the theory of the package is not printed: {e}"))?;
        match Form::read(&text) {
            Ok(back) if back == *self => Ok(text),
            Ok(_) => Err("the printed form reads back as another form".to_string()),
            Err(e) => Err(format!("the printed form does not read back: {e}")),
        }
    }
}

// ---------------------------------------------------------------- reading

/// A constant of the meta-theory and its arguments, of a term that applies it (in LF) or names it.
fn parts(term: &Term) -> Option<(&str, &[Term])> {
    fn name(g: &GlobalName) -> Option<&str> {
        (*g.module() == contracts() && g.name().len() == 1).then(|| g.name().last_simple()).flatten()
    }
    match term {
        Term::Sym(g) => Some((name(g)?, &[])),
        Term::App(f, args) if matches!(&**f, Term::Sym(a) if *a == hoas_apply()) => match args.split_first() {
            Some((Term::Sym(g), rest)) => Some((name(g)?, rest)),
            _ => None,
        },
        _ => None,
    }
}

fn args<'a>(term: &'a Term, head: &str, count: usize) -> Result<&'a [Term], String> {
    match parts(term) {
        Some((h, a)) if h == head && a.len() == count => Ok(a),
        _ => Err(format!("`{term}` is no `{head}` of {count} arguments")),
    }
}

fn name_of(term: &Term) -> Result<&str, String> {
    match parts(term) {
        Some((name, [])) => Ok(name),
        _ => Err(format!("`{term}` names no constant of the meta-theory")),
    }
}

fn decode(text: &str) -> Result<String, String> {
    let mut bytes = Vec::new();
    let raw = text.as_bytes();
    let mut i = 0;
    while i < raw.len() {
        if raw[i] == b'%' {
            let hex = text.get(i + 1..i + 3).ok_or("a `%` without two hexadecimal digits")?;
            bytes.push(u8::from_str_radix(hex, 16).map_err(|_| format!("`%{hex}` is no escape"))?);
            i += 3;
        } else {
            bytes.push(raw[i]);
            i += 1;
        }
    }
    String::from_utf8(bytes).map_err(|e| format!("a literal is no UTF-8: {e}"))
}

fn text_of(term: &Term) -> Result<String, String> {
    match term {
        Term::Lit(Literal { value: LitValue::String(text), .. }) => decode(text),
        other => Err(format!("`{other}` is no string")),
    }
}

fn int_of(term: &Term) -> Result<i64, String> {
    let natural = |t: &Term| match t {
        Term::Lit(Literal { value: LitValue::Int(n), .. }) => n.to_i128().and_then(|n| i64::try_from(n).ok()).ok_or_else(|| format!("`{t}` is no number of 64 bits")),
        other => Err(format!("`{other}` is no number")),
    };
    match parts(term) {
        Some(("neg", [n])) => Ok(-natural(n)?),
        _ => natural(term),
    }
}

fn count_of(term: &Term) -> Result<usize, String> {
    usize::try_from(int_of(term)?).map_err(|e| format!("`{term}`: {e}"))
}

fn cmp_of(term: &Term) -> Result<Cmp, String> {
    match name_of(term)? {
        "eq" => Ok(Cmp::Eq),
        "geq" => Ok(Cmp::Ge),
        "leq" => Ok(Cmp::Le),
        "gt" => Ok(Cmp::Gt),
        "lt" => Ok(Cmp::Lt),
        other => Err(format!("`{other}` is no comparison")),
    }
}

/// The items of a list of `cons`, `nil` and `join`, in order, read without recursion.
fn items_of(term: &Term, kind: Kind) -> Result<Vec<&Term>, String> {
    let mut out = Vec::new();
    let mut rest = vec![term];
    while let Some(mut term) = rest.pop() {
        loop {
            match parts(term) {
                Some((name, [])) if name == kind.nil => break,
                Some((name, [item, tail])) if name == kind.cons => {
                    out.push(item);
                    term = tail;
                }
                Some((name, [first, second])) if name == kind.join => {
                    rest.push(second);
                    term = first;
                }
                _ => return Err(format!("`{term}` is no list of `{}`", kind.cons)),
            }
        }
    }
    Ok(out)
}

fn texts_of(term: &Term) -> Result<Vec<String>, String> {
    items_of(term, STRINGS)?.into_iter().map(text_of).collect()
}

fn formula_of(term: &Term) -> Result<Formula, String> {
    let s = text_of;
    let Some((head, a)) = parts(term) else { return Err(format!("`{term}` is no formula")) };
    Ok(match (head, a) {
        ("true", []) => Formula::True,
        ("not", [inner]) => Formula::Not(Box::new(formula_of(inner)?)),
        ("and", [parts]) => Formula::And(items_of(parts, PROPS)?.into_iter().map(formula_of).collect::<Result<_, _>>()?),
        ("or", [parts]) => Formula::Or(items_of(parts, PROPS)?.into_iter().map(formula_of).collect::<Result<_, _>>()?),
        ("implies", [x, y]) => Formula::Implies(Box::new(formula_of(x)?), Box::new(formula_of(y)?)),
        ("Dom", [attr, value]) => Formula::Atom(Atom::Dom { attr: s(attr)?, value: s(value)? }),
        ("Val", [attr, value]) => Formula::Atom(Atom::Val { attr: s(attr)?, value: s(value)? }),
        ("Act", [key]) => Formula::Atom(Atom::Act { key: s(key)? }),
        ("Forbid", [key]) => Formula::Atom(Atom::Forbid { key: s(key)? }),
        ("Discouraged", [key]) => Formula::Atom(Atom::Discouraged { key: s(key)? }),
        ("Event", [key]) => Formula::Atom(Atom::Event { key: s(key)? }),
        ("Config", [key]) => Formula::Atom(Atom::Config { key: s(key)? }),
        ("Role", [subject, role]) => Formula::Atom(Atom::Role { subject: s(subject)?, role: s(role)? }),
        ("Num", [attr, unit, cmp, n]) => Formula::Atom(Atom::Num { attr: s(attr)?, unit: s(unit)?, cmp: cmp_of(cmp)?, n: int_of(n)? }),
        ("Lin", [terms, unit, cmp, n]) => Formula::Atom(Atom::Lin {
            terms: items_of(terms, TERMS)?.into_iter().map(|t| args(t, "term", 2).and_then(|a| Ok((s(&a[0])?, int_of(&a[1])?)))).collect::<Result<_, _>>()?,
            unit: s(unit)?,
            cmp: cmp_of(cmp)?,
            n: int_of(n)?,
        }),
        ("Before", [first, second]) => Formula::Atom(Atom::Before { first: s(first)?, second: s(second)? }),
        ("Rel", [name, list]) => Formula::Atom(Atom::Rel { name: s(name)?, args: texts_of(list)? }),
        (other, a) => return Err(format!("`{other}` of {} arguments is no formula", a.len())),
    })
}

/// The formulas that a list names: constants of the theory of the package declared before.
fn refs_of(term: &Term, theory: &MPath, pool: &BTreeMap<String, usize>) -> Result<Vec<usize>, String> {
    items_of(term, PROPS)?
        .into_iter()
        .map(|t| match t {
            Term::Sym(g) if g.module() == theory => pool.get(&g.name().to_string()).copied().ok_or_else(|| format!("an obligation names `{}`, which is no formula of the form", g.name())),
            other => Err(format!("`{other}` names no formula")),
        })
        .collect()
}

fn question_of(term: &Term, theory: &MPath, pool: &BTreeMap<String, usize>) -> Result<ObligationQuestion, String> {
    let Some((head, a)) = parts(term) else { return Err(format!("`{term}` is no question")) };
    Ok(match (head, a) {
        ("forall_exists", [premises, standing, conclusions, chosen]) => ObligationQuestion::ForAllExists { premises: refs_of(premises, theory, pool)?, standing: refs_of(standing, theory, pool)?, conclusions: refs_of(conclusions, theory, pool)?, chosen: texts_of(chosen)? },
        ("satisfiable", [query]) => ObligationQuestion::Satisfiable { query: refs_of(query, theory, pool)? },
        ("unsatisfiable", [query]) => ObligationQuestion::Unsatisfiable { query: refs_of(query, theory, pool)? },
        ("all", [parts]) => ObligationQuestion::All { parts: items_of(parts, QUESTIONS)?.into_iter().map(|p| question_of(p, theory, pool)).collect::<Result<_, _>>()? },
        ("any", [parts]) => ObligationQuestion::Any { parts: items_of(parts, QUESTIONS)?.into_iter().map(|p| question_of(p, theory, pool)).collect::<Result<_, _>>()? },
        ("negation", [part]) => ObligationQuestion::Not { part: Box::new(question_of(part, theory, pool)?) },
        (other, a) => return Err(format!("`{other}` of {} arguments is no question", a.len())),
    })
}

impl Form {
    /// Reads the source file of an MMT form with the `mmt` crate: the file
    /// must read over LF, declare the meta-theory of this version of trioc,
    /// and hold one theory over it, whose constants are what [`Form::write`]
    /// writes. An error is reported with its line and column.
    pub fn read(text: &str) -> Result<Form, String> {
        let own = base()?.theory(&contracts()).ok_or("the meta-theory is not in the library")?;
        let mut lib = lf()?;
        let document: DPath = "http://trion.dev/form/specification.mmt".parse().map_err(|e: Error| e.to_string())?;
        let read = lib.add_source(text, &document, None);
        if !read.is_ok() {
            return Err(format!("it does not read as MMT: {}", shown(read.errors())));
        }
        // The meta-theory is the one of this version.
        match lib.theory(&contracts()) {
            None => return Err(format!("the file does not declare the meta-theory `{META}?Contracts`")),
            Some(declared) if declared != own => return Err(format!("the file declares a meta-theory `{META}?Contracts` other than the one of this version")),
            Some(_) => {}
        }
        let packages: Vec<&MPath> = read.theories().iter().filter(|p| **p != contracts()).collect();
        let [package] = packages.as_slice() else {
            return Err(format!("the file holds {} theories besides the meta-theory, and the form holds one, over the meta-theory", packages.len()));
        };
        let theory = lib.theory(package).ok_or("the theory of the package is not in the library")?;
        if theory.meta() != Some(&contracts()) || theory.parent().is_some() {
            return Err(format!("the theory {package} is not over the meta-theory `{META}?Contracts`"));
        }
        if !theory.metadata().is_empty() {
            return Err(format!("the theory {package} holds metadata, which the form does not"));
        }
        Form::of_theory(&lib, theory)
    }

    /// The form that the constants of the theory of a package state.
    fn of_theory(lib: &Library, theory: &Theory) -> Result<Form, String> {
        let mut form = Form { package: String::new(), revision: String::new(), semantics: String::new(), tool: String::new(), system: Vec::new(), environment: Vec::new(), contracts: Vec::new(), obligations: ProofObligations { moments: 0, individuals: None, pool: Vec::new(), owners: BTreeMap::new(), obligations: Vec::new(), findings: Vec::new() } };
        let mut pool: BTreeMap<String, usize> = BTreeMap::new();
        let mut subject = false;
        for declaration in theory.declarations() {
            let Declaration::Constant(c) = declaration else { return Err(format!("the theory of the package holds a declaration that is no constant: {declaration:?}")) };
            let name = c.path().name().to_string();
            let pos = lib.position_of(c.path()).map(|p| format!("{p}: ")).unwrap_or_default();
            let at = |problem: String| format!("{pos}the declaration `{name}`: {problem}");
            if c.notation().is_some() || c.presentation_notation().is_some() || !c.aliases().is_empty() || c.role().is_some() || !c.metadata().is_empty() {
                return Err(at("it has components that the form does not have".to_string()));
            }
            let (Some(sort), Some(value)) = (c.tp(), c.df()) else { return Err(at("it has no type or no definition".to_string())) };
            if !sort.is_plain() || !value.is_plain() {
                return Err(at("it leaves something open (an unknown or a free variable)".to_string()));
            }
            let (sort, value) = (sort.term(), value.term());
            let sort = name_of(sort).map_err(at)?;
            match sort {
                "subject" => {
                    let a = args(value, "about", 6).map_err(at)?;
                    form.package = text_of(&a[0]).map_err(at)?;
                    form.revision = text_of(&a[1]).map_err(at)?;
                    form.semantics = text_of(&a[2]).map_err(at)?;
                    form.tool = text_of(&a[3]).map_err(at)?;
                    form.obligations.moments = count_of(&a[4]).map_err(at)?;
                    form.obligations.individuals = match parts(&a[5]) {
                        Some(("no_individuals", [])) => None,
                        _ => Some(count_of(&args(&a[5], "individuals", 1).map_err(at)?[0]).map_err(at)?),
                    };
                    subject = true;
                }
                "actor" => match parts(value) {
                    Some(("system", [actor])) => form.system.push(text_of(actor).map_err(at)?),
                    Some(("environment", [actor])) => form.environment.push(text_of(actor).map_err(at)?),
                    _ => return Err(at(format!("`{value}` is no actor"))),
                },
                "statement" => {
                    let a = args(value, "stated", 9).map_err(at)?;
                    let role = name_of(&a[4]).map_err(at)?;
                    let role = role.strip_prefix("as_").filter(|r| ROLES.contains(r)).ok_or_else(|| at(format!("`{role}` is no role")))?.to_string();
                    let (mut parameters, mut chosen) = (Vec::new(), Vec::new());
                    for item in items_of(&a[5], PARAMETERS).map_err(at)? {
                        let (into, v) = match parts(item) {
                            Some(("chosen_variable", _)) => (&mut chosen, args(item, "chosen_variable", 2).map_err(at)?),
                            _ => (&mut parameters, args(item, "variable", 2).map_err(at)?),
                        };
                        into.push((text_of(&v[0]).map_err(at)?, text_of(&v[1]).map_err(at)?));
                    }
                    let timing = texts_of(&args(&a[6], "timed", 1).map_err(at)?[0]).map_err(at)?;
                    let scope = match parts(&a[7]) {
                        Some(("unscoped", [])) => Scope::Unscoped,
                        Some(("in_document", [])) => Scope::Document,
                        _ => {
                            let b = args(&a[7], "in_block", 3).map_err(at)?;
                            Scope::Block { head: text_of(&b[0]).map_err(at)?, file: text_of(&b[1]).map_err(at)?, line: count_of(&b[2]).map_err(at)? }
                        }
                    };
                    let contract = args(&a[8], "contract", 2).map_err(at)?;
                    form.contracts.push(Contract { id: text_of(&a[0]).map_err(at)?, file: text_of(&a[1]).map_err(at)?, line: count_of(&a[2]).map_err(at)?, text: text_of(&a[3]).map_err(at)?, role, parameters, chosen, assume: formula_of(&contract[0]).map_err(at)?, guarantee: formula_of(&contract[1]).map_err(at)?, timing, scope });
                }
                "prop" => {
                    formula_number(&name).filter(|&n| n == form.obligations.pool.len()).ok_or_else(|| at(format!("the formulas are not named {}, {}, … without a gap", formula_name(0), formula_name(1))))?;
                    // A formula is written out: it names no other.
                    let formula = formula_of(value).map_err(at)?;
                    pool.insert(name.clone(), form.obligations.pool.len());
                    form.obligations.pool.push(formula);
                }
                "ownership" => {
                    let a = args(value, "owns", 2).map_err(at)?;
                    let number = match &a[1] {
                        Term::Sym(f) if f.module() == theory.path() => pool.get(&f.name().to_string()).copied().ok_or_else(|| at(format!("`{}` is no formula declared before", f.name())))?,
                        other => return Err(at(format!("`{other}` names no formula"))),
                    };
                    form.obligations.owners.insert(number, text_of(&a[0]).map_err(at)?);
                }
                "obligation" => {
                    let a = args(value, "obliged", 5).map_err(at)?;
                    let property = match name_of(&a[1]) {
                        Ok(p) if PROPERTIES.contains(&p) => p.to_string(),
                        _ => return Err(at(format!("`{}` is none of the properties that trion states: {}", a[1], PROPERTIES.join(", ")))),
                    };
                    form.obligations.obligations.push(ProofObligation { name: text_of(&a[0]).map_err(at)?, property, proposition: text_of(&a[2]).map_err(at)?, statements: texts_of(&a[3]).map_err(at)?, question: question_of(&a[4], theory.path(), &pool).map_err(at)? });
                }
                other => return Err(at(format!("the sort `{other}` is not read"))),
            }
        }
        if !subject {
            return Err("the theory names no subject".to_string());
        }
        Ok(form)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn example() -> Form {
        let atoms = vec![
            Formula::Atom(Atom::Act { key: "API|store <message> & \"log\" $x {y} 100%\n❙".to_string() }),
            Formula::Atom(Atom::Num { attr: "time@1".to_string(), unit: "ms".to_string(), cmp: Cmp::Ge, n: -3 }),
            Formula::Atom(Atom::Lin { terms: vec![("a".to_string(), 2), ("b".to_string(), -1)], unit: "".to_string(), cmp: Cmp::Lt, n: 0 }),
            Formula::Atom(Atom::Rel { name: "owner".to_string(), args: vec!["room#1".to_string(), "member#2".to_string()] }),
            Formula::Atom(Atom::Rel { name: "empty".to_string(), args: vec![] }),
        ];
        let pool = vec![Formula::And(atoms.clone()), Formula::Implies(Box::new(Formula::True), Box::new(Formula::Not(Box::new(Formula::Or(vec![]))))), atoms[0].clone()];
        Form {
            package: "p".to_string(),
            revision: "r".to_string(),
            semantics: "1".to_string(),
            tool: "0.1.0".to_string(),
            system: vec!["API".to_string()],
            environment: vec!["user".to_string()],
            contracts: vec![
                Contract { id: "A".to_string(), file: "a.trion".to_string(), line: 3, text: "When a user sends a message, the API shall store the message.".to_string(), role: "guarantee".to_string(), parameters: vec![("user".to_string(), "user".to_string())], chosen: vec![("some user".to_string(), "user".to_string())], assume: Formula::True, guarantee: atoms[0].clone(), timing: vec!["activation: each occurrence of user send message".to_string(), "action API|store message: start then completion; completes within 5 s measured from the activation".to_string()], scope: Scope::Unscoped },
                Contract { id: "D".to_string(), file: "a.trion".to_string(), line: 5, text: "No user sends a message.".to_string(), role: "assumption".to_string(), parameters: Vec::new(), chosen: Vec::new(), assume: atoms[0].clone(), guarantee: Formula::True, timing: Vec::new(), scope: Scope::Block { head: "While the door is open".to_string(), file: "a.trion".to_string(), line: 4 } },
            ],
            obligations: ProofObligations {
                moments: 3,
                individuals: Some(2),
                pool,
                owners: BTreeMap::from([(2, "A".to_string())]),
                findings: Vec::new(),
                obligations: vec![ProofObligation { name: "consistency".to_string(), property: "consistency".to_string(), proposition: "within traces of 3 moments: …".to_string(), statements: vec!["A".to_string()], question: ObligationQuestion::All { parts: vec![ObligationQuestion::Satisfiable { query: vec![0] }, ObligationQuestion::ForAllExists { premises: vec![1], standing: vec![], conclusions: vec![2], chosen: vec!["API|store".to_string()] }] } }],
            },
        }
    }

    pub(super) fn text() -> String {
        example().write().unwrap()
    }

    #[test]
    fn a_form_is_read_as_it_was_written() {
        let form = example();
        let text = form.write().unwrap();
        assert_eq!(Form::read(&text).unwrap(), form);
        // The text is a fixed point: what is read is written as it was.
        assert_eq!(Form::read(&text).unwrap().write().unwrap(), text);
    }

    #[test]
    fn a_form_that_the_meta_theory_does_not_describe_is_not_written() {
        // A role that the meta-theory does not name: it is written by its URI and not read back as a role.
        let mut form = example();
        form.contracts[0].role = "wish".to_string();
        let error = form.write().unwrap_err();
        assert!(error.starts_with("the printed form does not read back: ") && error.contains("as_wish"), "{error}");
        // A property that the meta-theory does not name.
        let mut form = example();
        form.obligations.obligations[0].property = "beauty".to_string();
        assert!(form.write().unwrap_err().contains("beauty"));
        // An obligation that names a formula of the pool that is not there.
        let mut form = example();
        form.obligations.obligations[0].question = ObligationQuestion::Satisfiable { query: vec![7] };
        assert!(form.write().unwrap_err().contains("fh"));
    }

    /// Whether one of the first two parts of an error is a position `line:column`.
    fn positioned(error: &str) -> bool {
        error.split(": ").take(2).any(|at| at.split(':').count() == 2 && at.split(':').all(|n| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit())))
    }

    #[test]
    fn a_form_that_does_not_read_is_refused_with_its_position() {
        let text = text();
        // A literal where a string is expected: the object reads, and is not one that the form writes.
        let error = Form::read(&text.replacen("Act \"", "Act 5 \"", 1)).unwrap_err();
        assert!(error.contains("the declaration `contract0`") && error.contains("is no formula") && positioned(&error), "{error}");
        let error = Form::read(&text.replacen("(Act \"", "(Act 5)(\"", 1)).unwrap_err();
        assert!(positioned(&error), "{error}");
        // A name that is declared nowhere: the notations do not read it.
        let error = Form::read(&text.replacen("Act \"", "actt \"", 1)).unwrap_err();
        assert!(error.starts_with("it does not read as MMT: ") && error.contains("actt") && positioned(&error), "{error}");
        // Another file, and another meta-theory.
        assert!(Form::read("namespace http://elsewhere❚\ntheory p =\n❚\n").unwrap_err().contains("does not declare the meta-theory"));
        let error = Form::read(&text.replacen("  scenario : property❙\n", "", 1)).unwrap_err();
        assert!(error.contains("other than the one of this version"), "{error}");
    }

    #[test]
    fn long_lists_are_written_balanced_and_read_in_order() {
        let mut form = example();
        let parts: Vec<Formula> = (0..1000).map(|i| Formula::Atom(Atom::Act { key: format!("k{i}") })).collect();
        form.obligations.pool[0] = Formula::And(parts);
        form.contracts[0].timing = (0..1000).map(|i| format!("t{i}")).collect();
        let text = form.write().unwrap();
        assert_eq!(Form::read(&text).unwrap(), form);
        // no list nests deeper than a run and the halvings: at most eight `pcons` and ten `pjoin` in a row of brackets
        let deepest = text.lines().map(|l| l.chars().scan(0i64, |d, c| { *d += match c { '(' => 1, ')' => -1, _ => 0 }; Some(*d) }).max().unwrap_or(0)).max().unwrap();
        assert!(deepest < 40, "{deepest}");
    }

    /// The declarations of LF agree with MMT/urtheories: every constant that
    /// trion declares exists there with the same notation and role, and a
    /// form reads over the real archive as over trion's declarations.
    #[test]
    #[ignore = "needs MMT/urtheories (commit 8bc91e38df43decdd55b1eda471c4d7b9c75dfdd) in .tools/urtheories"]
    fn the_declarations_of_lf_agree_with_urtheories() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.tools/urtheories");
        let archive = mmt::Archive::open(&root).expect("needs MMT/urtheories in .tools/urtheories");
        let mut real = Library::new();
        let _ = real.load_archives(std::slice::from_ref(&archive));
        let ours = lf().unwrap();
        let mut compared = 0;
        for theory in ours.theories() {
            for c in theory.constants() {
                let official = real.constant(c.path()).unwrap_or_else(|| panic!("{} is not in MMT/urtheories", c.path()));
                assert_eq!(official.notation().map(ToString::to_string), c.notation().map(ToString::to_string), "{}", c.path());
                assert_eq!(official.role(), c.role(), "{}", c.path());
                compared += 1;
            }
            for d in theory.declarations() {
                if let Declaration::Rule(r) = d {
                    assert!(real.closure(theory.path()).iter().filter_map(|p| real.theory(p)).flat_map(|t| t.declarations()).any(|e| matches!(e, Declaration::Rule(q) if q.term() == r.term())), "{} in {}", r.term(), theory.path());
                }
            }
        }
        assert_eq!(compared, 9);
        // the form reads over the real archive to the same theory
        let text = text();
        let mut lib = real.clone();
        let read = lib.add_source(&text, &"http://trion.dev/form/specification.mmt".parse().unwrap(), None);
        assert!(read.is_ok(), "{}", shown(read.errors()));
        let mut mine = lf().unwrap();
        let mine_read = mine.add_source(&text, &"http://trion.dev/form/specification.mmt".parse().unwrap(), None);
        for p in mine_read.theories() {
            assert_eq!(lib.theory(p), mine.theory(p), "{p}");
        }
    }
}
