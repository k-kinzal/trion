//! The examples of MMT's language documentation (doc/language/*.md of
//! UniFormal/MMT at v27.0.0), verbatim where they are complete MMT text and
//! embedded in a minimal theory where they are fragments. Each test names the
//! file and section it is taken from.

mod common;

use common::*;
use mmt::notation::Marker;
use mmt::rules::hoas_apply;
use mmt::uri::{MPath, NamespaceMap};
use mmt::{Declaration, Document, ErrorKind, Library, Metadatum, Notation, ParseResult, Term};

fn sym(thy: &str, name: &str) -> Term {
    Term::Sym(mpath(thy).sym(name))
}

fn read(lib: &Library, theory: &MPath, text: &str) -> ParseResult {
    lib.object_scope(theory).unwrap().parse(text).unwrap()
}

/// declarations.md, "Notations": `# 1 + 2 prec 10` and `# 1 ⋅ 2 prec 15`, so that
/// "the expression `a + b ⋅ c` would be correctly parsed as `a + (b ⋅ c)`";
/// objects.md, "Examples": that is `OMA(OMS(+),OMS(a),OMA(⋅,OMS(b),OMS(c)))`.
#[test]
fn declarations_notations_precedence() {
    let mut lib = mini_lf();
    let errors = add(&mut lib, "namespace http://test.org/n❚ theory T = a❙ b❙ c❙ plus # 1 + 2 prec 10❙ times # 1 ⋅ 2 prec 15❙ ❚");
    assert!(errors.is_empty(), "{}", show(&errors));
    let t = mpath("http://test.org/n?T");
    let r = read(&lib, &t, "a + b ⋅ c");
    let s = |n| sym("http://test.org/n?T", n);
    assert_eq!(*r.term(), Term::app(s("plus"), vec![s("a"), Term::app(s("times"), vec![s("b"), s("c")])]));
    // with the precedences swapped, the reading changes
    let errors = add(&mut lib, "namespace http://test.org/n❚ theory U = a❙ b❙ c❙ plus # 1 + 2 prec 15❙ times # 1 ⋅ 2 prec 10❙ ❚");
    assert!(errors.is_empty(), "{}", show(&errors));
    let u = |n| sym("http://test.org/n?U", n);
    let r = read(&lib, &mpath("http://test.org/n?U"), "a + b ⋅ c");
    assert_eq!(*r.term(), Term::app(u("times"), vec![Term::app(u("plus"), vec![u("a"), u("b")]), u("c")]));
}

/// declarations.md, "Notations": "implication is right-associative by convention.
/// This can be handled by assigning it a notation `1 %R⇒ 2`."
#[test]
fn declarations_notations_right_associative() {
    let mut lib = mini_lf();
    let errors = add(&mut lib, "namespace http://test.org/n❚ theory R = a❙ b❙ c❙ imp # 1 %R⇒ 2❙ conj # 1 ∧ 2❙ ❚");
    assert!(errors.is_empty(), "{}", show(&errors));
    let s = |n| sym("http://test.org/n?R", n);
    let r = read(&lib, &mpath("http://test.org/n?R"), "a ⇒ b ⇒ c");
    assert_eq!(*r.term(), Term::app(s("imp"), vec![s("a"), Term::app(s("imp"), vec![s("b"), s("c")])]));
    // without %R, connectives are left-associative
    let r = read(&lib, &mpath("http://test.org/n?R"), "a ∧ b ∧ c");
    assert_eq!(*r.term(), Term::app(s("conj"), vec![Term::app(s("conj"), vec![s("a"), s("b")]), s("c")]));
}

/// declarations.md, "Notations": "the false elimination rule can be formalized as
/// `⊦ false ⟶ {A:prop}⊦ A` with notation `# falsE 1 %I2`"; the second argument "can be
/// inferred by the type checker". Reading leaves it as an unknown (`/I/0`), for a type
/// checker to infer; this crate does not infer it.
#[test]
fn declarations_notations_implicit_marker() {
    let n = Notation::parse("falsE 1 %I2", &NamespaceMap::empty()).unwrap();
    assert!(n.markers().contains(&Marker::ImplicitArg(2)));
    let mut lib = mini_lf();
    let errors = add(
        &mut lib,
        "namespace http://test.org/n❚ theory ND : http://cds.omdoc.org/urtheories?LF =
           prop : type❙
           ded : prop ⟶ type ❘ # ⊦ 1 prec 0❙
           false : prop❙
           falsE : ⊦ false ⟶ {A:prop}⊦ A ❘ # falsE 1 %I2❙
           ex : {B : prop} ⊦ false ⟶ ⊦ B ❘ = [B][p] falsE p❙
         ❚",
    );
    assert!(errors.is_empty(), "{}", show(&errors));
    let ex = lib.constant(&mpath("http://test.org/n?ND").sym("ex")).unwrap();
    let df = ex.df().unwrap();
    // the types of B and p are unknowns as well, since `[B][p]` declares none
    assert_eq!(df.term().to_string(), "(lambda [B : /B/0] (lambda [p : (/p/1 B)] (apply falsE p (/I/2 B p))))");
    assert_eq!(df.unknowns().len(), 3);
}

/// declarations.md, "Notations": "A constant `c` with type Π_{a:A}F(a)→B takes two
/// arguments ... So `c` could have a notation `# c 2` omitting the first argument."
/// Reading puts an unknown for the omitted argument.
#[test]
fn declarations_notations_omitted_argument_is_implicit() {
    let mut lib = mini_lf();
    let errors = add(
        &mut lib,
        "namespace http://test.org/n❚ theory Dep : http://cds.omdoc.org/urtheories?LF =
           A : type❙ B : type❙ F : A ⟶ type❙
           c : {a:A} F a ⟶ B ❘ # c 2❙
           a0 : A❙ x : F a0❙
           y : B ❘ = c x❙
         ❚",
    );
    assert!(errors.is_empty(), "{}", show(&errors));
    let thy = mpath("http://test.org/n?Dep");
    let y = lib.constant(&thy.sym("y")).unwrap();
    let unknown = y.df().unwrap().unknowns()[0].clone();
    assert_eq!(*y.df().unwrap().term(), Term::app(Term::Sym(hoas_apply()), vec![Term::Sym(thy.sym("c")), Term::Var(unknown), Term::Sym(thy.sym("x"))]));
}

/// declarations.md, "Metadata": the example verbatim inside a theory. MMT reads the key
/// with `StructureParser.readSPath`, i.e. `Path.parseS`, and `?myAnnotationKey` is a module
/// URI, so MMT v27.0.0 rejects the example as written ("symbol path expected"); with symbol
/// URIs as keys (`?M?myAnnotationKey`) it is accepted.
#[test]
fn declarations_metadata() {
    let example = "myAnnotationKey   ❙
myAnnotationKey2  ❙
myAnnotationValue ❙
myAnnotationValue2❙

myConstant : someType ❘ meta ?myAnnotationKey  ?myAnnotationValue
                      ❘ meta ?myAnnotationKey2 ?myAnnotationValue2❙";
    let mut lib = mini_lf();
    let errors = add(&mut lib, &format!("namespace http://test.org/n❚ theory M = someType❙ {example} ❚"));
    assert_eq!(errors.len(), 1, "{}", show(&errors));
    assert_eq!(errors[0].kind(), ErrorKind::Uri, "{}", errors[0]);
    let fixed = example.replace("?myAnnotation", "?M?myAnnotation");
    let errors = add(&mut lib, &format!("namespace http://test.org/n❚ theory M = someType❙ {fixed} ❚"));
    assert!(errors.is_empty(), "{}", show(&errors));
    let thy = mpath("http://test.org/n?M");
    let c = lib.constant(&thy.sym("myConstant")).unwrap();
    assert_eq!(c.metadata(), vec![Metadatum::Meta(thy.sym("myAnnotationKey"), Term::Sym(thy.sym("myAnnotationValue"))), Metadatum::Meta(thy.sym("myAnnotationKey2"), Term::Sym(thy.sym("myAnnotationValue2")))]);
}

/// modules.md, "Metadata": the theory of the example verbatim, which MMT v27.0.0 rejects for
/// the reason given at [`declarations_metadata`], and accepts with symbol URIs as keys; the
/// view of the same example is outside the supported subset and rejected as unsupported.
#[test]
fn modules_metadata() {
    let theory = "theory MyTheory =
  myAnnotationKey   ❙
  myAnnotationKey2  ❙
  myAnnotationValue ❙
  myAnnotationValue2❙
  meta ?myAnnotationKey  ?myAnnotationValue ❙
  meta ?myAnnotationKey2 ?myAnnotationValue2❙
❚";
    let view = "// Also possible in views: ❚
view v : ?MyTheory -> ... =
  // Do the symbols come from the domain theory? ❙

  meta ?myAnnotationKey  ?myAnnotationValue ❙
  meta ?myAnnotationKey2 ?myAnnotationValue2❙
❚";
    let mut lib = mini_lf();
    let errors = add(&mut lib, &format!("namespace http://test.org/n❚ {theory}"));
    assert_eq!(errors.len(), 1, "{}", show(&errors));
    assert_eq!(errors[0].kind(), ErrorKind::Uri, "{}", errors[0]);
    let errors = add(&mut lib, &format!("namespace http://test.org/n❚ {}", theory.replace("meta ?myAnnotation", "meta ?MyTheory?myAnnotation")));
    assert!(errors.is_empty(), "{}", show(&errors));
    let thy = mpath("http://test.org/n?MyTheory");
    let t = lib.theory(&thy).unwrap();
    // the values `?myAnnotationValue` are module references, as for any object
    assert_eq!(t.metadata(), vec![Metadatum::Meta(thy.sym("myAnnotationKey"), Term::Module(mpath("http://test.org/n?myAnnotationValue"))), Metadatum::Meta(thy.sym("myAnnotationKey2"), Term::Module(mpath("http://test.org/n?myAnnotationValue2")))]);
    let e = Document::parse(&format!("{theory}\n{view}")).unwrap_err();
    assert_eq!(e.kind(), ErrorKind::Unsupported, "{e}");
    assert!(e.to_string().contains("views"), "{e}");
}

/// modules.md, "Theories": "the inner theory can see all previous declarations of the
/// outer theory, but at no point can the outer theory see inside the inner theory".
#[test]
fn modules_nested_theories() {
    let mut lib = mini_lf();
    let errors = add(&mut lib, "namespace http://test.org/n❚ theory outer = a❙ theory inner = b❙ c # see 1❙ d = see a❙ ❚ e = a❙ ❚");
    assert!(errors.is_empty(), "{}", show(&errors));
    let inner = lib.theory(&mpath("http://test.org/n?outer/inner")).unwrap();
    assert_eq!(inner.parent(), Some(&mpath("http://test.org/n?outer")));
    let outer = lib.theory(&mpath("http://test.org/n?outer")).unwrap();
    assert!(outer.declarations().iter().any(|d| matches!(d, Declaration::Theory(p) if *p == mpath("http://test.org/n?outer/inner"))));
    // the later body of the outer theory does not see the inner theory
    let errors = add(&mut lib, "namespace http://test.org/n❚ theory outer2 = a❙ theory inner = b❙ ❚ e = b❙ ❚");
    assert_eq!(errors.len(), 1, "{}", show(&errors));
    assert_eq!(errors[0].kind(), ErrorKind::Unresolved, "{}", errors[0]);
    assert!(lib.theory(&mpath("http://test.org/n?outer2")).is_none());
}

/// namespaces.md, "Interpretation Instructions": the three instructions as given.
#[test]
fn namespaces_interpretation_instructions() {
    let mut lib = mini_lf();
    let errors = add(
        &mut lib,
        "namespace http://some.example.uri.org/❚
import prefix http://some.example.uri.org/❚
theory SomeTheory = c❙ ❚
fixmeta http://some.example.uri.org/?SomeTheory❚
theory T = d = c❙ ❚
theory U = include prefix?SomeTheory❙ e = c❙ ❚",
    );
    assert!(errors.is_empty(), "{}", show(&errors));
    let t = lib.theory(&mpath("http://some.example.uri.org/?T")).unwrap();
    assert_eq!(t.meta(), Some(&mpath("http://some.example.uri.org/?SomeTheory")));
    let d = lib.constant(&mpath("http://some.example.uri.org/?T").sym("d")).unwrap();
    assert_eq!(d.df().map(ParseResult::term), Some(&sym("http://some.example.uri.org/?SomeTheory", "c")));
    let u = lib.constant(&mpath("http://some.example.uri.org/?U").sym("e")).unwrap();
    assert_eq!(u.df().map(ParseResult::term), Some(&sym("http://some.example.uri.org/?SomeTheory", "c")));
}

/// namespaces.md: "If all files begin by declaring `.` as the namespace, ... only folder
/// names count and file names are ignored"; "the latter [relative URIs] are interpreted
/// relative to the current namespace. At the beginning of a file, the current namespace
/// is the corresponding document identifier."
#[test]
fn namespaces_relative() {
    let mut lib = mini_lf();
    let base = "http://ex.org/folder/file.mmt".parse().unwrap();
    let e = lib.add_source("theory A = a❙ ❚ namespace .❚ theory B = b❙ ❚ namespace sub❚ theory C = c❙ ❚", &base, None);
    assert!(e.is_ok(), "{}", show(e.errors()));
    let shown: Vec<String> = e.theories().iter().map(ToString::to_string).collect();
    // `URI.resolve` merges a relative path with all but the last segment of the base (as RFC 3986 does),
    // and `namespace .` leaves no trailing slash, so `sub` replaces `folder`
    assert_eq!(shown, ["http://ex.org/folder/file.mmt?A", "http://ex.org/folder?B", "http://ex.org/sub?C"]);
}

/// delimiters.md: the delimiters ❚ ❙ ❘ (U+275A, U+2759, U+2758), and their ASCII
/// alternatives (GS, RS, US as in `api/parser/Reader.scala`) read the same.
#[test]
fn delimiters_unicode_and_ascii() {
    let unicode = "namespace http://test.org/n❚ theory D = a # A ❘ role R❙ b❙ ❚";
    let ascii = "namespace http://test.org/n\u{1d} theory D = a # A \u{1f} role R\u{1e} b\u{1e} \u{1d}";
    assert_eq!(Document::parse(unicode).unwrap(), Document::parse(ascii).unwrap());
}

/// declarations.md, "Structures": structures are outside the supported subset and are rejected.
#[test]
fn declarations_structures_are_unsupported() {
    let e = Document::parse("theory Rings = R : type ❙ structure addition : ?AbelianGroup = G = R ❙ ❚ ❚").unwrap_err();
    assert_eq!(e.kind(), ErrorKind::Unsupported, "{e}");
}

/// declarations.md, "Rules": "`rule PATH` ... where `PATH` is the MMT URI of a Scala
/// object". A rule that does not change reading is accepted and has no effect; a lexer
/// extension that MMT applies and this crate does not implement is unsupported.
#[test]
fn declarations_rules_without_effect_on_reading_are_accepted() {
    let mut lib = mini_lf();
    let errors = add(&mut lib, "namespace http://test.org/n❚ import rules scala://lf.mmt.kwarc.info❚ theory X = rule rules?ShallowPolymorphism❙ ❚");
    assert!(errors.is_empty(), "{}", show(&errors));
    let errors = add(&mut lib, "namespace http://test.org/n❚ import rules scala://mmt.kwarc.info❚ theory Y = rule rules/quotation?TermLiteralRule❙ ❚");
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].kind(), ErrorKind::Unsupported, "{}", errors[0]);
}

/// declarations.md, "Constants": "If a constant has both a type and a definition, the
/// definition has to type-check against the given type". That is type checking, which
/// this crate does not do: an ill-typed definition is read like any other.
#[test]
fn declarations_constants_are_read_not_type_checked() {
    let mut lib = mini_lf();
    let errors = add(
        &mut lib,
        "namespace http://test.org/n❚ theory C : http://cds.omdoc.org/urtheories?LF =
           i : type❙ o : type❙ z : i❙ f : i ⟶ o❙
           bad : i ❘ = f z❙
         ❚",
    );
    assert!(errors.is_empty(), "{}", show(&errors));
}
