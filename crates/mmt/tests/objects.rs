//! Theories built as objects (`Library::add_theory`) over the stand-in for
//! LF's notations: the printed text reads back to the same theory, and what
//! could not be written or read back is refused, attributed to the constant.

mod common;

use common::*;
use mmt::rules::hoas_apply;
use mmt::term::{LitValue, Term};
use mmt::uri::{DPath, LocalName, MPath};
use mmt::{Constant, Declaration, ErrorKind, Library, Limits, Metadatum, Theory};

const META: &str = "namespace http://test.org/meta❚
import rules scala://mmt.kwarc.info❚
theory M : http://cds.omdoc.org/urtheories?LF =
  s : type❙
  rule rules/lf?Realize s rules/api/uom?StandardString❙
  o : type❙
  p : s ⟶ o❙
  q : o ⟶ o ⟶ o ❘ # 1 ∧ 2 prec 10❙
❚
";

fn library() -> (Library, MPath) {
    let mut lib = mini_lf();
    let e = lib.add_source(META, &"http://test.org/meta.mmt".parse().unwrap(), None);
    assert!(e.is_ok(), "{}", show(e.errors()));
    (lib, mpath("http://test.org/meta?M"))
}

fn lf(f: Term, args: Vec<Term>) -> Term {
    Term::app(Term::Sym(hoas_apply()), std::iter::once(f).chain(args).collect())
}

fn string(meta: &MPath, s: &str) -> Term {
    Term::lit(LitValue::String(s.to_string()), Term::Sym(meta.sym("s")))
}

fn built() -> MPath {
    mpath("http://test.org/built?B")
}

fn theory(meta: &MPath, decls: impl FnOnce(&MPath) -> Vec<Constant>) -> Theory {
    let path = built();
    decls(&path).into_iter().fold(Theory::new(path).with_meta(meta.clone()), |t, c| t.with_declaration(Declaration::Constant(c)))
}

#[test]
fn a_theory_built_as_objects_prints_and_reads_back() {
    let (mut lib, m) = library();
    let sym = |n: &str| Term::Sym(m.sym(n));
    let t = theory(&m, |b| {
        let a = lf(sym("p"), vec![string(&m, "a \u{2200} b // 'q'")]);
        vec![
            Constant::new(b.sym("a")).with_type(sym("o")).with_definiens(a).with_alias(LocalName::simple("α")).with_role("Simplify").with_metadatum(Metadatum::Tag(m.sym("o"))),
            Constant::new(b.sym("c")).with_type(sym("o")).with_definiens(lf(sym("q"), vec![Term::Sym(b.sym("a")), Term::Sym(b.sym("a"))])),
        ]
    });
    let p = lib.add_theory(t.clone()).unwrap();
    let printed = lib.print_theories(&[m.clone(), p.clone()]).unwrap();
    assert!(printed.contains("c : o ❘ = a ∧ a❙"), "{printed}");
    let mut fresh = mini_lf();
    let base: DPath = "http://test.org/printed.mmt".parse().unwrap();
    let e = fresh.add_source(&printed, &base, Some("printed.mmt".as_ref()));
    assert!(e.is_ok(), "{}", show(e.errors()));
    assert_eq!(fresh.theory(&p), Some(&t));
}

#[test]
fn what_could_not_be_written_is_refused_at_the_constant() {
    let (lib, m) = library();
    let sym = |n: &str| Term::Sym(m.sym(n));
    let add = |t: Theory| lib.clone().add_theory(t).unwrap_err();
    // a name twice, a constant of another theory
    let e = add(theory(&m, |b| vec![Constant::new(b.sym("a")).with_type(sym("o")), Constant::new(b.sym("a"))]));
    assert_eq!(e.kind(), ErrorKind::Structure, "{e}");
    assert_eq!(e.contexts(), ["constant http://test.org/built?B?a"], "{e}");
    let e = add(theory(&m, |_| vec![Constant::new(m.sym("a"))]));
    assert_eq!(e.kind(), ErrorKind::Structure, "{e}");
    // a role that would end the component
    let e = add(theory(&m, |b| vec![Constant::new(b.sym("a")).with_role("x ❘ y")]));
    assert_eq!(e.kind(), ErrorKind::Syntax, "{e}");
    assert_eq!(e.contexts(), ["constant http://test.org/built?B?a"], "{e}");
    // an object deeper than the limit
    let deep = (0..=Limits::DEFAULT_DEPTH).fold(sym("o"), |t, _| lf(sym("q"), vec![t, sym("o")]));
    let e = add(theory(&m, |b| vec![Constant::new(b.sym("a")).with_definiens(deep)]));
    assert_eq!(e.kind(), ErrorKind::Limit, "{e}");
    // a meta-theory that is not in the library
    let e = add(theory(&mpath("http://test.org/meta?Nothing"), |_| vec![]));
    assert_eq!(e.kind(), ErrorKind::Unresolved, "{e}");
    // a theory that is declared already
    let e = add(Theory::new(m.clone()));
    assert_eq!(e.kind(), ErrorKind::Structure, "{e}");
}

#[test]
fn a_string_that_the_reader_cannot_delimit_is_refused_when_printed() {
    // MMT's string lexer has no escape, and the structure reader ends a component at ❙ inside quotes
    for text in ["say \"hi\"", "a ❙ b", "a ❘ b"] {
        let (mut lib, m) = library();
        let t = theory(&m, |b| vec![Constant::new(b.sym("a")).with_type(Term::Sym(m.sym("o"))).with_definiens(lf(Term::Sym(m.sym("p")), vec![string(&m, text)]))]);
        let p = lib.add_theory(t).unwrap();
        let e = lib.print_theories(&[p]).unwrap_err();
        assert_eq!(e.kind(), ErrorKind::Print, "{e}");
        assert_eq!(e.contexts(), ["constant http://test.org/built?B?a"], "{e}");
    }
}

#[test]
fn references_are_not_checked_but_printing_fails_on_what_it_cannot_write() {
    let (mut lib, m) = library();
    let sym = |n: &str| Term::Sym(m.sym(n));
    // no static semantics: a reference to a later constant is accepted
    let p = lib.add_theory(theory(&m, |b| vec![Constant::new(b.sym("a")).with_type(sym("o")).with_definiens(Term::Sym(b.sym("c"))), Constant::new(b.sym("c")).with_type(sym("o"))])).unwrap();
    // it is written by its URI and reads back as itself
    let printed = lib.print_theories(&[m.clone(), p.clone()]).unwrap();
    let mut fresh = mini_lf();
    assert!(fresh.add_source(&printed, &"http://test.org/printed.mmt".parse().unwrap(), None).is_ok(), "{printed}");
    assert_eq!(fresh.theory(&p), lib.theory(&p));
}
