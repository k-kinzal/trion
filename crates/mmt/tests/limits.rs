//! Deep input is an error of kind `Limit`, never a stack overflow, reading is
//! linear in the nesting, and the default depth is safe on a 2 MiB stack (the
//! default stack of a test thread) in an unoptimized build. Every case runs on
//! a thread with exactly that stack, so a debug run of these tests proves the
//! default.

mod common;

use std::time::{Duration, Instant};

use common::*;
use mmt::rules::hoas_apply;
use mmt::term::Term;
use mmt::uri::MPath;
use mmt::{Constant, Declaration, Document, ErrorKind, Library, Limits, Theory};

const STACK: usize = 2 * 1024 * 1024;
const DEPTH: usize = Limits::DEFAULT_DEPTH;

/// Runs `f` on a thread with a 2 MiB stack.
fn on_small_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new().stack_size(STACK).spawn(f).unwrap().join().unwrap()
}

const SRC: &str = "namespace http://test.org/deep❚
import rules scala://mmt.kwarc.info❚
theory D : http://cds.omdoc.org/urtheories?LF =
  str : type❙
  concat : str ⟶ str ⟶ str❙
  rule rules/lf?Realize str rules/api/uom?StandardString❙
  rule rules/literals?StandardStringInterpolation str concat❙
  a : str❙
  neg : str ⟶ str ❘ # - 1 prec 30❙
  imp : str ⟶ str ⟶ str ❘ # 1 %R⇒ 2 prec 5❙
  all : (str ⟶ str) ⟶ str ❘ # ∀ ⟦ V1T ⟧ 2 prec -10000❙
  f : str ⟶ str❙
❚";

fn library() -> (Library, MPath) {
    let mut lib = mini_lf();
    let e = lib.add_source(SRC, &base(), None);
    assert!(e.is_ok(), "{}", show(e.errors()));
    (lib, mpath("http://test.org/deep?D"))
}

/// Objects that nest `n` levels: brackets, a prefix operator, a
/// right-associative operator, default application, binders in the types of
/// bound variables, and interpolated strings.
fn objects(n: usize) -> Vec<(&'static str, String)> {
    vec![
        ("brackets", format!("{}a{}", "(".repeat(n), ")".repeat(n))),
        ("prefix", format!("{}a", "- ".repeat(n))),
        ("right-associative", format!("{}a", "a ⇒ ".repeat(n))),
        ("application", format!("{}a{}", "(f ".repeat(n), ")".repeat(n))),
        ("binder", format!("{}str{}", "∀ ⟦ x : ".repeat(n), " ⟧ a".repeat(n))),
        ("interpolation", format!("{}a{}", "s\"x${ ".repeat(n), " }\"".repeat(n))),
    ]
}

/// Reads each object and prints it back; the kind of the first error.
fn read_and_print(n: usize) -> Vec<(&'static str, Result<(), ErrorKind>)> {
    let (lib, d) = library();
    let scope = lib.object_scope(&d).unwrap();
    objects(n).into_iter().map(|(what, text)| (what, scope.parse(&text).and_then(|r| scope.print(&r)).map(drop).map_err(|e| e.kind()))).collect()
}

#[test]
fn objects_of_the_default_depth_read_and_print_on_a_2_mib_stack() {
    // a binder and an interpolation are two levels of the term each (`lambda` in `apply`, `concat` of the parts), so half as many
    for (what, r) in on_small_stack(|| read_and_print(DEPTH)) {
        if what != "interpolation" && what != "binder" {
            assert_eq!(r, Ok(()), "{what}");
        }
    }
    for (what, r) in on_small_stack(|| read_and_print(DEPTH / 2 - 1)) {
        assert_eq!(r, Ok(()), "{what}");
    }
}

#[test]
fn deeper_objects_are_a_limit_error_in_linear_time() {
    for n in [DEPTH + 1, 100_000] {
        let start = Instant::now();
        for (what, r) in on_small_stack(move || read_and_print(n)) {
            if what != "brackets" || n > 2 * DEPTH + 2 {
                assert_eq!(r, Err(ErrorKind::Limit), "{what} {n}");
            }
        }
        assert!(start.elapsed() < Duration::from_secs(20), "{n}: {:?}", start.elapsed());
    }
}

#[test]
fn brackets_cost_no_stack_and_are_linear() {
    // brackets are not part of the term and are followed in a loop: deep brackets need only the scanner's bound
    let time = |n: usize| {
        on_small_stack(move || {
            let d = mpath("http://test.org/deep?D");
            let mut lib = Library::with_limits(Limits::default().with_depth(n));
            let minilf = std::fs::read_to_string(crate_dir().join("tests/data/minilf.mmt")).unwrap();
            assert!(lib.add_source(&minilf, &"http://test.org/minilf.mmt".parse().unwrap(), None).is_ok());
            assert!(lib.add_source(SRC, &base(), None).is_ok());
            let text = format!("{}a{}", "(".repeat(n), ")".repeat(n));
            let start = Instant::now();
            let r = lib.object_scope(&d).unwrap().parse(&text).unwrap();
            assert_eq!(*r.term(), Term::Sym(d.sym("a")));
            start.elapsed()
        })
    };
    let (small, large) = (time(2_000), time(16_000));
    // linear: 8 times the input, well below the 64 times of a quadratic reading
    assert!(large < small * 24 + Duration::from_millis(200), "{small:?} {large:?}");
}

#[test]
fn deep_terms_built_by_hand_are_refused_without_overflow() {
    on_small_stack(|| {
        let (mut lib, d) = library();
        let a = Term::Sym(d.sym("a"));
        let neg = Term::Sym(d.sym("neg"));
        let deep = (0..100_000).fold(a.clone(), |t, _| Term::app(Term::Sym(hoas_apply()), vec![neg.clone(), t]));
        assert_eq!(lib.object_scope(&d).unwrap().print_term(&deep).unwrap_err().kind(), ErrorKind::Limit);
        let p = mpath("http://test.org/deep?Built");
        let t = Theory::new(p.clone()).with_meta(mpath("http://cds.omdoc.org/urtheories?LF")).with_declaration(Declaration::Constant(Constant::new(p.sym("c")).with_definiens(deep)));
        assert_eq!(lib.add_theory(t).unwrap_err().kind(), ErrorKind::Limit);
        // at the limit, a term is added and printed
        let ok = (1..DEPTH).fold(a, |t, _| Term::app(Term::Sym(hoas_apply()), vec![neg.clone(), t]));
        let t = Theory::new(p.clone()).with_meta(mpath("http://cds.omdoc.org/urtheories?LF")).with_declaration(Declaration::Include(d.clone())).with_declaration(Declaration::Constant(Constant::new(p.sym("c")).with_definiens(ok)));
        lib.add_theory(t).unwrap();
        lib.print_theories(&[p]).unwrap();
    });
}

fn nested_theories(n: usize) -> String {
    format!("namespace http://test.org/nest❚ {}{}", "theory T = c❙ ".repeat(n), "❚".repeat(n))
}

#[test]
fn nested_theories_of_the_default_depth_read_elaborate_and_print_on_a_2_mib_stack() {
    on_small_stack(|| {
        let mut lib = Library::new();
        let e = lib.add_source(&nested_theories(DEPTH), &base(), None);
        assert!(e.is_ok(), "{}", show(e.errors()));
        assert_eq!(e.theories().len(), DEPTH);
        let text = lib.print_theories(&[mpath("http://test.org/nest?T")]).unwrap();
        assert_eq!(Document::parse(&text).unwrap(), Document::parse(&nested_theories(DEPTH)).unwrap());
    });
}

#[test]
fn deeper_nested_theories_are_a_limit_error() {
    on_small_stack(|| {
        for n in [DEPTH + 1, 100_000] {
            assert_eq!(Document::parse(&nested_theories(n)).unwrap_err().kind(), ErrorKind::Limit);
            let errors = Library::new().add_source(&nested_theories(n), &base(), None).into_errors();
            assert_eq!(errors.len(), 1);
            assert_eq!(errors[0].kind(), ErrorKind::Limit);
        }
    });
}
#[test]
fn theories_required_before_they_are_elaborated_nest_at_most_the_depth() {
    // each theory includes the next, which is declared later: elaboration requires them inside one another
    let chain = |n: usize| {
        let mut text = String::from("namespace http://test.org/chain❚ ");
        for i in 0..n {
            text.push_str(&format!("theory T{i} = include ?T{}❙ c❙ ❚ ", i + 1));
        }
        text.push_str(&format!("theory T{n} = c❙ ❚"));
        text
    };
    on_small_stack(move || {
        let e = Library::new().add_source(&chain(DEPTH - 1), &base(), None);
        assert!(e.is_ok(), "{}", show(e.errors()));
        let errors = Library::new().add_source(&chain(10_000), &base(), None).into_errors();
        assert!(errors.iter().any(|e| e.kind() == ErrorKind::Limit), "{}", show(&errors));
    });
}
