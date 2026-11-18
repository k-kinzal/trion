//! Inputs that once broke the crate, and inputs at the limits: terms nested
//! 100 000 deep go through the parser, the printer, `Clone`,
//! `PartialEq`, `Hash`, `Debug` and `Drop` on the test's thread (2 MiB of stack
//! by default), which a recursive implementation exhausts long before.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use eunoia::{parse_script, parse_term, Application, LetForm, LetTerm, ParseErrorKind, Position, Symbol, Term};

const DEPTH: usize = 100_000;

fn nested(open: &str, leaf: &str, close: &str) -> String {
    let mut s = String::with_capacity((open.len() + close.len()) * DEPTH + leaf.len());
    for _ in 0..DEPTH {
        s.push_str(open);
    }
    s.push_str(leaf);
    for _ in 0..DEPTH {
        s.push_str(close);
    }
    s
}

fn hash(t: &Term) -> u64 {
    let mut h = DefaultHasher::new();
    t.hash(&mut h);
    h.finish()
}

/// Parses, prints, compares, hashes, clones, formats and drops a deep term.
fn exercise(text: &str) -> Term {
    let t = parse_term(text).unwrap();
    assert!(t.depth() > DEPTH);
    assert_eq!(t.to_string(), text);
    let c = t.clone();
    assert_eq!(c, t);
    assert_eq!(hash(&c), hash(&t));
    assert!(format!("{c:?}").len() > text.len());
    drop(c);
    t
}

#[test]
fn deep_applications() {
    exercise(&nested("(f ", "x", ")"));
}

#[test]
fn deep_lets_annotations_binders_and_qualified_heads() {
    exercise(&nested("(let ((x ", "y", ")) x)"));
    exercise(&nested("(let ((x y)) ", "x", ")"));
    exercise(&nested("(! ", "x", " :named n)"));
    exercise(&nested("(lambda ((x ", "T", ")) x)"));
    exercise(&nested("((_ ", "f", " 1) x)"));
}

#[test]
fn deep_terms_that_differ_at_the_bottom_are_unequal() {
    let a = parse_term(&nested("(f ", "x", ")")).unwrap();
    let b = parse_term(&nested("(f ", "y", ")")).unwrap();
    assert_ne!(a, b);
}

#[test]
fn deep_terms_built_without_the_parser_drop() {
    let mut t = Term::symbol("x").unwrap();
    for i in 0..DEPTH {
        t = if i % 2 == 0 { Term::Apply(Application::new(Term::symbol("f").unwrap(), vec![t]).unwrap()) } else { Term::Let(LetTerm::new(LetForm::Let, vec![(Symbol::new("y").unwrap(), Term::symbol("x").unwrap())], t)) };
    }
    assert_eq!(t.depth(), DEPTH + 1);
    drop(t);
}

#[test]
fn deep_scripts_round_trip() {
    let body = nested("(f ", "a", ")");
    let text = format!("(declare-const a Bool) (define d () {body}) (assume @p {body})");
    let script = parse_script(&text).unwrap();
    assert_eq!(parse_script(&script.to_string()).unwrap(), script);
    let lambdas = nested("(lambda ((x ", "Bool", ")) x)");
    let script = parse_script(&format!("(define d () {lambdas})")).unwrap();
    assert_eq!(parse_script(&script.to_string()).unwrap(), script);
}

#[test]
fn an_error_deep_inside_is_placed_at_its_token() {
    let body = nested("(f ", "#q", ")");
    let err = parse_script(&format!("(declare-const f (-> Bool Bool))\n(assume @p {body})")).unwrap_err();
    assert!(matches!(err.kind, ParseErrorKind::InvalidLiteral(_)), "{err}");
    assert_eq!(err.position, Position::new(2, 12 + 3 * DEPTH as u32));
}

#[test]
fn unbalanced_deep_text_is_an_error() {
    let open = "(f ".repeat(DEPTH);
    assert!(parse_term(&open).is_err());
    assert!(parse_script(&format!("(assume @p {open})")).is_err());
}

/// A binder keeps its arguments: the variable list once moved the head out of
/// the frame, and the first argument was then read as the head and dropped,
/// which a round trip cannot see (both directions drop it) but the printed
/// text can.
#[test]
fn binders_keep_their_arguments() {
    let text = "(forall ((x Int) (y Int)) (P x y))";
    let t = parse_term(text).unwrap();
    assert_eq!(t.to_string(), text);
    let Term::Apply(a) = &t else { panic!("{t}") };
    assert_eq!(a.args().len(), 1);
    assert_eq!(a.vars().map(<[_]>::len), Some(2));
}
