//! What the syntax types may hold: the reader and the constructors reject
//! the same terms and sorts — the productions SMT-LIB 2.7 added
//! (unsupported), what only another dialect has (a construction error), and
//! text nested beyond the reader's limit in its place (a depth error) — so
//! that every value prints as text that reads back to it. Also the error
//! values themselves.

use moxi::response::{Answer, Certificate, CheckSystemResponse, Model, State, Verbosity};
use moxi::{parse_term, CheckSystem, Command, Condition, ConditionKind, DeclareConst, DefineFun, DefineSort, DefineSystem, ErrorKind, Script};
use smtlib::command::FunctionDef;
use smtlib::lexicon::{ExtendedConstant, Numeral, SpecConstant};
use smtlib::response::ModelResponse;
use smtlib::term::{Identifier, MatchCase, Pattern, QualIdentifier, SortedVar};
use smtlib::{NonEmpty, Sort, Symbol, Term};
use std::str::FromStr;

/// The nesting the reader accepts: smtlib's default.
const LIMIT: usize = smtlib::Dialect::DEFAULT_MAX_DEPTH;

fn symbol(name: &str) -> Symbol {
    Symbol::new(name).unwrap()
}

fn var(name: &str) -> Term {
    Term::Identifier(QualIdentifier::plain(Identifier::simple(symbol(name))))
}

/// `(not (not … x))` whose text nests `depth` parentheses.
fn nested(depth: usize) -> Term {
    let not = QualIdentifier::plain(Identifier::simple(symbol("not")));
    (0..depth).fold(var("x"), |t, _| Term::Application(not.clone(), NonEmpty::one(t)))
}

/// `(A (A … Int))` whose text nests `depth` parentheses.
fn nested_sort(depth: usize) -> Sort {
    (0..depth).fold(Sort::int(), |s, _| Sort::apply(Identifier::simple(symbol("A")), NonEmpty::one(s)))
}

fn minus_one() -> Term {
    Term::Constant(SpecConstant::Extended(ExtendedConstant::parse("-1").unwrap()))
}

fn map_sort() -> Sort {
    Sort::apply(Identifier::simple(symbol("->")), NonEmpty::new(vec![Sort::int(), Sort::int()]).unwrap())
}

/// `(match x ((_ true)))`.
fn wildcard_match() -> Term {
    Term::Match(Box::new(var("x")), NonEmpty::one(MatchCase::new(Pattern::Wildcard, var("true"))))
}

fn kind<T: std::fmt::Debug>(result: moxi::Result<T>) -> ErrorKind {
    result.unwrap_err().kind()
}

// The productions SMT-LIB 2.7 added to the term grammar are rejected
// while reading, as unsupported, at the term that holds them; match and
// annotations, which SMT-LIB 2.6 has, are read, and so are `@` and `->`,
// which are symbols in the grammar of both versions (what 2.7 makes of them
// is theory).
#[test]
fn smtlib_2_7_forms_are_unsupported_when_read() {
    for (text, at) in [
        ("(define-system S :init (= f (lambda ((y Int)) y)))", 24),
        ("(check-system S :reachable (r (match x ((_ true)))))", 31),
        ("(check-system S :reachable (r (match x (((c _) true)))))", 31),
    ] {
        let error = Script::from_str(text).unwrap_err();
        assert_eq!((error.kind(), error.position().map(|p| p.column())), (ErrorKind::Unsupported, Some(at)), "{error}\n{text}");
        assert!(error.message().contains("2.7"), "{error}");
    }
    assert_eq!(kind(parse_term("(lambda ((y Int)) y)")), ErrorKind::Unsupported);
    for text in [
        "(define-system S :init (! (match x ((c true) (d false))) :named n))",
        "(define-system S :input ((f (-> Int Int))) :init (= (@ f 0) 1))",
        "(declare-const f (-> Int Int))",
        "(define-fun g ((h (-> Int Int))) Int (@ h 0))",
    ] {
        let read = Script::from_str(text).unwrap();
        assert_eq!(Script::from_str(&read.to_string()).unwrap(), read);
    }
}

// Constructors reject the same forms, and terms of other dialects, so the
// printer never writes text that reads back differently: an extended
// constant -1 would print as (- 1).
#[test]
fn constructors_reject_what_the_reader_cannot_produce() {
    let system = || DefineSystem::new(symbol("S"));
    assert_eq!(kind(system().with_init(minus_one())), ErrorKind::Construction);
    assert_eq!(kind(system().with_trans(parse_term("(= x 0)").map(|_| minus_one()).unwrap())), ErrorKind::Construction);
    let binder = Term::Binder(symbol("choice"), NonEmpty::one(SortedVar::new(symbol("y"), Sort::int())), Box::new(var("y")));
    assert_eq!(kind(system().with_inv(binder)), ErrorKind::Construction);
    let lambda = Term::Lambda(NonEmpty::one(SortedVar::new(symbol("y"), Sort::int())), Box::new(var("y")));
    assert_eq!(kind(Condition::new(ConditionKind::Reachable, symbol("r"), lambda)), ErrorKind::Unsupported);
    assert_eq!(kind(system().with_trans(wildcard_match())), ErrorKind::Unsupported);
    // `->` is a symbol of the grammar: a sort built with it is accepted.
    let f = SortedVar::new(symbol("f"), map_sort());
    assert!(system().with_local(vec![f.clone()]).is_ok());
    assert!(CheckSystem::new(symbol("S")).with_input(vec![f]).is_ok());
    assert!(DeclareConst::new(symbol("c"), map_sort()).is_ok());
    assert!(DefineSort::new(symbol("M"), vec![], map_sort()).is_ok());
    let def = |body| FunctionDef::new(symbol("g"), vec![], Sort::int(), body);
    assert_eq!(kind(DefineFun::new(def(minus_one()))), ErrorKind::Construction);
    assert_eq!(kind(Model::new(symbol("m"), vec![ModelResponse::DefineFun(def(minus_one()))])), ErrorKind::Construction);
    assert_eq!(kind(State::new(Numeral::new("0").unwrap(), vec![(symbol("x"), minus_one())])), ErrorKind::Construction);
    assert_eq!(kind(Certificate::new(symbol("c"), minus_one(), Numeral::new("1").unwrap())), ErrorKind::Construction);
    // Constructor errors have no position.
    assert_eq!(system().with_init(minus_one()).unwrap_err().position(), None);
}

// The deepest term or sort each place admits is accepted and round-trips;
// one more parenthesis is a depth error. The depth counts the parentheses
// of the place: 1 for :init, 2 for a named formula, 5 for a value in a
// trail, 4 inside a model's define-fun. Run on a 2 MiB stack, the size of
// a spawned thread, because the derived comparison recurses.
#[test]
fn depth_limit_in_each_place() {
    std::thread::Builder::new().stack_size(2 << 20).spawn(depth_limit).unwrap().join().unwrap();
}

fn depth_limit() {
    let init = |t| DefineSystem::new(symbol("S")).with_init(t);
    let ok = init(nested(LIMIT - 1)).unwrap();
    let script = Script::new(vec![Command::DefineSystem(Box::new(ok))]);
    assert_eq!(Script::from_str(&script.to_string()).unwrap(), script);
    assert_eq!(kind(init(nested(LIMIT))), ErrorKind::Depth);

    let condition = |t| Condition::new(ConditionKind::Reachable, symbol("r"), t);
    let check = CheckSystem::new(symbol("S")).with_attribute(moxi::CheckAttribute::Condition(condition(nested(LIMIT - 2)).unwrap()));
    let script = Script::new(vec![Command::CheckSystem(Box::new(check))]);
    assert_eq!(Script::from_str(&script.to_string()).unwrap(), script);
    assert_eq!(kind(condition(nested(LIMIT - 1))), ErrorKind::Depth);

    let state = |t| State::new(Numeral::new("0").unwrap(), vec![(symbol("x"), t)]);
    let trail = moxi::response::Trail::new(symbol("p"), vec![state(nested(LIMIT - 5)).unwrap()]);
    let response = CheckSystemResponse::new(Verbosity::Full, vec![moxi::response::ResponseItem::Trail(trail)]);
    assert_eq!(CheckSystemResponse::from_str(&response.to_string()).unwrap(), response);
    assert_eq!(kind(state(nested(LIMIT - 4))), ErrorKind::Depth);

    let model = |t| Model::new(symbol("m"), vec![ModelResponse::DefineFun(FunctionDef::new(symbol("g"), vec![], Sort::bool(), t))]);
    let response = CheckSystemResponse::new(Verbosity::Full, vec![moxi::response::ResponseItem::Model(model(nested(LIMIT - 4)).unwrap())]);
    assert_eq!(CheckSystemResponse::from_str(&response.to_string()).unwrap(), response);
    assert_eq!(kind(model(nested(LIMIT - 3))), ErrorKind::Depth);

    let constant = |s| DeclareConst::new(symbol("c"), s);
    let script = Script::new(vec![Command::DeclareConst(constant(nested_sort(LIMIT - 1)).unwrap())]);
    assert_eq!(Script::from_str(&script.to_string()).unwrap(), script);
    assert_eq!(kind(constant(nested_sort(LIMIT))), ErrorKind::Depth);
}

// Errors: the kind, the position of the text, the message; an error of the
// SMT-LIB layer keeps the smtlib error, with its own kind, as its source.
#[test]
fn errors_wrap_smtlib_errors() {
    use std::error::Error as _;
    let lexical = Script::from_str("(define-system S :init x’)").unwrap_err();
    assert_eq!(lexical.kind(), ErrorKind::Lexical);
    assert_eq!(lexical.smtlib().map(|e| e.kind()), Some(smtlib::ErrorKind::Lexical));
    assert!(lexical.source().is_some());
    let deep = Script::from_str(&format!("(define-system S :init {}x{})", "(not ".repeat(LIMIT), ")".repeat(LIMIT))).unwrap_err();
    assert_eq!((deep.kind(), deep.smtlib().map(|e| e.kind())), (ErrorKind::Depth, Some(smtlib::ErrorKind::Depth)));
    let ours = Script::from_str("(define-system S :colour red)").unwrap_err();
    assert_eq!(ours.kind(), ErrorKind::Syntax);
    assert!(ours.smtlib().is_none() && ours.source().is_none());
    assert_eq!(ours.to_string(), format!("1:18: syntax error: {}", ours.message()));
}

// Reading one command or one response from text without one reports the
// end of the text.
#[test]
fn empty_text_is_an_error_at_its_end() {
    for text in ["", "\n  ", "; a comment\n"] {
        let lines = text.matches('\n').count() + 1;
        let column = text.rsplit('\n').next().unwrap().chars().count() + 1;
        let error = Command::from_str(text).unwrap_err();
        assert_eq!((error.kind(), error.position().map(|p| (p.line(), p.column()))), (ErrorKind::Syntax, Some((lines, column))), "{error} for {text:?}");
        let error = CheckSystemResponse::from_str(text).unwrap_err();
        assert_eq!((error.kind(), error.position().map(|p| (p.line(), p.column()))), (ErrorKind::Syntax, Some((lines, column))), "{error} for {text:?}");
    }
    assert_eq!(Script::from_str("  ").unwrap(), Script::default());
}

// The small enumerations print as the words of the grammar.
#[test]
fn displays() {
    assert_eq!(ConditionKind::Fairness.to_string(), ":fairness");
    assert_eq!(Answer::Unknown.to_string(), "unknown");
    assert_eq!(Verbosity::Compact.to_string(), "compact");
}

// Every class of error from text reports where it happened: lexical,
// syntax (from smtlib and from this crate), unsupported (an unadopted
// command, an SMT-LIB 2.7 production), depth (at the parenthesis beyond the
// limit), each at the line and column of the offending token or list.
#[test]
fn every_error_from_text_has_its_position() {
    let deep = format!("(define-system S\n :init {}x{})", "(not ".repeat(LIMIT), ")".repeat(LIMIT));
    for (text, kind, at) in [
        ("(define-system S)\n(define-system T :init x’)", ErrorKind::Lexical, (2, 25)),
        ("(define-system S)\n(declare-sort A)", ErrorKind::Syntax, (2, 1)),
        ("(define-system S)\n  (define-system T :colour red)", ErrorKind::Syntax, (2, 20)),
        ("(define-system S)\n(assert true)", ErrorKind::Unsupported, (2, 2)),
        ("(define-system S)\n(define-system T :init (lambda ((y Int)) y))", ErrorKind::Unsupported, (2, 24)),
        (deep.as_str(), ErrorKind::Depth, (2, 8 + 5 * (LIMIT - 1))),
    ] {
        let error = Script::from_str(text).unwrap_err();
        assert_eq!((error.kind(), error.position().map(|p| (p.line(), p.column()))), (kind, Some(at)), "{error}");
    }
    let error = CheckSystemResponse::from_str("(check-system-response\n :verbosity full :model (m (assert true)))").unwrap_err();
    assert_eq!((error.kind(), error.position().map(|p| (p.line(), p.column()))), (ErrorKind::Syntax, Some((2, 29))), "{error}");
}
