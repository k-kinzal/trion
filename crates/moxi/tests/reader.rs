//! The reader's rules one by one: for each rule of the grammar, text that
//! keeps it is read and text that breaks it is rejected with the kind of
//! error and the line and column the rule implies; and the printer's
//! canonical forms.

use std::str::FromStr;
use moxi::response::{Answer, CheckSystemResponse, QueryResult, ResponseItem, Verbosity};
use moxi::{parse_term, CheckAttribute, CheckSystem, Command, Condition, ConditionKind, DefineSystem, ErrorKind, Query, Script, Subsystem};
use smtlib::term::SortedVar;
use smtlib::{NonEmpty, Sort, Symbol};

fn symbol(name: &str) -> Symbol {
    Symbol::new(name).unwrap()
}

/// Requires `text` to be rejected with `kind` at line 1, `column`.
fn rejected(text: &str, kind: ErrorKind, column: usize) -> moxi::Error {
    let error = Script::from_str(text).map(|s| panic!("read: {text}\n{s:?}")).unwrap_err();
    assert_eq!((error.kind(), error.position().unwrap().line(), error.position().unwrap().column()), (kind, 1, column), "{error}\n{text}");
    error
}

fn column(text: &str, needle: &str) -> usize {
    text[..text.find(needle).unwrap()].chars().count() + 1
}

// Commands: the five adopted SMT-LIB commands and MoXI's three; any other
// SMT-LIB command is unsupported at its name, including the 2.7 commands;
// any other head is a syntax error.
#[test]
fn commands() {
    let all = "(set-logic QF_LIA)(declare-sort A 0)(define-sort B () A)(declare-const c A)(define-fun f ((x Int)) Int x)(declare-enum-sort E (a b))(define-system S)(check-system S)";
    let names: Vec<&str> = Script::from_str(all).unwrap().commands().iter().map(Command::name).collect();
    assert_eq!(names, ["set-logic", "declare-sort", "define-sort", "declare-const", "define-fun", "declare-enum-sort", "define-system", "check-system"]);
    for unadopted in ["(assert true)", "(declare-fun f () Bool)", "(exit)", "(check-sat)", "(declare-datatype D ((d)))", "(define-const c Bool true)", "(declare-sort-parameter X)"] {
        let error = rejected(&format!("(set-logic ALL) {unadopted}"), ErrorKind::Unsupported, 18);
        assert!(error.message().contains("does not adopt"), "{error}");
    }
    rejected("(define-systems S)", ErrorKind::Syntax, 2);
    rejected("(let ((x 1)) x)", ErrorKind::Syntax, 2);
    rejected("()", ErrorKind::Syntax, 1);
    rejected("define-system", ErrorKind::Syntax, 1);
    rejected("(declare-enum-sort E)", ErrorKind::Syntax, 1);
    rejected("(declare-enum-sort E (a (b)))", ErrorKind::Syntax, 25);
    // Command::parse reads exactly one command.
    assert_eq!(Command::from_str("").unwrap_err().kind(), ErrorKind::Syntax);
    let two = Command::from_str("(define-system S) (define-system T)").unwrap_err();
    assert_eq!((two.kind(), two.position().unwrap().column()), (ErrorKind::Syntax, 19));
    assert_eq!("(define-system S)".parse::<Command>().unwrap().name(), "define-system");
}

// define-system: its attributes, each at most once except :subsys, in the
// order variables, subsystems, formulas; every attribute has a value.
#[test]
fn define_system() {
    let text = "(define-system S :input ((i Int)) :local () :subsys (A (T i)) :subsys (B (T)) :trans (= o' i))";
    let script = Script::from_str(text).unwrap();
    let Command::DefineSystem(s) = &script.commands()[0] else { panic!() };
    assert_eq!((s.input().map(<[_]>::len), s.output(), s.local().map(<[_]>::len)), (Some(1), None, Some(0)));
    assert_eq!(s.subsystems().iter().map(|x| (x.name().as_str(), x.arguments().len())).collect::<Vec<_>>(), [("A", 1), ("B", 0)]);
    assert!(s.init().is_none() && s.trans().is_some() && s.inv().is_none() && !s.is_atomic());
    for (text, at) in [
        ("(define-system S :init true :input ((x Bool)))", ":input"),
        ("(define-system S :init true :subsys (N (T)))", ":subsys"),
        ("(define-system S :subsys (N (T)) :local ((x Bool)))", ":local"),
        ("(define-system S :init true :init false)", ":init false"),
        ("(define-system S :output () :output ())", ":output ()"),
        ("(define-system S :colour red)", ":colour"),
        ("(define-system S :init)", ":init"),
        ("(define-system S :init :trans true)", ":init :trans"),
        ("(define-system S true)", "true"),
        ("(define-system :init true)", ":init"),
        ("(define-system S :input (x))", "x"),
        ("(define-system S :subsys (N T))", "T"),
        ("(define-system S :subsys (N ()))", "()"),
        ("(define-system S :subsys (N (T x) y))", "(N"),
        ("(define-system S :subsys (N (T (x))))", "(x)"),
    ] {
        let at = if at == ":init" && text.ends_with(":init)") { column(text, ":init") } else { text.rfind(at).map(|i| text[..i].chars().count() + 1).unwrap() };
        rejected(text, ErrorKind::Syntax, at);
    }
    rejected("(define-system)", ErrorKind::Syntax, 1);
    // Formulas are SMT-LIB terms: a parenthesized term is not one (smtlib
    // reports it at the inner list, which is not a function identifier).
    rejected("(define-system S :init ((and a b)))", ErrorKind::Syntax, 25);
}

// check-system: :input, :output and :local at most once and before the
// other attributes; the others repeatable; named formulas, queries, and
// :queries with at least one query.
#[test]
fn check_system() {
    let text = "(check-system S :output ((o Int)) :reachable (r (> o 0)) :current (c (= o 0)) :query (q (r c)) :queries ((p ()) (s (r))) :reachable (r2 o))";
    let script = Script::from_str(text).unwrap();
    let Command::CheckSystem(c) = &script.commands()[0] else { panic!() };
    assert_eq!(c.conditions().map(|x| (x.kind(), x.label().as_str())).collect::<Vec<_>>(), [(ConditionKind::Reachable, "r"), (ConditionKind::Current, "c"), (ConditionKind::Reachable, "r2")]);
    assert_eq!(c.queries().map(|q| q.name().as_str()).collect::<Vec<_>>(), ["q", "p", "s"]);
    assert_eq!(c.attributes().len(), 5);
    for (text, at) in [
        ("(check-system S :query (q (a)) :input ((x Bool)))", ":input"),
        ("(check-system S :local () :local ())", ":local ()"),
        ("(check-system S :queries ())", "()"),
        ("(check-system S :query (q a))", "a"),
        ("(check-system S :query (q))", "(q)"),
        ("(check-system S :reachable r)", "r)"),
        ("(check-system S :reachable (r))", "(r)"),
        ("(check-system S :assumption ((a) true))", "(a)"),
        ("(check-system S :invariant (p true))", ":invariant"),
    ] {
        rejected(text, ErrorKind::Syntax, text.rfind(at).map(|i| text[..i].chars().count() + 1).unwrap());
    }
}

// Attributes written in another order than the canonical one print in the
// canonical order and read back equal; the printed text is stable.
#[test]
fn canonical_order() {
    let script = Script::from_str("(define-system S :output ((o Bool)) :input ((i Bool)) :inv (= o i) :init o)").unwrap();
    let printed = script.to_string();
    assert_eq!(printed, "(define-system S\n :input ((i Bool))\n :output ((o Bool))\n :init o\n :inv (= o i))\n");
    assert_eq!(Script::from_str(&printed).unwrap(), script);
}

// The lexicon: ' is a symbol character; a quoted symbol followed by ' is
// two tokens (SMT-LIB §3.1), so `|o|'` is the symbol o and then the symbol
// '; reserved words are not symbols unless quoted; ’ is not a character of
// the lexicon.
#[test]
fn lexicon() {
    let script = Script::from_str("(define-system S :trans (= o' |o'|))").unwrap();
    let Command::DefineSystem(s) = &script.commands()[0] else { panic!() };
    assert_eq!(s.trans().unwrap().to_text(&moxi::dialect()), "(= o' o')");
    rejected("(define-system S :trans |o|')", ErrorKind::Syntax, 28);
    assert_eq!(parse_term("(= |o|' x)").unwrap().to_text(&moxi::dialect()), "(= o ' x)");
    rejected("(define-system S :input ((reset Bool)))", ErrorKind::Syntax, 27);
    Script::from_str("(define-system S :input ((|reset| Bool)))").unwrap();
    rejected("(define-system S :trans o’)", ErrorKind::Lexical, 26);
}

// Errors are values with a kind, a position and a message, and display as
// `line:column: kind: message`.
#[test]
fn errors() {
    let error = Script::from_str("(define-system S)\n\n  (define-system S :init)").unwrap_err();
    assert_eq!((error.position().unwrap().line(), error.position().unwrap().column()), (3, 20));
    assert_eq!(error.to_string(), format!("3:20: syntax error: {}", error.message()));
    let boxed: Box<dyn std::error::Error> = Box::new(error);
    assert!(boxed.to_string().starts_with("3:20"));
}

// Syntax built with the constructors prints as text that reads back to an
// equal value.
#[test]
fn constructors() -> moxi::Result<()> {
    let int = |name: &str| SortedVar::new(symbol(name), Sort::int());
    let delay = DefineSystem::new(symbol("Delay")).with_input(vec![int("i")])?.with_output(vec![int("o")])?.with_init(parse_term("(= o 0)")?)?.with_trans(parse_term("(= o' i)")?)?;
    let double = DefineSystem::new(symbol("DoubleDelay"))
        .with_input(vec![int("in")])?
        .with_output(vec![int("out")])?
        .with_local(vec![int("temp")])?
        .with_subsystem(Subsystem::new(symbol("D1"), symbol("Delay"), vec![symbol("in"), symbol("temp")]))
        .with_subsystem(Subsystem::new(symbol("D2"), symbol("Delay"), vec![symbol("temp"), symbol("out")]));
    let check = CheckSystem::new(symbol("DoubleDelay"))
        .with_attribute(CheckAttribute::Condition(Condition::new(ConditionKind::Reachable, symbol("r"), parse_term("(> out 5)")?)?))
        .with_attribute(CheckAttribute::Query(Query::new(symbol("q"), vec![symbol("r")])))
        .with_attribute(CheckAttribute::Queries(NonEmpty::one(Query::new(symbol("p"), vec![]))));
    let script: Script = [Command::SetLogic(symbol("QF_LIA")), Command::DefineSystem(Box::new(delay)), Command::DefineSystem(Box::new(double)), Command::CheckSystem(Box::new(check))].into_iter().collect();
    assert_eq!(Script::from_str(&script.to_string()).unwrap(), script);
    let mut grown = Script::default();
    for command in script.clone().into_commands() {
        grown.push(command);
    }
    assert_eq!(grown, script);
    Ok(())
}

// The response reader: :verbosity once and required; a query result with
// :result and at most one of each reference; a trace with both trails; a
// certificate with :inv and :k; trails of numbered states.
#[test]
fn responses() {
    let ok = "(check-system-response :verbosity compact :query (q :result unsat :certificate c) :certificate (c :inv (>= k 0) :k 1))";
    let response = CheckSystemResponse::from_str(ok).unwrap();
    assert_eq!(response.verbosity(), Verbosity::Compact);
    assert_eq!(response.queries().map(QueryResult::result).collect::<Vec<_>>(), [Answer::Unsat]);
    let ResponseItem::Certificate(c) = &response.items()[1] else { panic!() };
    assert_eq!((c.name().as_str(), c.k().as_str()), ("c", "1"));
    for (text, at) in [
        ("(check-system-response)", "check-system-response"),
        ("(check-system-response :verbosity full :verbosity full)", ":verbosity full)"),
        ("(check-system-response :verbosity terse)", "terse"),
        ("(check-system-response :verbosity full :query (q :model m))", "(q"),
        ("(check-system-response :verbosity full :query (q :result maybe))", "maybe"),
        ("(check-system-response :verbosity full :query (q :result sat :trace t :trace u))", ":trace u"),
        ("(check-system-response :verbosity full :query (q :result sat :witness w))", ":witness"),
        ("(check-system-response :verbosity full :trace (t :prefix p))", "(t"),
        ("(check-system-response :verbosity full :certificate (c :inv true))", "(c"),
        ("(check-system-response :verbosity full :certificate (c :inv true :k x))", "x)"),
        ("(check-system-response :verbosity full :trail (p ((x (a 1)))))", "x"),
        ("(check-system-response :verbosity full :trail (p ((0 (a)))))", "(a)"),
        ("(check-system-response :verbosity full :model (m (assert true)))", "assert"),
        ("(check-system-response :verbosity full :proof p)", ":proof"),
        ("(check-system-result :verbosity full)", "("),
    ] {
        let error = CheckSystemResponse::from_str(text).map(|r| panic!("read: {text}\n{r:?}")).unwrap_err();
        let column = text.rfind(at).map(|i| text[..i].chars().count() + 1).unwrap();
        let column = if at == "(" { 1 } else { column };
        assert_eq!((error.kind(), error.position().unwrap().column()), (ErrorKind::Syntax, column), "{error}\n{text}");
    }
    assert_eq!("(check-system-response :verbosity full) (x)".parse::<CheckSystemResponse>().unwrap_err().position().unwrap().column(), 41);
}
