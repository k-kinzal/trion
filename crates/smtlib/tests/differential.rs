//! Differential tests against cvc5 1.4.2 and z3 4.15.4, found in the
//! repository's `.tools/bin`, then on `PATH`, with their versions checked.
//!
//! What each verdict covers:
//!
//! - `cvc5 --strict-parsing --parse-only` reads a script and checks its
//!   sorts, and nothing more. When it accepts a script this crate printed,
//!   the printed text is SMT-LIB that cvc5 reads; when it accepts a mangled
//!   text, that text is in the grammar, and this crate must read it too.
//!   When cvc5 rejects a text, the reason may be sorts or names, which this
//!   crate does not check, so a rejection is not compared.
//! - The responses z3 and cvc5 print are read by the response reader, with
//!   one response per command (`:print-success true`) or one per command
//!   that answers more than `success`.
//!
//! These tests run the tools, so they are ignored by default and run with
//! `cargo test -p smtlib -- --ignored`. Run that way, a missing tool or
//! another version fails the test with what is missing: a test never passes
//! without its tool.

mod common;

use common::{cvc5, sorted, z3, Tool};
use proptest::strategy::{Strategy, ValueTree};
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use smtlib::response::{GeneralResponse, ResponseKind, SpecificSuccessResponse};
use smtlib::{Command, Dialect, ErrorKind, Script};

const NEEDS_CVC5: &str = "needs cvc5 1.4.2 in .tools/bin or on PATH";

fn cvc5_parses(cvc5: &Tool, script: &str) -> (bool, String) {
    let (ok, out, err) = cvc5.run(&["--strict-parsing", "--parse-only", "--lang=smt2"], script);
    (ok && !out.contains("(error"), format!("{out}{err}"))
}

fn cvc5_session(cvc5: &Tool, script: &str) -> String {
    cvc5.run(&["--strict-parsing", "--incremental", "--lang=smt2", "--tlimit=20000"], script).1
}

fn z3_session(z3: &Tool, script: &str) -> String {
    z3.run(&["-in", "-smt2", "-T:20"], script).1
}

fn runner(cases: u32) -> TestRunner {
    TestRunner::new(Config { cases, failure_persistence: None, ..Config::default() })
}

/// Reads the responses `output` to `script`; panics with both when they do
/// not read.
fn responses(script: &Script, output: &str, print_success: bool) -> Vec<GeneralResponse> {
    GeneralResponse::parse_session(output, script.commands(), print_success, &Dialect::strict()).unwrap_or_else(|e| panic!("{script}\n--- output\n{output}\n--- {e}"))
}

// Scripts well sorted by construction, read and printed by this crate, are
// read by cvc5's strict parser.
#[test]
#[ignore = "needs cvc5 1.4.2 in .tools/bin or on PATH"]
fn cvc5_reads_what_this_crate_prints() {
    let cvc5 = cvc5();
    runner(64)
        .run(&sorted::script(), |text| {
            let script = Script::parse(&text).unwrap_or_else(|e| panic!("{text}\n{e}"));
            let printed = script.to_string();
            let (ok, output) = cvc5_parses(&cvc5, &printed);
            assert!(ok, "{NEEDS_CVC5}: cvc5 rejected a script this crate printed:\n{printed}\n{output}");
            Ok(())
        })
        .unwrap();
}

// The reference examples of Figure 3.11 and §3.6.5, printed by this crate,
// are read by cvc5.
#[test]
#[ignore = "needs cvc5 1.4.2 in .tools/bin or on PATH"]
fn cvc5_reads_printed_reference_scripts() {
    let cvc5 = cvc5();
    let scripts = [
        "(set-option :print-success true) (set-info :smt-lib-version 2.7) (set-logic QF_LIA) (declare-const w Int) (declare-const x Int) (declare-const y Int) (declare-const z Int) (assert (> x y)) (assert (> y z)) (push 1) (assert (> z x)) (check-sat) (get-info :all-statistics) (pop 1) (push 1) (check-sat) (exit)",
        "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int) (declare-const z Int) (assert (=> (! (> x y) :named p1) (! (= x z) :named p2))) (check-sat-assuming (p1 (not p2)))",
        "(set-logic QF_UF) (declare-const x Bool) (declare-const y Bool) (declare-const z Bool) (assert (=> x y z)) (assert (and x y z)) (assert (= x y z)) (assert (distinct x y z))",
        "(set-logic QF_LIA) (declare-const |x y| Int) (declare-const |abc| Int) (assert (> |x y| abc)) (assert (> |abc| 0))",
        "(set-logic ALL) (declare-datatype L ((nil) (cons (hd Int) (tl L)))) (declare-const l L) (assert (= 1 (match l ((nil 0) ((cons h t) 1))))) (check-sat)",
        "(set-logic ALL) (declare-fun f (Int) Int) (define-const c Int 3) (define-funs-rec ((g ((x Int)) Int)) ((ite (> x 0) (g (- x 1)) (f c)))) (assert (forall ((y Int)) (! (> (f y) 0) :pattern ((f y))))) (assert (let ((z 1)) (> (g z) 0)))",
    ];
    for text in scripts {
        let printed = Script::parse(text).unwrap().to_string();
        let (ok, output) = cvc5_parses(&cvc5, &printed);
        assert!(ok, "{printed}\n{output}");
    }
    // A quoted symbol that needs no quotes prints unquoted, and cvc5 reads
    // it as the same symbol: a redeclaration of abc as |abc| is an error.
    let twice = "(set-logic QF_LIA) (declare-const abc Int) (declare-const |abc| Int)";
    assert!(Script::parse(twice).unwrap().to_string().matches("abc").count() == 2);
    assert!(!cvc5_parses(&cvc5, twice).0);
}

// Mangled well-sorted scripts: whenever cvc5's strict parser accepts the
// text, this crate reads it too, and its print is read by cvc5 again.
#[test]
#[ignore = "needs cvc5 1.4.2 in .tools/bin or on PATH"]
fn what_cvc5_reads_this_crate_reads() {
    let cvc5 = cvc5();
    let edits = proptest::collection::vec((proptest::arbitrary::any::<proptest::sample::Index>(), 0u8..3, proptest::sample::select(vec!['(', ')', '|', ' ', '_', '!', '0', 'x', ':', '-'])), 1..4);
    let accepted = std::cell::Cell::new(0);
    // A fixed seed, so that the number of texts cvc5 reads is the same on
    // every run.
    let config = Config { cases: 1000, failure_persistence: None, ..Config::default() };
    TestRunner::new_with_rng(config, TestRng::deterministic_rng(RngAlgorithm::ChaCha))
        .run(&(sorted::script(), edits), |(text, edits): (String, Vec<(proptest::sample::Index, u8, char)>)| {
            let mut chars: Vec<char> = text.chars().collect();
            for (at, edit, c) in edits {
                let i = at.index(chars.len());
                match edit {
                    0 => {
                        chars.remove(i);
                    }
                    1 => chars.insert(i, chars[i]),
                    _ => chars[i] = c,
                }
            }
            let mangled: String = chars.into_iter().collect();
            if cvc5_parses(&cvc5, &mangled).0 {
                accepted.set(accepted.get() + 1);
                let script = Script::parse(&mangled).unwrap_or_else(|e| panic!("cvc5 reads a text this crate rejects:\n{mangled}\n{e}"));
                let (ok, output) = cvc5_parses(&cvc5, &script.to_string());
                assert!(ok, "cvc5 reads the text but not its print:\n{mangled}\n{script}\n{output}");
            }
            Ok(())
        })
        .unwrap();
    // The comparison is empty unless some mangled texts are still read.
    eprintln!("cvc5 read {} of 1000 mangled texts", accepted.get());
    assert!(accepted.get() >= 50, "only {} mangled texts were read by cvc5", accepted.get());
}

/// A session that asks for every response kind z3 answers in the 2.7
/// grammar. Not included: `echo` (z3 prints the string without its quotes,
/// which is not a ⟨string⟩).
const SESSION: &str = "(set-option :print-success true)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :produce-unsat-assumptions true)
(set-option :produce-assignments true)
(set-option :produce-assertions true)
(set-option :produce-proofs true)
(set-info :smt-lib-version 2.7)
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const p Bool)
(define-fun g ((a Int)) Int (+ a 1))
(assert (! (> x (g y)) :named a1))
(assert (! (= (f x) (- 3)) :named a2))
(check-sat)
(get-model)
(get-value (x (+ x y) (f x) p (- 3)))
(get-assignment)
(get-assertions)
(get-info :name)
(get-info :version)
(get-info :authors)
(get-info :error-behavior)
(get-info :assertion-stack-levels)
(get-option :produce-models)
(get-option :random-seed)
(get-option :verbosity)
(push 1)
(assert (! (< x y) :named a3))
(check-sat)
(get-unsat-core)
(get-proof)
(pop 1)
(check-sat-assuming (a1 (not p)))
(get-unsat-assumptions)
(get-info :all-statistics)
(get-info :reason-unknown)
(reset-assertions)
(exit)";

fn count(responses: &[GeneralResponse], f: impl Fn(&GeneralResponse) -> bool) -> usize {
    responses.iter().filter(|r| f(r)).count()
}

#[test]
#[ignore = "needs z3 4.15.4 in .tools/bin or on PATH"]
fn z3_session_responses_read() {
    let z3 = z3();
    let script = Script::parse(SESSION).unwrap();
    let output = z3_session(&z3, SESSION);
    let read = responses(&script, &output, true);
    assert_eq!(read.len(), script.commands().len());
    // z3 answers every command but get-unsat-assumptions after sat.
    assert_eq!(count(&read, |r| matches!(r, GeneralResponse::Error(_))), 1, "{output}");
    assert!(read.iter().any(|r| matches!(r, GeneralResponse::Specific(SpecificSuccessResponse::GetModel(m)) if !m.is_empty())));
    assert!(read.iter().any(|r| matches!(r, GeneralResponse::Specific(SpecificSuccessResponse::GetValue(v)) if v.len() == 5)));
    assert!(read.iter().any(|r| matches!(r, GeneralResponse::Specific(SpecificSuccessResponse::GetUnsatCore(c)) if c.len() == 2)));
    assert!(read.iter().any(|r| matches!(r, GeneralResponse::Specific(SpecificSuccessResponse::GetProof(_)))));
    assert_eq!(count(&read, |r| matches!(r, GeneralResponse::Success)), 21, "{output}");
}

#[test]
#[ignore = "needs cvc5 1.4.2 in .tools/bin or on PATH"]
fn cvc5_session_responses_read() {
    let cvc5 = cvc5();
    // cvc5 prints get-proof in its own proof format, as a sequence of
    // S-expressions; its :error-behavior is immediate-exit, so
    // get-unsat-assumptions after sat (an error) ends the session; its
    // :all-statistics value contains `{ … }`, which is not an S-expression.
    // These three are left out. get-assertions is kept: cvc5 prints the
    // defined function with lambda (SMT-LIB 2.7).
    let left_out = ["(get-proof", "(get-unsat-assumptions", "(get-info :all-statistics"];
    let text: String = SESSION.lines().filter(|l| !left_out.iter().any(|c| l.starts_with(c))).collect::<Vec<_>>().join("\n");
    let script = Script::parse(&text).unwrap();
    let output = cvc5_session(&cvc5, &text);
    let read = responses(&script, &output, true);
    assert_eq!(read.len(), script.commands().len());
    // The one error: get-info :reason-unknown when the last answer was not
    // unknown.
    assert_eq!(count(&read, |r| matches!(r, GeneralResponse::Error(_))), 1, "{output}");
    assert!(read.iter().any(|r| matches!(r, GeneralResponse::Specific(SpecificSuccessResponse::GetModel(m)) if !m.is_empty())));
    assert!(read.iter().any(|r| matches!(r, GeneralResponse::Specific(SpecificSuccessResponse::GetUnsatCore(c)) if c.len() == 2)));
}

// Models and values for generated scripts, from both solvers: get-model and
// get-value after every check-sat (an error after unsat is a valid
// response). With :print-success true every command has exactly one
// response, so an error is attributed to its command.
#[test]
#[ignore = "needs z3 4.15.4 and cvc5 1.4.2 in .tools/bin or on PATH"]
fn generated_models_read() {
    let (z3, cvc5) = (z3(), cvc5());
    runner(24)
        .run(&sorted::script(), |text| {
            let mut session = String::from("(set-option :print-success true)\n(set-option :produce-models true)\n");
            for line in text.lines() {
                session.push_str(line);
                session.push('\n');
                if line == "(check-sat)" {
                    session.push_str("(get-model)\n(get-value (x0 (+ x1 |x 2|) (f x0) b0))\n");
                }
            }
            let script = Script::parse(&session).unwrap();
            for (solver, output) in [("z3", z3_session(&z3, &session)), ("cvc5", cvc5_session(&cvc5, &session))] {
                let read = responses(&script, &output, true);
                let mut models = 0;
                for (command, response) in script.commands().iter().zip(&read) {
                    match response {
                        GeneralResponse::Specific(SpecificSuccessResponse::GetValue(pairs)) => assert_eq!(pairs.len(), 4),
                        GeneralResponse::Specific(SpecificSuccessResponse::GetModel(_)) => models += 1,
                        GeneralResponse::Error(message) => assert!(matches!(command, Command::GetModel | Command::GetValue(_)), "{solver}: {command}: {message}\n{output}"),
                        _ => {}
                    }
                }
                assert!(models > 0 || !output.contains("\nsat"), "{solver}\n{output}");
            }
            Ok(())
        })
        .unwrap();
}

// cvc5's model for a declared sort is in the 2.7 grammar (abstract values
// in `as`); z3's is not: it contains declare-fun and a forall cardinality
// constraint, which ⟨model_response⟩ does not admit, and the reader rejects
// it at its position. get-value is in the grammar for both.
#[test]
#[ignore = "needs z3 4.15.4 and cvc5 1.4.2 in .tools/bin or on PATH"]
fn models_with_declared_sorts() {
    let (z3, cvc5) = (z3(), cvc5());
    let text = "(set-option :produce-models true) (set-logic QF_UF) (declare-sort U 0) (declare-const a U) (declare-const b U) (declare-fun f (U) U) (assert (distinct a b (f a))) (check-sat) (get-model) (get-value (a (f b)))";
    let script = Script::parse(text).unwrap();
    let (_, output, _) = cvc5.run(&["--strict-parsing", "--lang=smt2"], text);
    responses(&script, &output, false);
    let output = z3_session(&z3, text);
    let error = GeneralResponse::parse_session(&output, script.commands(), false, &Dialect::strict()).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Syntax, "{error}");
    assert!(error.position().is_some_and(|p| p.line() > 1), "{error}");
    let nodes = smtlib::sexpr::read_all(&output, &Dialect::strict()).unwrap();
    let value = GeneralResponse::from_spanned(&nodes[2], ResponseKind::GetValue).unwrap();
    assert!(matches!(value, GeneralResponse::Specific(SpecificSuccessResponse::GetValue(_))));
}

// The generator of the tests above gives scripts that this crate reads and
// prints back (this one needs no tool).
#[test]
fn the_sorted_generator_gives_scripts_this_crate_reads() {
    let mut runner = runner(1);
    for _ in 0..32 {
        let text = sorted::script().new_tree(&mut runner).unwrap().current();
        let script = Script::parse(&text).unwrap_or_else(|e| panic!("{text}\n{e}"));
        assert_eq!(script.to_string().parse::<Script>().unwrap(), script);
    }
}

// Without its tool, a test that needs it fails, naming what is missing.
#[test]
#[should_panic(expected = "is needed in .tools/bin or on PATH")]
fn a_missing_tool_fails_the_test() {
    common::tool("smtlib-test-no-such-tool", &["--version"], "1.0");
}

// A tool of another version fails the test too.
#[test]
#[ignore = "needs z3 4.15.4 in .tools/bin or on PATH"]
#[should_panic(expected = "z3 0.0.1 is needed")]
fn another_version_fails_the_test() {
    common::tool("z3", &["--version"], "0.0.1");
}
