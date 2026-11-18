//! Reading a whole cvc5 session: SMT-LIB answers of every kind interleaved
//! with proofs, read for the commands that were sent, and in time linear in
//! the size of the output.
//!
//! `tests/sessions/interleaved.smt2` is answered by cvc5 1.4.2 with
//! `--incremental --proof-format-mode=cpc` (`interleaved.cvc5.out`) and with
//! `--dump-proofs` added (`interleaved.cvc5-dump.out`, where the proof comes
//! twice: after `unsat`, and for `get-proof`). `stored_sessions_are_current`
//! compares them with a live run, or rewrites them under
//! `CPC_UPDATE_CORPUS=1`.

mod common;

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use cpc::smtlib::response::{CheckSatResponse, ResponseKind, SpecificSuccessResponse};
use cpc::smtlib::{GeneralResponse, Script as SmtScript};
use cpc::{read_responses, read_session, Answer, Response, SessionOptions};
use eunoia::Position;

fn dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/sessions")
}

fn commands() -> Vec<cpc::smtlib::Command> {
    SmtScript::parse(&std::fs::read_to_string(dir().join("interleaved.smt2")).unwrap()).unwrap().into_commands()
}

const RUNS: [(&str, &[&str], bool); 2] = [("interleaved.cvc5.out", &["--incremental", "--proof-format-mode=cpc"], false), ("interleaved.cvc5-dump.out", &["--incremental", "--dump-proofs", "--proof-format-mode=cpc"], true)];

fn specific(a: &Answer) -> Option<&SpecificSuccessResponse> {
    match a.response() {
        Response::Smt(GeneralResponse::Specific(s)) => Some(s),
        _ => None,
    }
}

fn check_answers(answers: &[Answer], dump: bool) {
    let mut it = answers.iter();
    let mut next = || it.next().expect("an answer");
    assert_eq!(next().check_sat(), Some(CheckSatResponse::Sat));
    assert!(matches!(specific(next()), Some(SpecificSuccessResponse::GetValue(v)) if v.len() == 2));
    assert!(matches!(specific(next()), Some(SpecificSuccessResponse::GetModel(m)) if m.len() == 2));
    assert!(matches!(specific(next()), Some(SpecificSuccessResponse::GetInfo(_))));
    assert!(matches!(specific(next()), Some(SpecificSuccessResponse::Echo(s)) if s.to_string().contains("between")));
    let unsat = next();
    assert_eq!(unsat.check_sat(), Some(CheckSatResponse::Unsat));
    let proofs = if dump { 2 } else { 1 };
    for _ in 0..proofs {
        let p = next();
        let proof = p.proof().expect("a proof");
        assert!(proof.script().len() > 50);
        // the proof's commands are placed in the whole output, after the unsat
        assert!(proof.script().position(0).unwrap().line > unsat.position().line);
    }
    assert!(matches!(specific(next()), Some(SpecificSuccessResponse::GetInfo(_))));
}

#[test]
fn interleaved_answers_are_read_for_their_commands() {
    for (file, _, dump) in RUNS {
        let output = std::fs::read_to_string(dir().join(file)).unwrap();
        let answers = read_session(&output, &commands(), SessionOptions::new().with_dump_proofs(dump)).unwrap();
        check_answers(&answers, dump);
    }
}

#[test]
fn the_wrong_options_are_reported() {
    let output = std::fs::read_to_string(dir().join("interleaved.cvc5-dump.out")).unwrap();
    // read without --dump-proofs, the dumped proof is taken for the answer to
    // get-proof, and the real answer to get-proof is one too many
    let err = read_session(&output, &commands(), SessionOptions::new()).unwrap_err();
    assert!(matches!(err, cpc::OutputError::Response { .. } | cpc::OutputError::ExtraResponse(_)), "{err}");
}

#[test]
fn stored_sessions_are_current() {
    let Some(cvc5) = common::cvc5() else { return };
    let update = std::env::var_os("CPC_UPDATE_CORPUS").is_some_and(|v| v == "1");
    for (file, args, dump) in RUNS {
        let out = std::process::Command::new(&cvc5).args(args).arg(dir().join("interleaved.smt2")).output().expect("run cvc5");
        let text = String::from_utf8(out.stdout).unwrap();
        if update {
            std::fs::write(dir().join(file), &text).unwrap();
        } else {
            assert_eq!(text, std::fs::read_to_string(dir().join(file)).unwrap(), "{file}");
            check_answers(&read_session(&text, &commands(), SessionOptions::new().with_dump_proofs(dump)).unwrap(), dump);
        }
    }
}

/// An output of `n` check-sat answers, each followed by a dumped proof.
fn many(n: usize) -> (String, Vec<ResponseKind>) {
    let proof = "unsat\n(\n(declare-const p Bool)\n(assume @p1 p)\n(assume @p2 (not p))\n(step @p3 false :rule contra :premises (@p1 @p2))\n)\n";
    (proof.repeat(n), vec![ResponseKind::CheckSat; n])
}

fn time(n: usize) -> Duration {
    let (output, kinds) = many(n);
    let start = Instant::now();
    let answers = read_responses(&output, &kinds, SessionOptions::new().with_dump_proofs(true)).unwrap();
    let elapsed = start.elapsed();
    assert_eq!(answers.len(), 2 * n);
    assert_eq!(answers.last().and_then(|a| a.proof()).and_then(|p| p.script().position(3)), Some(Position::new(7 * n as u32 - 1, 1)));
    elapsed
}

/// 10 000 proofs are read in time linear in their number: ten times the
/// proofs take far less than the hundred times that a reader which re-reads
/// the output for every proof would take.
#[test]
fn ten_thousand_proofs_are_read_in_linear_time() {
    let small = (0..3).map(|_| time(1_000)).min().unwrap();
    let large = (0..3).map(|_| time(10_000)).min().unwrap();
    let ratio = large.as_secs_f64() / small.as_secs_f64().max(1e-6);
    eprintln!("1 000 proofs: {small:?}, 10 000 proofs: {large:?} (ratio {ratio:.1})");
    assert!(ratio < 30.0, "1 000 proofs: {small:?}, 10 000 proofs: {large:?} (ratio {ratio:.1})");
}
