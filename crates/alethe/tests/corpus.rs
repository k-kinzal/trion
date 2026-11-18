//! Proofs produced by cvc5 1.4.2 (`tests/corpus/*.cvc5.out`) for the
//! problems in `tests/corpus/*.smt2`: propositional, QF_UF, QF_LIA, QF_LRA,
//! QF_BV, quantified and incremental. The output splits into one proof per
//! printed proof, and every proof reads and prints back to an equal proof.

mod common;

use alethe::{read_output, read_proofs, ErrorKind, Proof, SolverResponse};
use common::*;
use smtlib::command::Command as ScriptCommand;
use smtlib::response::CheckSatResponse;

#[test]
fn the_corpus_covers_the_logics() {
    let logics: Vec<String> = supported_stems()
        .iter()
        .flat_map(|s| pairs(s).expect("the corpus entry"))
        .filter_map(|p| p.problem.commands().iter().find_map(|c| if let ScriptCommand::SetLogic(l) = c { Some(l.as_str().to_string()) } else { None }))
        .collect();
    for logic in ["QF_UF", "QF_LIA", "QF_LRA", "UFLRA", "LIA", "QF_BV"] {
        assert!(logics.iter().any(|l| l == logic), "no proof in {logic}");
    }
}

#[test]
fn every_proof_reads_and_prints_back() {
    let mut commands = 0;
    for stem in supported_stems() {
        let proofs = read_proofs(&output(&stem)).unwrap_or_else(|e| panic!("{stem}: {e}"));
        assert!(!proofs.is_empty(), "{stem}: no proof");
        for located in proofs {
            let proof: Proof = located.into_iter().map(|(_, c)| c).collect();
            let printed = proof.to_text();
            assert_eq!(Proof::parse(&printed).unwrap_or_else(|e| panic!("{stem}: {e}")), proof, "{stem}");
            commands += proof.commands().len();
        }
    }
    assert!(commands > 500, "{commands}");
}

#[test]
fn the_incremental_output_has_one_proof_per_printed_proof() {
    let responses: Vec<SolverResponse> = read_output(&output("incremental")).expect("the incremental entry").into_iter().map(|(_, r)| r).collect();
    let kinds: Vec<&str> = responses
        .iter()
        .map(|r| match r {
            SolverResponse::CheckSat(CheckSatResponse::Unsat) => "unsat",
            SolverResponse::Proof(_) => "proof",
            _ => "other",
        })
        .collect();
    // --dump-proofs prints a proof after each unsat and get-proof prints it again.
    assert_eq!(kinds, ["unsat", "proof", "proof", "unsat", "proof", "proof"]);
}

#[test]
fn unsupported_entries_are_reported_as_unsupported() {
    for (stem, why) in UNSUPPORTED {
        let error = read_proofs(&output(stem)).expect_err(why);
        assert_eq!(error.kind(), ErrorKind::Unsupported, "{stem}: {error}");
    }
}

#[test]
fn errors_in_output_carry_their_position() {
    let text = output("prop_or");
    assert!(text.contains(":premises (a0 t1)"));
    let line = text.lines().position(|l| l.contains(":premises (a0 t1)")).expect("the line") + 1;
    let error = read_proofs(&text.replace(":premises (a0 t1)", ":premises ()")).expect_err("an empty :premises");
    assert_eq!(error.kind(), ErrorKind::Syntax);
    assert_eq!(error.position().map(|p| p.line()), Some(line), "{error}");
}
