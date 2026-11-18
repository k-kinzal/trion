//! Real CPC proofs of cvc5 1.4.2, stored in `tests/data` next to the SMT-LIB
//! problems they prove: they must be read (for the commands of the problem)
//! and printed back to equal commands, and the documents built from them must
//! have the form of `cpc_gen.sh`'s. Whether Ethos accepts them is
//! `tests/ethos.rs`.
//!
//! The stored outputs (`<stem>.cvc5.out`, and `<stem>.cvc5-ref.out` with
//! `--proof-print-reference`) are compared with a live run of cvc5 1.4.2 by
//! `cvc5_output_is_current`; with the environment variable
//! `CPC_UPDATE_CORPUS=1` that test rewrites them instead, which is how the
//! corpus is regenerated after adding a problem:
//!
//! ```text
//! CPC_UPDATE_CORPUS=1 cargo test -p cpc --test proofs cvc5_output_is_current
//! ```
//!
//! cvc5, which is not in the repository, is found at run time; see `common`.

mod common;

use common::{commands, data, documents, documents_of, options, problems, read, runs};
use cpc::{read_proofs, read_session, ProofDocument, Variant};
use eunoia::{parse_script, Script};

#[test]
fn the_problems_cover_the_logics() {
    let all = problems().iter().map(|s| read(s, "smt2")).collect::<Vec<_>>().join("\n");
    for logic in ["QF_UF", "QF_LIA", "QF_UFLIA"] {
        assert!(all.contains(&format!("(set-logic {logic})")), "{logic}");
    }
    assert!(problems().len() >= 8);
}

#[test]
fn every_output_is_one_unsat_and_one_proof_per_query() {
    for stem in problems() {
        let answers = read_session(&read(&stem, "cvc5.out"), &commands(&stem), options(&stem, "cvc5.out")).unwrap();
        let queries = if stem == "incremental" { 2 } else { 1 };
        assert_eq!(answers.len(), 2 * queries, "{stem}");
        for pair in answers.chunks(2) {
            assert_eq!(pair[0].check_sat(), Some(cpc::smtlib::response::CheckSatResponse::Unsat), "{stem}");
            assert!(pair[1].proof().is_some_and(|p| !p.script().is_empty()), "{stem}");
        }
    }
}

#[test]
fn every_proof_round_trips() {
    for stem in problems() {
        for doc in documents(&stem) {
            let text = doc.to_string();
            let script = parse_script(&text).unwrap_or_else(|e| panic!("{stem}: {e}\n{text}"));
            assert_eq!(script, doc.to_script(), "{stem}");
            assert_eq!(&script.commands()[2..], doc.body().commands(), "{stem}");
        }
    }
}

#[test]
fn every_document_claims_false() {
    for stem in problems() {
        let docs = documents(&stem);
        assert!(!docs.is_empty(), "{stem}");
        for doc in docs {
            assert!(!doc.is_empty() && doc.claims_false(), "{stem}");
        }
    }
}

/// The documents of `cpc_gen.sh` are the include lines followed by the lines of
/// cvc5's output without the first two and the last; they read as the same
/// commands as ours.
#[test]
fn documents_agree_with_cpc_gen() {
    for stem in problems().into_iter().filter(|s| s != "incremental") {
        let out = read(&stem, "cvc5.out");
        let lines: Vec<&str> = out.lines().collect();
        let gen = format!("(include \"/cpc/Cpc.eo\")\n(include \"/cpc/expert/CpcExpert.eo\")\n{}\n", lines[2..lines.len() - 1].join("\n"));
        let ours = documents(&stem).remove(0);
        assert_eq!(parse_script(&gen).unwrap(), ours.to_script(), "{stem}");
    }
}

#[test]
fn incremental_output_splits_into_two_documents() {
    let docs = documents("incremental");
    assert_eq!(docs.len(), 2);
    assert_ne!(docs[0].body(), docs[1].body());
    // Positions are those of the whole output: the second proof starts after the first.
    let last_of_first = docs[0].body().iter().last().and_then(|(p, _)| p).unwrap();
    assert!(docs[1].body().position(0).unwrap().line > last_of_first.line);
}

#[test]
fn reference_documents() {
    for stem in problems().into_iter().filter(|s| s != "incremental") {
        let docs = documents_of(&stem, "cvc5-ref.out", "/cpc", Variant::Expert);
        assert_eq!(docs.len(), 1, "{stem}");
        let doc = docs.into_iter().next().unwrap().with_reference(&format!("{stem}.smt2")).unwrap();
        let text = doc.to_string();
        assert!(text.contains(&format!("(reference \"{stem}.smt2\")")), "{stem}");
        assert_eq!(parse_script(&text).unwrap(), doc.to_script());
        // A proof that declares its symbols cannot reference the problem.
        assert!(documents(&stem).remove(0).with_reference("x.smt2").is_err(), "{stem}");
    }
}

#[test]
fn writing_a_reference_document_writes_the_problem() {
    let dir = std::env::temp_dir().join(format!("cpc-doc-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let problem = read("prop", "smt2");
    let doc = documents_of("prop", "cvc5-ref.out", "/cpc", Variant::Expert).remove(0).with_reference("prop.smt2").unwrap();
    assert!(doc.write(&dir, "prop.eo", None).is_err());
    let path = doc.write(&dir, "prop.eo", Some(&problem)).unwrap();
    assert_eq!(std::fs::read_to_string(dir.join("prop.smt2")).unwrap(), problem);
    assert_eq!(parse_script(&std::fs::read_to_string(path).unwrap()).unwrap(), doc.to_script());
    std::fs::remove_dir_all(&dir).unwrap();
}

/// Neither the document nor the problem it references can be written outside
/// the directory given to `write`.
#[test]
fn documents_are_written_inside_their_directory() {
    let doc = documents_of("prop", "cvc5-ref.out", "/cpc", Variant::Expert).remove(0);
    for bad in ["../x.smt2", "/tmp/x.smt2", "", "a/../../x.smt2"] {
        assert!(matches!(doc.clone().with_reference(bad), Err(cpc::DocumentError::OutsideDirectory(_))), "{bad:?}");
    }
    assert!(matches!(doc.clone().with_reference("é.smt2"), Err(cpc::DocumentError::NotAscii(_))));
    let dir = std::env::temp_dir().join(format!("cpc-doc-escape-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    for bad in ["../escape.eo", "/tmp/escape.eo", ""] {
        let err = doc.write(&dir, bad, None).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput, "{bad:?}");
    }
    assert!(doc.write(&dir, "sub.eo", None).is_ok());
    std::fs::remove_dir_all(&dir).unwrap();
}

/// A document built without cvc5, from a script the caller writes.
#[test]
fn documents_can_be_built_programmatically() {
    let body = parse_script("(declare-const p Bool)\n(assume @p1 p)\n(assume @p2 (not p))\n(step @p3 false :rule contra :premises (@p1 @p2))").unwrap();
    let doc = ProofDocument::new("/cpc/", Variant::Cpc, body).unwrap();
    assert_eq!(doc.signature_dir(), "/cpc/");
    assert_eq!(doc.header().len(), 1);
    assert!(doc.to_string().starts_with("(include \"/cpc/Cpc.eo\")\n(declare-const p Bool)\n"));
    assert!(doc.claims_false());
    assert!(matches!(ProofDocument::new("/é", Variant::Cpc, Script::default()), Err(cpc::DocumentError::NotAscii(_))));
    let expert = ProofDocument::new("/cpc", Variant::Expert, doc.body().clone()).unwrap();
    assert!(expert.to_string().starts_with("(include \"/cpc/Cpc.eo\")\n(include \"/cpc/expert/CpcExpert.eo\")\n"));
}

// ------------------------------------------------------------ live cvc5

/// The stored outputs are what cvc5 1.4.2 prints today; with
/// `CPC_UPDATE_CORPUS=1` they are rewritten from it.
#[test]
fn cvc5_output_is_current() {
    let Some(cvc5) = common::cvc5() else { return };
    let update = std::env::var_os("CPC_UPDATE_CORPUS").is_some_and(|v| v == "1");
    for stem in problems() {
        let problem = data().join(format!("{stem}.smt2"));
        for (suffix, args, options) in runs(&stem) {
            let out = std::process::Command::new(&cvc5).args(&args).arg(&problem).output().expect("run cvc5");
            let text = String::from_utf8(out.stdout).unwrap();
            if update {
                std::fs::write(data().join(format!("{stem}.{suffix}")), &text).unwrap();
            } else {
                let commands = commands(&stem);
                assert_eq!(read_proofs(&text, &commands, options).unwrap(), read_proofs(&read(&stem, suffix), &commands, options).unwrap(), "{stem} {suffix}");
            }
        }
    }
}
