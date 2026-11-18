//! Property tests of the reader of cvc5's output and of proof documents.
//!
//! - Concatenating any sequence of the stored cvc5 outputs, with whitespace,
//!   comments and the answers of other commands between them, reads back as
//!   the same proofs in the same order, given the concatenated commands.
//! - A proof document prints to text that reads back as the same script, for
//!   any signature directory and either variant.
//! - The reader never panics, on random text and on stored outputs mangled
//!   by edits.

use cpc::smtlib::response::ResponseKind;
use cpc::{read_proofs, read_responses, ProofDocument, SessionOptions, Variant};
use eunoia::parse_script;
use proptest::prelude::*;

mod common;

/// The stored outputs with what the reader needs: the response kinds and options.
fn outputs() -> &'static Vec<(String, Vec<ResponseKind>, SessionOptions)> {
    static OUT: std::sync::OnceLock<Vec<(String, Vec<ResponseKind>, SessionOptions)>> = std::sync::OnceLock::new();
    OUT.get_or_init(|| {
        let mut out = Vec::new();
        for stem in common::problems() {
            let kinds: Vec<ResponseKind> = common::commands(&stem).iter().map(ResponseKind::of).collect();
            for (suffix, _, options) in common::runs(&stem) {
                out.push((common::read(&stem, suffix), kinds.clone(), options));
            }
        }
        out
    })
}

/// Text between two outputs, with the response kinds of the commands it answers.
fn separator() -> impl Strategy<Value = Vec<(&'static str, Option<ResponseKind>)>> {
    prop::collection::vec(
        prop::sample::select(vec![(" ", None), ("\n", None), ("\t", None), ("; a comment ( \" |\n", None), ("sat\n", Some(ResponseKind::CheckSat)), ("(error \"x ) \"\"y\"\"\")\n", Some(ResponseKind::GetModel)), ("(:reason-unknown incomplete)\n", Some(ResponseKind::GetInfo)), ("((x 1))\n", Some(ResponseKind::GetValue)), ("\"echoed\"\n", Some(ResponseKind::Echo))]),
        0..4,
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn concatenated_outputs_split(picks in prop::collection::vec((0..outputs().len(), separator()), 1..5)) {
        // every stored output is read with dump-proofs or without; one session has one setting
        let dump = outputs()[picks[0].0].2;
        let picks: Vec<_> = picks.into_iter().filter(|(k, _)| outputs()[*k].2 == dump).collect();
        let mut text = String::new();
        let mut kinds = Vec::new();
        let mut expected = Vec::new();
        for (k, sep) in &picks {
            for (t, kind) in sep {
                text.push_str(t);
                kinds.extend(kind);
            }
            let (out, ks, options) = &outputs()[*k];
            text.push_str(out);
            kinds.extend(ks.iter().copied());
            let alone = read_responses(out, ks, *options).unwrap();
            expected.extend(alone.into_iter().filter_map(|a| a.proof().map(|p| p.script().clone())));
        }
        let got: Vec<_> = read_responses(&text, &kinds, dump).unwrap().into_iter().filter_map(|a| a.proof().map(|p| p.script().clone())).collect();
        prop_assert_eq!(got, expected);
    }

    #[test]
    fn documents_round_trip(k in 0..outputs().len(), dir in "[a-zA-Z0-9_./ -]{0,12}", expert in any::<bool>()) {
        let variant = if expert { Variant::Expert } else { Variant::Cpc };
        let (out, kinds, options) = &outputs()[k];
        for answer in read_responses(out, kinds, *options).unwrap() {
            let Some(proof) = answer.proof() else { continue };
            let doc = ProofDocument::from_proof(proof.clone(), &dir, variant).unwrap();
            let text = doc.to_string();
            prop_assert_eq!(parse_script(&text).unwrap(), doc.to_script());
        }
    }

    #[test]
    fn the_reader_does_not_panic(text in "(?s:.{0,200})", kinds in prop::collection::vec(prop::sample::select(vec![ResponseKind::General, ResponseKind::CheckSat, ResponseKind::GetProof, ResponseKind::GetValue, ResponseKind::GetModel, ResponseKind::GetInfo, ResponseKind::Echo]), 0..6), dump in any::<bool>(), success in any::<bool>()) {
        let _ = read_responses(&text, &kinds, SessionOptions::new().with_dump_proofs(dump).with_print_success(success));
    }

    #[test]
    fn mangled_outputs_do_not_panic(k in 0..outputs().len(), edits in prop::collection::vec((any::<prop::sample::Index>(), 0u8..3, prop::sample::select(vec!['(', ')', '|', '"', ';', ' ', '\n', 'é', 'x'])), 1..6)) {
        let (out, kinds, options) = &outputs()[k];
        let mut chars: Vec<char> = out.chars().collect();
        for (at, kind, c) in edits {
            let i = at.index(chars.len() + 1);
            match kind {
                0 => chars.insert(i, c),
                1 if i < chars.len() => { chars.remove(i); }
                _ => chars.truncate(i),
            }
        }
        let text: String = chars.into_iter().collect();
        let _ = read_responses(&text, kinds, *options);
        let _ = read_proofs(&text, &[], *options);
    }
}
