//! Differential test against Ethos 0.2.5 (commit
//! 08e4aa40c4f8a6e00833f10e8d8985777e424027, the version cvc5 1.4.2 pins;
//! `.tools/bin/ethos`, else `ethos` on `PATH`; found at run time, see
//! `common`), with the documents including the official
//! signature of cvc5 1.4.2 from `.tools/cvc5-signature`: every proof document this crate builds from the
//! stored cvc5 outputs must be accepted by `ethos`, which prints `correct` for a
//! checked proof without `:sorry` steps (`src/main.cpp`), both standalone and
//! with a `reference` to the problem. Mutated documents that the static check
//! refuses must be refused by Ethos too.

use std::path::{Path, PathBuf};
use std::process::Command as Process;

use common::{documents_of, problems, read};
use cpc::Variant;
use eunoia::parse_script;

mod common;

fn run(ethos: &Path, file: &Path) -> (bool, String) {
    let out = Process::new(ethos).arg(file).output().expect("run ethos");
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    (out.status.success() && text.lines().any(|l| l.trim() == "correct"), text)
}

fn workdir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("cpc-ethos-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn ethos_accepts_our_documents() {
    let (Some(ethos), Some(sig)) = (common::ethos(), common::signature_dir()) else { return };
    let sig = sig.to_str().unwrap();
    let dir = workdir("accept");
    for stem in problems() {
        for (k, doc) in documents_of(&stem, "cvc5.out", sig, Variant::Expert).into_iter().enumerate() {
            let path = doc.write(&dir, &format!("{stem}-{k}.eo"), None).unwrap();
            let (ok, text) = run(&ethos, &path);
            assert!(ok, "{stem} #{k}: {text}");
        }
        if stem == "incremental" {
            continue;
        }
        let problem = read(&stem, "smt2");
        let doc = documents_of(&stem, "cvc5-ref.out", sig, Variant::Expert).remove(0).with_reference(&format!("{stem}.smt2")).unwrap();
        let path = doc.write(&dir, &format!("{stem}-ref.eo"), Some(&problem)).unwrap();
        let (ok, text) = run(&ethos, &path);
        assert!(ok, "{stem} (reference): {text}");
    }
    std::fs::remove_dir_all(&dir).unwrap();
}

/// The defects that the format does not catch, and Ethos does: each mutation
/// of a real proof reads and prints, and Ethos refuses it.
#[test]
fn ethos_refuses_mutated_documents() {
    let (Some(ethos), Some(sig)) = (common::ethos(), common::signature_dir()) else { return };
    let dir = workdir("refuse");
    let doc = documents_of("prop", "cvc5.out", sig.to_str().unwrap(), Variant::Expert).remove(0);
    let text = doc.to_string();
    let mutations = [
        ("undeclared-rule", text.replacen(":rule chain_resolution", ":rule no_such_rule", 1)),
        ("dangling-premise", text.replacen(":premises (@p3 @p4)", ":premises (@p3 @p999)", 1)),
        ("missing-premise", text.replacen(":premises (@p3 @p4)", ":premises (@p3)", 1)),
        ("extra-argument", text.replacen(":rule cnf_or_pos :args (", ":rule cnf_or_pos :args (true ", 1)),
        ("undeclared-symbol", text.replacen("(declare-const", "(declare-const zz Bool)\n(assume @zz (and zz qq))\n(declare-const", 1)),
        ("unclosed-assume-push", format!("{text}(assume-push @extra true)\n")),
        ("step-pop-at-level-zero", format!("{text}(step-pop @closing (=> true false) :rule scope :premises (@p1))\n")),
    ];
    for (name, mutated) in mutations {
        assert_ne!(mutated, text, "{name}: the mutation applies");
        assert!(parse_script(&mutated).is_ok(), "{name}: the format reads it");
        let path = dir.join(format!("{name}.eo"));
        std::fs::write(&path, &mutated).unwrap();
        let (ok, out) = run(&ethos, &path);
        assert!(!ok, "{name}: Ethos accepted it: {out}");
    }
    std::fs::remove_dir_all(&dir).unwrap();
}
