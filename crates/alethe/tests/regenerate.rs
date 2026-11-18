//! Regenerates the cvc5 corpus and compares it with the stored outputs, so
//! that the corpus is what cvc5 1.4.2 prints and not an edited copy.

mod common;

use common::*;
use std::process::Command;

fn cvc5() -> std::path::PathBuf {
    let cvc5 = tool("cvc5");
    let version = Command::new(&cvc5).arg("--version").output().expect("cvc5 runs");
    let version = String::from_utf8_lossy(&version.stdout);
    assert!(version.starts_with("cvc5 1.4.2"), "the corpus was produced by cvc5 1.4.2, found: {}", version.lines().next().unwrap_or_default());
    cvc5
}

#[test]
#[ignore = "needs cvc5 (cvc5 1.4.2) in .tools/bin or on PATH; run with --include-ignored"]
fn the_corpus_is_what_cvc5_prints() {
    let cvc5 = cvc5();
    for stem in corpus_stems() {
        let output = Command::new(&cvc5).args(CVC5_FLAGS).arg(corpus_dir().join(format!("{stem}.smt2"))).output().expect("cvc5 runs");
        let mut printed = String::from_utf8(output.stdout).expect("utf-8");
        printed.push_str(&String::from_utf8_lossy(&output.stderr));
        assert_eq!(printed, common::output(&stem), "{stem}: cvc5 prints something else now");
    }
}

/// Fresh proofs from cvc5, not only the stored ones, read and print back.
#[test]
#[ignore = "needs cvc5 (cvc5 1.4.2) in .tools/bin or on PATH; run with --include-ignored"]
fn fresh_cvc5_proofs_read_back() {
    let cvc5 = cvc5();
    for stem in supported_stems() {
        let output = Command::new(&cvc5).args(CVC5_FLAGS).arg(corpus_dir().join(format!("{stem}.smt2"))).output().expect("cvc5 runs");
        for pair in split(&script(&stem), &String::from_utf8(output.stdout).expect("utf-8")).expect("split") {
            assert_eq!(alethe::Proof::parse(&pair.proof.to_text()).unwrap_or_else(|e| panic!("{stem}: {e}")), pair.proof, "{stem}");
        }
    }
}
