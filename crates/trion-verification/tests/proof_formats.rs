//! The Alethe and CPC proofs that `proof::derive` writes from the solver's
//! refutations, checked by the checkers of their formats: Carcara accepts
//! each Alethe proof as `valid` for its problem, and Ethos each CPC
//! document as `correct`, with the problem as its `reference`.
//!
//! The checkers are found in the repository's `.tools/bin`, then on `PATH`,
//! and the CPC signature of cvc5 1.4.2 in `.tools/cvc5-signature`; a test
//! without them fails, since a run without them checks nothing.

use proptest::prelude::*;
use std::path::{Path, PathBuf};
use trion_solver::{decide, Atom, Cmp, Formula, Status};
use trion_verification::proof::{self, Names};

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn tool(name: &str) -> PathBuf {
    let local = repository().join(".tools/bin").join(name);
    if local.is_file() {
        return local;
    }
    std::env::var_os("PATH").and_then(|paths| std::env::split_paths(&paths).map(|d| d.join(name)).find(|p| p.is_file())).unwrap_or_else(|| panic!("this test needs `{name}` in .tools/bin or on PATH"))
}

fn signature() -> PathBuf {
    let dir = repository().join(".tools/cvc5-signature");
    assert!(dir.join("Cpc.eo").is_file(), "this test needs proofs/eo/cpc of cvc5 1.4.2 in .tools/cvc5-signature");
    dir
}

fn run(tool: &Path, args: &[&Path]) -> String {
    let output = std::process::Command::new(tool).args(args).output().unwrap_or_else(|e| panic!("cannot run {}: {e}", tool.display()));
    format!("{}{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr))
}

/// Refutes `formulas` with the solver and has both checkers accept the proofs.
fn proved(formulas: &[Formula]) {
    let names = Names::of(&[formulas]);
    let answer = decide(formulas);
    assert_eq!(answer.status, Status::Unsatisfiable, "{formulas:?}");
    let refutation = answer.refutation().expect("an unsatisfiable answer has a refutation");
    let derivation = proof::derive(&names, formulas, refutation).unwrap_or_else(|e| panic!("{e}\n{formulas:?}"));
    let problem = proof::problem(&names, formulas, None).unwrap().to_string();
    let dir = tempfile::tempdir().unwrap();
    let smt2 = dir.path().join("p.smt2");
    std::fs::write(&smt2, &problem).unwrap();
    let alethe = dir.path().join("p.smt2.alethe");
    std::fs::write(&alethe, derivation.alethe().unwrap().to_text()).unwrap();
    let printed = run(&tool("carcara"), &[Path::new("check"), &alethe, &smt2]);
    assert_eq!(printed.trim(), "valid", "Carcara on\n{problem}\n{}\n{printed}", derivation.alethe().unwrap().to_text());
    #[cfg(unix)]
    std::os::unix::fs::symlink(signature(), dir.path().join("signature")).unwrap();
    let document = cpc::ProofDocument::new("signature", cpc::Variant::Cpc, derivation.cpc().unwrap()).and_then(|d| d.with_reference("p.smt2")).unwrap();
    let path = document.write(dir.path(), "p.cpc", Some(&problem)).unwrap();
    let printed = run(&tool("ethos"), &[&path]);
    assert_eq!(printed.trim(), "correct", "Ethos on\n{problem}\n{}\n{printed}", std::fs::read_to_string(&path).unwrap());
}

fn event(key: &str) -> Formula {
    Formula::Atom(Atom::Event { key: key.to_string() })
}

fn num(attr: &str, cmp: Cmp, n: i64) -> Formula {
    Formula::Atom(Atom::Num { attr: attr.to_string(), unit: "ms".to_string(), cmp, n })
}

fn lin(terms: &[(&str, i64)], cmp: Cmp, n: i64) -> Formula {
    Formula::Atom(Atom::Lin { terms: terms.iter().map(|(a, c)| (a.to_string(), *c)).collect(), unit: "ms".to_string(), cmp, n })
}

fn not(f: Formula) -> Formula {
    Formula::not(f)
}

#[test]
fn propositional_refutations() {
    let (a, b, c) = (event("a"), event("b"), event("c"));
    proved(&[a.clone(), Formula::implies(a.clone(), b.clone()), not(b.clone())]);
    proved(&[Formula::Or(vec![a.clone(), b.clone()]), not(a.clone()), not(b.clone())]);
    // Double negations, and a subformula written two ways.
    proved(&[not(not(a.clone())), Formula::Or(vec![not(a.clone()), b.clone(), not(a.clone())]), not(b.clone())]);
    proved(&[Formula::implies(a.clone(), b.clone()), not(Formula::Or(vec![not(a.clone()), b.clone()]))]);
    proved(&[Formula::And(vec![Formula::implies(a.clone(), b.clone()), a.clone()]), Formula::Or(vec![not(b.clone()), c.clone()]), not(c.clone())]);
    // `true`, and the empty conjunction and disjunction.
    proved(&[not(Formula::True)]);
    proved(&[Formula::Or(Vec::new())]);
    proved(&[not(Formula::And(Vec::new())), a.clone()]);
    proved(&[Formula::And(vec![a.clone()]), not(a.clone())]);
}

#[test]
fn pigeons_need_search() {
    let at = |p: usize, h: usize| event(&format!("p{p}h{h}"));
    let holes = 3;
    let mut formulas = Vec::new();
    for p in 0..=holes {
        formulas.push(Formula::Or((0..holes).map(|h| at(p, h)).collect()));
    }
    for h in 0..holes {
        for p in 0..=holes {
            for q in p + 1..=holes {
                formulas.push(not(Formula::And(vec![at(p, h), at(q, h)])));
            }
        }
    }
    proved(&formulas);
}

#[test]
fn arithmetic_refutations() {
    // Every comparison, as it stands and denied.
    for cmp in [Cmp::Le, Cmp::Lt, Cmp::Ge, Cmp::Gt, Cmp::Eq] {
        proved(&[num("x", cmp, 5), not(num("x", cmp, 5))]);
    }
    proved(&[num("x", Cmp::Lt, 3), num("x", Cmp::Gt, 1), not(num("x", Cmp::Eq, 2))]);
    proved(&[lin(&[("x", 1), ("y", -1)], Cmp::Lt, 0), lin(&[("y", 1), ("x", -1)], Cmp::Lt, 0)]);
    proved(&[lin(&[("x", 1), ("y", 1)], Cmp::Eq, 5), num("x", Cmp::Ge, 3), num("y", Cmp::Ge, 3)]);
    proved(&[lin(&[("x", 2), ("y", 3)], Cmp::Eq, 10), num("x", Cmp::Ge, 2), num("y", Cmp::Ge, 2), not(num("x", Cmp::Eq, 2))]);
    // Negative bounds and coefficients.
    proved(&[lin(&[("x", -2)], Cmp::Le, -5), num("x", Cmp::Lt, 3)]);
    proved(&[num("x", Cmp::Ge, -4), num("x", Cmp::Le, -4), not(num("x", Cmp::Eq, -4))]);
    // A disequality split twice.
    proved(&[num("x", Cmp::Ge, 0), num("x", Cmp::Le, 2), not(num("x", Cmp::Eq, 0)), not(num("x", Cmp::Eq, 1)), not(num("x", Cmp::Eq, 2))]);
    // Arithmetic under the propositional structure.
    proved(&[Formula::implies(event("a"), num("x", Cmp::Gt, 10)), event("a"), Formula::Or(vec![num("x", Cmp::Lt, 5), not(event("a"))])]);
}

#[test]
fn witness_checks_are_refuted() {
    let formulas = [Formula::implies(event("a"), num("x", Cmp::Gt, 10)), event("a"), lin(&[("x", 1), ("y", 1)], Cmp::Eq, 12)];
    let names = Names::of(&[&formulas]);
    let answer = decide(&formulas);
    assert_eq!(answer.status, Status::Satisfiable);
    let checked = names.assertions(&formulas, answer.witness());
    proved(&checked);
}

fn formula(depth: u32) -> impl Strategy<Value = Formula> {
    let atom = prop_oneof![
        prop::sample::select(vec!["a", "b", "c"]).prop_map(event),
        (prop::sample::select(vec!["x", "y"]), prop::sample::select(vec![Cmp::Le, Cmp::Lt, Cmp::Ge, Cmp::Gt, Cmp::Eq]), -2i64..3).prop_map(|(x, cmp, n)| num(x, cmp, n)),
        (-2i64..3, -2i64..3, prop::sample::select(vec![Cmp::Le, Cmp::Lt, Cmp::Eq]), -2i64..3).prop_map(|(a, b, cmp, n)| lin(&[("x", a), ("y", b)], cmp, n)),
    ];
    atom.prop_recursive(depth, 12, 3, |inner| {
        prop_oneof![
            inner.clone().prop_map(not),
            prop::collection::vec(inner.clone(), 0..3).prop_map(Formula::And),
            prop::collection::vec(inner.clone(), 0..3).prop_map(Formula::Or),
            (inner.clone(), inner).prop_map(|(a, b)| Formula::implies(a, b)),
        ]
    })
}

proptest! {
    // Each case runs both checkers; `PROPTEST_CASES` asks for more.
    #![proptest_config(ProptestConfig::with_cases(std::env::var("PROPTEST_CASES").ok().and_then(|n| n.parse().ok()).unwrap_or(48)))]

    // Whatever the solver refutes, both checkers accept the proofs of; a
    // satisfiable set has its witness check proved instead.
    #[test]
    fn every_refutation_is_accepted(formulas in prop::collection::vec(formula(3), 1..6)) {
        let answer = decide(&formulas);
        match answer.status {
            Status::Unsatisfiable => proved(&formulas),
            Status::Satisfiable => {
                let names = Names::of(&[&formulas]);
                proved(&names.assertions(&formulas, answer.witness()));
            }
            Status::Unknown => {}
        }
    }
}
