//! Differential test against Carcara's development branch at commit
//! `20bf49c5ce31089ac83118574c888669355aaae1` (`carcara --version` prints
//! "carcara 1.1.0 [git 20bf49c master]"; the version number is not enough
//! to tell it from the 1.1.0 release, so the test checks the hash), the
//! proof checker the specification's authors maintain. Paths below are
//! relative to that commit's tree.
//!
//! This crate reads and writes the syntax only; Carcara is the second and
//! third stage (static validity and proof checking) of what this crate
//! prints. Carcara takes a problem file and a proof file; storing them is
//! not the crate's business, so this test writes them itself
//! (`common::write`): the problem with `smtlib`'s printer, the proof with
//! [`alethe::Proof::to_text`].
//!
//! - every problem and proof the test writes for the cvc5 corpus must be accepted
//!   by `carcara check` (as `valid` or `holey`: cvc5 1.4.2 proofs contain
//!   holes), unless the pair is listed in [`EXPECTED`] with a recorded
//!   [`Refusal`], in which case Carcara must refuse it with exactly that
//!   error and the pair must contain the construct it is about;
//! - mutations of those pairs, built with this crate's constructors and
//!   written by its printer, must be refused by Carcara, each for the
//!   mutation's own reason (or a recorded refusal), and each kind of
//!   mutation for its own reason at least once;
//! - Carcara's reading of the bit-vector constant of §4.1 is recorded
//!   ([`the_bit_vector_constant_of_section_4_1`]).
//!
//! A proof's problem is the script up to the check command the proof
//! answers (`common::split`). Carcara reads declarations,
//! definitions, `assert`, `check-sat-assuming` and `set-logic` and ignores
//! every other command (`src/parser/mod.rs`, `parse_problem`: "All other
//! commands are ignored"), so it does not undo the assertions of a `pop`:
//! for the later proofs of `incremental` it also admits assumptions of
//! popped assertions. The verdict on those pairs covers less than on the
//! others.
//!
//! When Carcara changes, the test fails on [`EXPECTED`], which must then be
//! updated.
//!
//! The flags: `--expand-let-bindings` (cvc5 prints assumptions with lets
//! expanded; `src/bin/cli/app.rs`, `expand_let_bindings`) and
//! `--ignore-unknown-rules` (cvc5 uses rules outside the rule list of
//! §5.2; Carcara then treats the ones it does not know as holes; `src/bin/cli/app.rs`, `ignore_unknown_rules`;
//! `src/checker/mod.rs`, `ignore_unknown_rules`). Carcara knows
//! `rare_rewrite`, so that rule is checked, not ignored (see
//! [`Refusal::RareRewriteRules`]).

mod common;

use alethe::{Assume, Command, Proof, Step};
use common::*;
use smtlib::term::NonEmpty;
use std::path::Path;
use std::process::Command as Process;

/// A recorded reason for which Carcara refuses a pair this crate writes
/// from cvc5's output.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Refusal {
    /// cvc5 1.4.2 writes steps with the rule `rare_rewrite`, which is not
    /// in the document's rule list (§5.2 has no such rule, and the document
    /// does not mention RARE). Carcara knows the rule
    /// (`src/checker/rules/mod.rs`, `"rare_rewrite" => rare::check_rare`)
    /// and checks the step against the rewrite rule its first argument
    /// names, taken from a file given with `--rare-file`
    /// (`docs/src/checking/rare.md`: "Carcara will only be able to check
    /// your proofs if every rewrite rule mentioned in the Alethe file is
    /// also present in your rare file"). The rules cvc5 1.4.2 uses are
    /// defined in cvc5's sources, which this repository does not have, so
    /// no file is given, and Carcara refuses the step
    /// (`src/checker/rules/rare.rs`, `RareRuleNotFound`: "the rule {0} was
    /// not found").
    RareRewriteRules,
}

impl Refusal {
    const ALL: [Refusal; 1] = [Refusal::RareRewriteRules];

    /// Whether Carcara's output is this refusal's error.
    fn explains(self, output: &str) -> bool {
        match self {
            Refusal::RareRewriteRules => output.contains("error: the rule ") && output.contains(" was not found") && output.contains("with rule rare_rewrite"),
        }
    }

    /// Whether the proof text has the construct.
    fn present(self, proof: &str) -> bool {
        match self {
            Refusal::RareRewriteRules => proof.lines().any(|l| l.contains(":rule rare_rewrite :args (\"")),
        }
    }
}

/// The outcome of `carcara check` on each written pair, by file stem: `None`
/// for accepted, or the recorded refusal.
const EXPECTED: &[(&str, Option<Refusal>)] = &[
    ("bv_congruence", None),
    ("bv_hexadecimal", None),
    ("incremental-1", None),
    ("incremental-2", None),
    ("incremental-3", None),
    ("incremental-4", None),
    ("lia_bounds", None),
    ("lia_ite", Some(Refusal::RareRewriteRules)),
    ("lia_negative", None),
    ("lra_bounds", None),
    ("prop_implies_chain", None),
    ("prop_named_let", None),
    ("prop_or", None),
    ("prop_pigeon", None),
    ("quant_implies", None),
    ("quant_instance", None),
    ("quant_lia", None),
    ("quant_skolem", None),
    ("uf_congruence", None),
    ("uf_transitivity", None),
];
/// Runs `carcara check` on a pair; whether it answers `valid` or `holey`,
/// and what it printed.
fn carcara_accepts(problem: &Path) -> (bool, String) {
    let proof = proof_path(problem);
    let output = Process::new(tool("carcara")).args(["check", "--expand-let-bindings", "--ignore-unknown-rules"]).arg(&proof).arg(problem).output().expect("carcara runs");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let verdict = stdout.lines().last().unwrap_or_default().trim().to_string();
    let accepted = output.status.success() && (verdict == "valid" || verdict == "holey");
    (accepted, without_colours(&format!("{stdout}{}", String::from_utf8_lossy(&output.stderr))))
}

/// `text` without ANSI colour codes, which Carcara writes into its errors.
fn without_colours(text: &str) -> String {
    let mut out = String::new();
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c == '\u{1b}' {
            for d in chars.by_ref() {
                if d.is_ascii_alphabetic() {
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}

fn assert_version() {
    let version = Process::new(tool("carcara")).arg("--version").output().expect("carcara runs");
    let version = String::from_utf8_lossy(&version.stdout);
    assert!(version.contains("git 20bf49c"), "the expected outcomes are those of Carcara at commit 20bf49c5ce31089ac83118574c888669355aaae1, found: {}", version.trim());
}

fn first_line(output: &str) -> String {
    output.lines().map(str::trim).filter(|l| !l.is_empty()).collect::<Vec<_>>().join(" | ")
}

#[test]
#[ignore = "needs carcara (Carcara at git 20bf49c) in .tools/bin or on PATH; run with --include-ignored"]
fn carcara_accepts_the_printed_corpus_proofs() {
    assert_version();
    let dir = scratch("carcara-accepts");
    let mut seen = Vec::new();
    for stem in supported_stems() {
        let pairs = pairs(&stem).expect("the corpus entry");
        for (pair, name) in pairs.iter().zip(names(&stem, pairs.len())) {
            let problem = write(pair, &dir, &name);
            let proof = proof_path(&problem);
            let (accepted, output) = carcara_accepts(&problem);
            eprintln!("{name}: {}", if accepted { "accepted".to_string() } else { format!("refused: {}", first_line(&output)) });
            let expected = EXPECTED.iter().find(|(s, _)| *s == name).unwrap_or_else(|| panic!("{name}: no recorded outcome")).1;
            match expected {
                None => assert!(accepted, "{name}: carcara refuses the pair\n{output}"),
                Some(r) => {
                    assert!(!accepted, "{name}: carcara now accepts the pair; the refusal {r:?} is resolved, update EXPECTED");
                    assert!(r.explains(&output), "{name}: carcara refuses the pair for another reason than {r:?}\n{output}");
                    assert!(r.present(&std::fs::read_to_string(&proof).expect("proof")), "{name}: the pair has no construct of {r:?}");
                }
            }
            seen.push(name);
        }
    }
    let missing: Vec<&str> = EXPECTED.iter().map(|(s, _)| *s).filter(|s| !seen.iter().any(|n| n == s)).collect();
    assert!(missing.is_empty(), "recorded outcomes for pairs that no longer exist: {missing:?}");
}

const PREMISE: &str = "a premise that is the step itself";
const REPEATED: &str = "a repeated index";
const NOT_ASSERTED: &str = "an assumption that is not asserted";
const UNDECLARED: &str = "an undeclared symbol";

/// Carcara's error for the mutation's own reason.
fn own_reason(what: &str, output: &str) -> bool {
    match what {
        PREMISE => output.contains("error: step id '") && output.contains("' is not defined"),
        REPEATED => output.contains("error: step id '") && output.contains("' was repeated"),
        NOT_ASSERTED => output.contains("error: could not match term to any of the original problem premises: (and "),
        UNDECLARED => output.contains("error: identifier 'undeclared_symbol' is not defined"),
        _ => unreachable!(),
    }
}

/// `step` with `id`, `clause` and `premises` replaced, built again with
/// the constructors.
fn rebuilt(step: &Step, id: &smtlib::Symbol, clause: Vec<smtlib::Term>, premises: &[smtlib::Symbol]) -> Step {
    let mut out = Step::new(id.clone(), clause, step.rule().clone()).expect("a step");
    if let Some(p) = NonEmpty::new(premises.to_vec()) {
        out = out.with_premises(p).expect("premises");
    }
    if let Some(a) = NonEmpty::new(step.args().to_vec()) {
        out = out.with_args(a).expect("args");
    }
    if let Some(d) = NonEmpty::new(step.discharge().to_vec()) {
        out = out.with_discharge(d).expect("discharge");
    }
    step.attributes().iter().fold(out, |s, a| s.with_attribute(a.clone()).expect("attribute"))
}

fn replaced(commands: &[Command], i: usize, command: Command) -> Proof {
    let mut c = commands.to_vec();
    c[i] = command;
    Proof::new(c)
}

fn mutations(pair: &Pair) -> Vec<(&'static str, Proof)> {
    let commands = pair.proof.commands();
    let mut out = Vec::new();
    if let Some((i, s)) = commands.iter().enumerate().find_map(|(i, c)| match c {
        Command::Step(s) if !s.premises().is_empty() => Some((i, s)),
        _ => None,
    }) {
        let mut premises = s.premises().to_vec();
        premises[0] = s.id().clone();
        out.push((PREMISE, replaced(commands, i, Command::Step(rebuilt(s, s.id(), s.clause().to_vec(), &premises)))));
    }
    if let (Some(first), Some((i, s))) = (commands[0].id(), commands.iter().enumerate().rev().find_map(|(i, c)| if let Command::Step(s) = c { Some((i, s)) } else { None })) {
        out.push((REPEATED, replaced(commands, i, Command::Step(rebuilt(s, first, s.clause().to_vec(), s.premises())))));
    }
    if let Some((i, a)) = commands.iter().enumerate().find_map(|(i, c)| if let Command::Assume(a) = c { Some((i, a)) } else { None }) {
        let term = alethe::term::parse(&format!("(and {} false)", alethe::term::to_text(a.term()))).expect("a term");
        let assume = a.attributes().iter().fold(Assume::new(a.id().clone(), term).expect("an assume"), |x, at| x.with_attribute(at.clone()).expect("attribute"));
        out.push((NOT_ASSERTED, replaced(commands, i, Command::Assume(assume))));
    }
    if let Some((i, s)) = commands.iter().enumerate().find_map(|(i, c)| match c {
        Command::Step(s) if !s.clause().is_empty() => Some((i, s)),
        _ => None,
    }) {
        let mut clause = s.clause().to_vec();
        clause[0] = alethe::term::parse("undeclared_symbol").expect("a term");
        out.push((UNDECLARED, replaced(commands, i, Command::Step(rebuilt(s, s.id(), clause, s.premises())))));
    }
    out
}

#[test]
#[ignore = "needs carcara (Carcara at git 20bf49c) in .tools/bin or on PATH; run with --include-ignored"]
fn carcara_refuses_mutations_of_the_corpus_proofs() {
    assert_version();
    let dir = scratch("carcara-refuses");
    let mut own = std::collections::HashMap::new();
    for stem in supported_stems() {
        for (k, pair) in pairs(&stem).expect("the corpus entry").into_iter().enumerate() {
            for (j, (what, proof)) in mutations(&pair).into_iter().enumerate() {
                assert_eq!(Proof::parse(&proof.to_text()).as_ref(), Ok(&proof), "{what}: the mutation is well-formed text");
                let mutated = Pair { problem: pair.problem.clone(), proof };
                let name = format!("{stem}-{k}-{j}");
                let problem = write(&mutated, &dir, &name);
                let (accepted, output) = carcara_accepts(&problem);
                assert!(!accepted, "{name}: {what}: carcara accepts the mutation\n{output}");
                let reason = if own_reason(what, &output) {
                    *own.entry(what).or_insert(0) += 1;
                    "its own reason".to_string()
                } else if let Some(r) = Refusal::ALL.into_iter().find(|r| r.explains(&output)) {
                    format!("the recorded refusal {r:?}")
                } else {
                    panic!("{name}: {what}: carcara refuses for an unrecorded reason\n{output}")
                };
                eprintln!("{name} ({what}): refused for {reason}: {}", first_line(&output));
            }
        }
    }
    for what in [PREMISE, REPEATED, NOT_ASSERTED, UNDECLARED] {
        assert!(own.get(what).copied().unwrap_or(0) > 0, "no mutation \"{what}\" is refused by carcara for its own reason");
    }
}

/// §4.1 writes the bit-vector constant bvⁱₙ as `(_ @bvn i)` ("We write
/// (_ @bv𝑛 𝑖 ) for bv𝑖𝑛"); this crate writes that form
/// ([`alethe::term::bv_constant`]) and reads it like any indexed
/// identifier. Carcara reads `(@bv i n)`, an application with the value
/// first (`src/ast/term.rs`, `BvConst: "@bv"`), and refuses `(_ @bv2 3)`:
/// its indexed operators of the `bv` kind are `(_ bvX n)` only
/// (`src/parser/mod.rs`, `parse_indexed_operator`, `strip_prefix("bv")`;
/// otherwise `InvalidIndexedOp`, "not a valid indexed operator"). A
/// recorded disagreement; the specification's form is the one this crate
/// writes.
#[test]
#[ignore = "needs carcara (Carcara at git 20bf49c) in .tools/bin or on PATH; run with --include-ignored"]
fn the_bit_vector_constant_of_section_4_1() {
    assert_version();
    let dir = scratch("carcara-bv-constant");
    let problem = smtlib::command::Script::parse("(set-logic QF_BV)(declare-const x (_ BitVec 2))(assert (= x #b11))(check-sat)").expect("problem");
    let numeral = |s: &str| smtlib::lexicon::Numeral::new(s).expect("a numeral");
    let section = alethe::term::to_text(&alethe::term::bv_constant(&numeral("2"), &numeral("3")));
    assert_eq!(section, "(_ @bv2 3)");
    let run = |name: &str, constant: &str| {
        let text = format!("(assume a0 (= x #b11))\n(step t1 (cl (= x {constant})) :rule hole)\n(step t2 (cl) :rule hole :premises (a0 t1))");
        let pair = Pair { problem: problem.clone(), proof: Proof::parse(&text).expect("this crate reads both forms") };
        carcara_accepts(&write(&pair, &dir, name))
    };
    let (accepted, output) = run("section", &section);
    assert!(!accepted && output.contains("error: not a valid indexed operator: '@bv2'"), "carcara now reads (_ @bv2 3); update this record\n{output}");
    let (accepted, output) = run("carcara", "(@bv 3 2)");
    assert!(accepted, "carcara no longer reads (@bv 3 2); update this record\n{output}");
}
