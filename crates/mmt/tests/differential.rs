//! Differential tests against MMT v27.0.0 itself (`.tools/mmt.jar`, run with
//! `.tools/bin/java`, over urtheories at commit
//! 8bc91e38df43decdd55b1eda471c4d7b9c75dfdd in `.tools/urtheories`; the JVM is
//! used only here, never by the crate). Each case is an archive with one
//! source file over MMT/urtheories; MMT builds it and this crate reads it.
//!
//! What the verdicts cover: MMT's `build ID mmt-omdoc` reads every
//! declaration and type-checks it, and its verdict is "no error"; this
//! crate's verdict is that the archive reads (structure, URIs, notations,
//! literals, elaboration) without error. MMT has no build target that only
//! reads, so the verdicts agree on what reading decides and diverge where
//! only type checking rejects; every case states both expected verdicts, and
//! each divergence says why. The cases where reading itself decides
//! (unbound tokens, metadata keys, scopes of nested theories, unsupported
//! lexers) agree with MMT.
//! Run with `--ignored --nocapture` to see the table.

mod common;

use std::path::{Path, PathBuf};
use std::process::Command;

use common::*;
use mmt::{Archive, Library};

const LF: &str = "http://cds.omdoc.org/urtheories?LF";

/// A case: its name, the verdict expected of this crate (reading), the verdict expected of MMT (reading and type checking), and the source.
type Case = (&'static str, bool, bool, String);

fn cases() -> Vec<Case> {
    let thy = |body: &str| format!("namespace http://test.org/d❚\nimport rules scala://mmt.kwarc.info❚\ntheory T : {LF} =\n  i : type❙ o : type❙ a : i❙ b : i❙ c : i❙ p : o❙\n{body}\n❚\n");
    let realize = "  str : type❙ int : type❙ concat : str ⟶ str ⟶ str❙
  rule rules/lf?Realize str rules/api/uom?StandardString❙
  rule rules/lf?Realize concat rules/api/uom?StringOperations/Concat❙
  rule rules/literals?StandardStringInterpolation str concat❙
  rule rules/lf?Realize int rules/api/uom?StandardInt❙";
    let fixture = std::fs::read_to_string(crate_dir().join("tests/data/specification/source/specification.mmt")).unwrap();
    let (head, rest) = fixture.split_once(" : prop ❘ = ").unwrap();
    let ill_fixture = format!("{head} : prop ❘ = (Act 5)❙{}", rest.split_once('❙').unwrap().1);
    let same = |name: &'static str, accept: bool, src: String| (name, accept, accept, src);
    // read by this crate, rejected by MMT's type checker
    let typing = |name: &'static str, src: String| (name, true, false, src);
    vec![
        same("constants, functions, definitions", true, thy("  f : i ⟶ o❙ d : o ❘ = f a❙ k = f b❙")),
        typing("definiens of the wrong type (typing)", thy("  g : i ⟶ i ❘ = a❙")),
        same("unbound token", false, thy("  d : i ❘ = foo❙")),
        typing("free variable (typing: no free variables in a constant)", thy("  d : i ❘ = X❙")),
        same("Pi and lambda", true, thy("  P : i ⟶ type❙ id : i ⟶ i ❘ = [x] x❙ dp : {x:i} P x ⟶ P x ❘ = [x][q] q❙")),
        typing("lambda of the wrong type (typing)", thy("  P : i ⟶ type❙ dp : {x:i} P x ⟶ P x ❘ = [x][q] x❙")),
        typing("polymorphism is not LF (typing)", thy("  id : {A:type} A ⟶ A ❘ = [A][x] x❙")),
        same("beta and eta", true, thy("  P : i ⟶ type❙ F : (i ⟶ i) ⟶ type❙ f : i ⟶ i❙ q : P a❙ q2 : P (([x:i] x) a) ❘ = q❙ r : F f❙ r2 : F ([x] f x) ❘ = r❙")),
        typing("Pi over a kind (typing)", thy("  Q : type ⟶ type❙")),
        same("type attribution", true, thy("  d : i ❘ = (a : i)❙")),
        typing("wrong type attribution (typing)", thy("  d : i ❘ = (a : o)❙")),
        same("precedence (declarations.md)", true, thy("  times : i ⟶ i ⟶ i ❘ # 1 ⋅ 2 prec 15❙ plus : i ⟶ i ⟶ o ❘ # 1 + 2 prec 10❙ d : o ❘ = a + b ⋅ c❙")),
        typing("precedence swapped (typing of the other reading)", thy("  times : i ⟶ i ⟶ i ❘ # 1 ⋅ 2 prec 10❙ plus : i ⟶ i ⟶ o ❘ # 1 + 2 prec 15❙ d : o ❘ = a + b ⋅ c❙")),
        same("right associativity %R (declarations.md)", true, thy("  imp : i ⟶ o ⟶ o ❘ # 1 %R⇒ 2❙ d : o ❘ = a ⇒ b ⇒ p❙")),
        typing("left associativity (typing of the other reading)", thy("  imp : i ⟶ o ⟶ o ❘ # 1 ⇒ 2❙ d : o ❘ = a ⇒ b ⇒ p❙")),
        same("implicit marker %I (declarations.md)", true, thy("  ded : o ⟶ type ❘ # ⊦ 1 prec 0❙ false : o❙ falsE : ⊦ false ⟶ {A:o}⊦ A ❘ # falsE 1 %I2❙ ex : {B : o} ⊦ false ⟶ ⊦ B ❘ = [B][q] falsE q❙")),
        typing("implicit marker excludes an explicit argument (typing)", thy("  ded : o ⟶ type ❘ # ⊦ 1 prec 0❙ false : o❙ falsE : ⊦ false ⟶ {A:o}⊦ A ❘ # falsE 1 %I2❙ ex : {B : o} ⊦ false ⟶ ⊦ B ❘ = [B][q] falsE q B❙")),
        same("omitted argument (declarations.md)", true, thy("  F : i ⟶ type❙ C : {x:i} F x ⟶ o ❘ # C 2❙ y : F a❙ d : o ❘ = C y❙")),
        typing("implicit argument that cannot be inferred (typing)", thy("  g : {x:i} o ❘ # g❙ d : o ❘ = g❙")),
        same("literals", true, thy(&format!("{realize}\n  s : str ❘ = \"abc\"❙ n : int ❘ = 42❙ t : str ❘ = s\"a${{s}}b\"❙"))),
        typing("literal of the wrong type (typing)", thy(&format!("{realize}\n  n : int ❘ = \"abc\"❙"))),
        same("nested theories (modules.md)", true, format!("namespace http://test.org/d❚\ntheory O : {LF} =\n  i : type❙ a : i❙\n  theory I : {LF} =\n    b : i ❘ = a❙\n  ❚\n  e : i ❘ = a❙\n❚\n")),
        same("outer theory does not see the inner one", false, format!("namespace http://test.org/d❚\ntheory O : {LF} =\n  i : type❙ a : i❙\n  theory I : {LF} =\n    b : i ❘ = a❙\n  ❚\n  e : i ❘ = b❙\n❚\n")),
        same("metadata as in declarations.md", false, thy("  myKey❙ myValue❙ d : i ❘ meta ?myKey ?myValue❙")),
        same("metadata with symbol keys", true, thy("  myKey❙ myValue❙ d : i ❘ meta ?T?myKey ?T?myValue❙")),
        ("rule that does not exist (MMT loads the class of a rule; reading does not)", true, false, thy("  rule rules/lf?NoSuchRule❙")),
        same("rule without effect on reading", true, thy("  rule rules/lf?ShallowPolymorphism❙")),
        same("lexer extension outside the subset", false, format!("namespace http://test.org/d❚\nimport rules scala://mmt.kwarc.info❚\ntheory T : {LF} =\n  rule rules/quotation?TermLiteralRule❙\n  d : type ❘ = `type`❙\n❚\n")),
        same("the MMT form of trion's specification", true, fixture),
        typing("the MMT form with (Act 5) (typing)", ill_fixture),
    ]
}

fn mmt_accepts(archive: &Path) -> (bool, String) {
    let tools = tools();
    let commands = format!("mathpath archive {} ; mathpath archive {} ; build test/t mmt-omdoc", tools.join("urtheories").display(), archive.display());
    let output = Command::new(tools.join("bin/java")).arg("-jar").arg(tools.join("mmt.jar")).arg("--noshell").arg(commands).current_dir(archive).output().expect("needs .tools/bin/java and .tools/mmt.jar (MMT v27.0.0)");
    let text = format!("{}{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
    let mut plain = String::new();
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c == '\u{1b}' {
            for c in chars.by_ref() {
                if c == 'm' {
                    break;
                }
            }
        } else {
            plain.push(c);
        }
    }
    let errors: Vec<&str> = plain.lines().filter(|l| l.contains("error")).collect();
    (plain.contains("'build test/t mmt-omdoc' finished") && errors.is_empty(), errors.join("\n"))
}

fn ours_accepts(base: &Library, archive: &Path) -> (bool, String) {
    let mut lib = base.clone();
    let a = Archive::open(archive).unwrap();
    let load = lib.load_archives(std::slice::from_ref(&a));
    (load.errors().is_empty(), show(load.errors()))
}

fn archive(dir: &Path, source: &str) -> PathBuf {
    let _ = std::fs::remove_dir_all(dir);
    std::fs::create_dir_all(dir.join("META-INF")).unwrap();
    std::fs::create_dir_all(dir.join("source")).unwrap();
    std::fs::write(dir.join("META-INF/MANIFEST.MF"), "id: test/t\nsource-base: http://test.org/t\nnarration-base: http://test.org/t\ndependencies: MMT/urtheories\n").unwrap();
    std::fs::write(dir.join("source/test.mmt"), source).unwrap();
    dir.to_path_buf()
}

#[test]
#[ignore = "needs .tools/bin/java, .tools/mmt.jar (MMT v27.0.0) and urtheories (commit 8bc91e38df43decdd55b1eda471c4d7b9c75dfdd) in .tools/urtheories"]
fn verdicts_agree_with_mmt() {
    let (base, _) = urtheories();
    let root = std::env::temp_dir().join(format!("mmt-differential-{}", std::process::id()));
    let cases = cases();
    let handles: Vec<_> = cases
        .iter()
        .enumerate()
        .map(|(k, (_, _, _, src))| {
            let dir = archive(&root.join(k.to_string()), src);
            std::thread::spawn(move || mmt_accepts(&dir))
        })
        .collect();
    let mut disagreements = Vec::new();
    println!("{:<50} {:>8} {:>8}", "case", "MMT", "mmt-rs");
    for ((k, (name, expected_ours, expected_theirs, _)), h) in cases.iter().enumerate().zip(handles) {
        let (theirs, their_errors) = h.join().unwrap();
        let (ours, our_errors) = ours_accepts(&base, &root.join(k.to_string()));
        let v = |b: bool| if b { "accept" } else { "reject" };
        println!("{name:<50} {:>8} {:>8}", v(theirs), v(ours));
        if theirs != *expected_theirs || ours != *expected_ours {
            disagreements.push(format!("{name}: MMT {}, this crate {}\n  MMT: {their_errors}\n  ours: {our_errors}", v(theirs), v(ours)));
        }
    }
    let _ = std::fs::remove_dir_all(&root);
    assert!(disagreements.is_empty(), "{}", disagreements.join("\n"));
}
