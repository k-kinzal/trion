//! What is written about a package: the MMT form, with the contracts and
//! the proof obligations, and the documents that `trion` writes in the
//! formats that `--format` names; and the results that `trioc prove` proves
//! from the MMT form.

mod common;
use common::*;

const CONSISTENT: &str = "primitive API, message\n[STORE] The API shall store the message.\n    unsourced \"an example\"\n[LOG] The API shall not log the message.\n    unsourced \"an example\"\n";
const CONTRADICTORY: &str = "primitive API, message\n[STORE] The API shall store the message.\n[NEVER] The API shall not store the message.\n";

fn package(statements: &str) -> Fixture {
    Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", statements)])
}

#[test]
fn the_markdown_document_states_each_statement_with_its_contract() {
    let f = package(&format!("section \"Storage\"\n{CONSISTENT}"));
    let run = f.convert(&["--out", "out", "--format", "markdown"]);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let document = f.read("out/specification.md");
    assert!(document.starts_with("# p\n\nConverted; nothing here is proved. The proof obligations hold within traces of 3 moments"), "{document}");
    assert!(document.contains("\n## a.trion\n") && document.contains("\n### Storage\n"), "{document}");
    assert!(document.contains("- **[STORE]** The API shall store the message.\n\n  ```text\n  A = ⊤\n  G = Act(API|store message) ∧ ¬Forbid(API|store message) ∧ ¬Discouraged(API|store message)\n  time: "), "{document}");
    assert!(document.contains("- **[LOG]** The API shall not log the message.\n\n  ```text\n  A = ⊤\n  G = ¬Act(API|log message) ∧ Forbid(API|log message)\n  time: "), "{document}");
    // A contract has its time: when it applies and when its response comes.
    assert!(document.contains("  time: action API|store message: start(API|store message) then complete(API|store message); eventually complete(API|store message)\n"), "{document}");
    assert!(document.contains("\n## Proof obligations\n\n- `consistency` (consistency): within traces of 3 moments, domains of one individual of each type: "), "{document}");
}

#[test]
fn a_description_of_the_environment_is_an_assumption() {
    // By responsibility: what the user does is the environment's, and what the API does is the system's.
    let f = package("system API\nenvironment user\nprimitive API, message, user, door\n[U] The user sends a message.\n[D] The API is ready.\n[S] The API shall store the message.\n");
    let run = f.convert(&["--out", "out", "--format", "markdown", "--json"]);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let report = run.json();
    let role = |id: &str| report["contracts"].as_array().unwrap().iter().find(|c| c["statement"]["id"] == id).map(|c| c["role"].as_str().unwrap().to_string());
    assert_eq!((role("U").as_deref(), role("D").as_deref(), role("S").as_deref()), (Some("assumption"), Some("guarantee"), Some("guarantee")), "{report}");
    // An assumption sentence assumes its fact and guarantees nothing.
    let document = f.read("out/specification.md");
    assert!(document.contains("- **[U]** The user sends a message.\n\n  ```text\n  A = "), "{document}");
    let block = document.split("**[U]**").nth(1).unwrap().split("```").nth(1).unwrap();
    assert!(block.contains("\n  G = ⊤\n"), "{block}");
    // Its scope is the whole document: it is distributed to every guarantee.
    assert!(block.trim_end().ends_with("distributed to every guarantee of the document"), "{block}");
}

#[test]
fn each_format_that_is_named_is_written_and_no_other() {
    let f = package(CONSISTENT);
    // Without a format, the MMT form is written.
    assert_eq!(f.convert(&["--out", "out"]).code, 0);
    assert!(f.path().join("out/source/specification.mmt").exists());
    assert!(!f.path().join("out/specification.md").exists() && !f.path().join("out/specification.html").exists());
    assert_eq!(f.convert(&["--out", "both", "--format", "markdown", "--format", "html"]).code, 0);
    assert!(f.path().join("both/specification.md").exists() && f.path().join("both/specification.html").exists() && !f.path().join("both/source/specification.mmt").exists());
}

#[test]
fn a_contradiction_is_converted_and_refuted_by_the_proof() {
    // The conversion proves nothing, and a document does not wait for a proof.
    let f = package(CONTRADICTORY);
    let run = f.convert(&["--out", "out", "--format", "mmt", "--format", "markdown"]);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    assert!(!run.stdout.contains("contradiction"), "{}", run.stdout);
    assert!(f.path().join("out/source/specification.mmt").exists() && f.path().join("out/specification.md").exists());
    // The proof refutes the consistency within its bound, and issues no certificate of it.
    let proved = f.prove(&["out", "--json", "--certificates", "certs"]);
    assert_eq!(proved.code, 1, "{}{}", proved.stdout, proved.stderr);
    let report = proved.json();
    let consistency = report["results"].as_array().unwrap().iter().find(|r| r["obligation"] == "consistency").unwrap();
    assert_eq!(consistency["verdict"], "refuted", "{report}");
    assert!(consistency["proposition"].as_str().unwrap().starts_with("within traces of 3 moments, domains of one individual of each type: "), "{report}");
    assert!(!f.path().join("certs/consistency.smt2").exists());
}

#[test]
fn each_obligation_of_the_mmt_form_has_one_result() {
    let f = package(CONSISTENT);
    assert_eq!(f.convert(&["--out", "out", "--format", "mmt"]).code, 0);
    let stated = f.convert(&["--json"]).json();
    let proved = f.prove(&["out", "--json", "--certificates", "certs", "--format", "smt2,alethe,cpc,moxi"]).json();
    let names = |value: &serde_json::Value, list: &str, key: &str| value[list].as_array().unwrap().iter().map(|o| o[key].as_str().unwrap().to_string()).collect::<Vec<_>>();
    assert_eq!(names(&stated, "obligations", "name"), names(&proved, "results", "obligation"), "{proved}");
    assert!(proved["results"].as_array().unwrap().iter().all(|r| r["verdict"] == "proved" && r["certificates"] == serde_json::json!(["smt2", "alethe", "cpc", "moxi"])), "{proved}");
    // A proved obligation has its certificate in each format that can state it.
    let script = f.read("certs/consistency.smt2");
    assert!(script.starts_with("; the expected answers, in order: unsat unsat\n") && script.contains("(check-sat)"), "{script}");
    // A satisfiable question is shown by its witness: the values asserted
    // with the negation of the formulas, which is expected unsat.
    let script = f.read("certs/compatibility.smt2");
    assert!(script.starts_with("; the expected answers, in order: sat unsat\n") && script.contains("; the witness of question 1: expected unsat\n"), "{script}");
    // MoXI states each question as a system without time and a
    // reachability query, with the answer that it is expected to have.
    let moxi = f.read("certs/consistency.moxi");
    assert!(moxi.contains("\n(set-logic QF_LIA)\n") && moxi.contains("(define-system question1") && moxi.contains("(check-system question1") && moxi.contains(":query (asked (holds))"), "{moxi}");
    // Alethe and CPC hold one problem and one proof for each question; a
    // satisfiable question is proved by the refutation of its witness check.
    for stem in ["consistency-q1", "consistency-q2", "compatibility-q1-witness"] {
        assert!(f.path().join(format!("certs/alethe/{stem}.smt2")).is_file() && f.path().join(format!("certs/alethe/{stem}.smt2.alethe")).is_file(), "{stem}");
        assert!(f.path().join(format!("certs/cpc/{stem}.smt2")).is_file() && f.path().join(format!("certs/cpc/{stem}.cpc")).is_file(), "{stem}");
    }
    assert!(proved["notes"].as_array().unwrap().is_empty(), "{proved}");
    // The CPC documents include the signature of cvc5 1.4.2 from
    // `cpc/signature/`, which trioc does not hold and does not write: the
    // result says what whoever checks them places there.
    assert!(!f.path().join("certs/cpc/signature").exists());
    assert_eq!(proved["certification"]["cpc_signature"], "proofs/eo/cpc of the sources of cvc5 1.4.2", "{proved}");
    let document = f.read("certs/cpc/consistency-q1.cpc");
    assert!(document.contains("(include \"signature/Cpc.eo\")"), "{document}");
}

#[test]
fn trioc_runs_no_other_program() {
    // With nothing on the search path, every format is written all the same:
    // the proofs are trioc's own, and the checkers below read them later.
    let f = package(CONSISTENT);
    assert_eq!(f.convert(&["--out", "out", "--format", "mmt"]).code, 0);
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_trioc")).env_clear().env("PATH", "").args(["prove", "out", "--certificates", "certs", "--format", "smt2,alethe,cpc,moxi"]).current_dir(f.path()).output().unwrap();
    let printed = String::from_utf8_lossy(&output.stdout);
    assert_eq!(output.status.code(), Some(0), "{printed}");
    assert!(printed.contains("certificates: the CPC documents include proofs/eo/cpc of the sources of cvc5 1.4.2 from cpc/signature/, which is not written"), "{printed}");
    assert!(!printed.contains("[certificate-"), "{printed}");
}

#[test]
fn a_package_that_does_not_conform_is_not_converted() {
    let f = package("primitive API\n[G] The API shall be secure.\n");
    let run = f.convert(&["--out", "out"]);
    assert_eq!(run.code, 1, "{}", run.stdout);
    assert!(run.stdout.contains("error[inexpressible-property]") && run.stdout.trim_end().ends_with("does not conform"), "{}", run.stdout);
    assert!(run.stderr.contains("nothing is written"), "{}", run.stderr);
    assert!(!f.path().join("out/source/specification.mmt").exists());
}

#[test]
fn a_form_that_is_not_one_is_refused() {
    let f = package(CONSISTENT);
    f.write("out/source/specification.mmt", "namespace http://elsewhere❚\ntheory p =\n❚\n");
    let run = f.prove(&["out"]);
    assert_eq!(run.code, 2, "{}", run.stdout);
    assert!(run.stderr.contains("no MMT form of trion"), "{}", run.stderr);
}

#[test]
fn a_format_without_a_directory_is_refused() {
    let run = package(CONSISTENT).convert(&["--format", "markdown"]);
    assert_eq!(run.code, 2, "{}", run.stdout);
    assert!(run.stderr.contains("--out"), "{}", run.stderr);
}

/// The blocks of `AGENTS.md` under "Principles of the Language", in their
/// order: the label of each (`Controlled Natural Language`, `A/G Contracts`,
/// `Proof Certificate`) with its text.
fn blocks_of_the_principles() -> Vec<(String, String)> {
    let text = std::fs::read_to_string(repo_root().join("AGENTS.md")).unwrap();
    let section = text.split("## Principles of the Language").nth(1).expect("the principles of the language");
    let mut blocks = Vec::new();
    let mut lines = section.lines();
    while let Some(line) = lines.next() {
        let Some(label) = line.strip_prefix("```text:") else { continue };
        let body: Vec<&str> = lines.by_ref().take_while(|line| *line != "```").collect();
        blocks.push((label.to_string(), body.join("\n")));
    }
    blocks
}

/// The blocks of a document that `trion` wrote: each fenced text, without
/// the indentation of the statement that it stands under.
fn blocks_of(document: &str) -> Vec<String> {
    let mut blocks = Vec::new();
    let mut lines = document.lines();
    while let Some(line) = lines.next() {
        if line.trim() != "```text" {
            continue;
        }
        let indent = line.len() - line.trim_start().len();
        let body: Vec<&str> = lines.by_ref().take_while(|line| line.trim() != "```").map(|line| line.get(indent..).unwrap_or("")).collect();
        blocks.push(body.join("\n"));
    }
    blocks
}

#[test]
fn the_examples_of_the_principles_are_what_the_command_writes() {
    // `AGENTS.md` states each principle with an example: a sentence, the
    // contracts that it is read as, and for the first the bounded proof
    // obligation. The document that the command writes for the sentence holds
    // the same contracts and the same formulas, letter for letter.
    let blocks = blocks_of_the_principles();
    let sentences: Vec<usize> = blocks.iter().enumerate().filter(|(_, (label, _))| label == "Controlled Natural Language").map(|(at, _)| at).collect();
    assert_eq!(sentences.len(), 2, "{blocks:?}");
    let mut certificates = 0;
    for (number, at) in sentences.iter().enumerate() {
        let example = &blocks[*at..sentences.get(number + 1).copied().unwrap_or(blocks.len())];
        let sentence = &example[0].1;
        let f = package(&format!("primitive API, message\n{sentence}\n"));
        let run = f.convert(&["--out", "out", "--format", "markdown"]);
        assert_eq!(run.code, 0, "{sentence}: {}{}", run.stdout, run.stderr);
        let written = blocks_of(&f.read("out/specification.md"));
        for (label, expected) in &example[1..] {
            match label.as_str() {
                // The contract in the notation of the principles: its
                // assumption and its guarantee. Its time follows them in the
                // document, and the bounded obligation states it over moments.
                "A/G Contracts" => {
                    let contracts: Vec<&str> = written[0].lines().filter(|line| line.is_empty() || line.starts_with("A = ") || line.starts_with("G = ")).collect();
                    assert_eq!(&contracts.join("\n"), expected, "the contracts of `{sentence}`");
                    assert!(written[0].lines().any(|line| line.starts_with("time: ")), "{}", written[0]);
                }
                "Bounded Proof Obligation" => {
                    certificates += 1;
                    assert_eq!(written.last().unwrap(), expected, "the certificate of `{sentence}`");
                }
                other => panic!("the principles hold a block that no test reads: {other}"),
            }
        }
    }
    assert_eq!(certificates, 1);
}

/// Places the CPC signature that the documents in `cpc` include, as whoever
/// checks them does: `proofs/eo/cpc` of cvc5 1.4.2, from
/// `.tools/cvc5-signature`, at `cpc/signature`.
fn place_cpc_signature(cpc: &std::path::Path) {
    let dir = repo_root().join(".tools/cvc5-signature");
    assert!(dir.join("Cpc.eo").is_file(), "this test needs proofs/eo/cpc of cvc5 1.4.2 in .tools/cvc5-signature");
    let link = cpc.join("signature");
    if !link.exists() {
        std::os::unix::fs::symlink(&dir, &link).unwrap();
    }
}

/// A tool of the tests, in `.tools/bin` or on the search path. A test that
/// needs a missing tool fails with what it needs: it never passes without
/// the check.
fn tool(name: &str) -> std::path::PathBuf {
    std::env::split_paths(&tools_path()).map(|dir| dir.join(name)).find(|path| path.is_file()).unwrap_or_else(|| panic!("this test needs `{name}` in .tools/bin or on PATH"))
}

/// What a tool prints on its standard output and its standard error.
fn run_tool(name: &str, args: &[&std::ffi::OsStr], dir: &std::path::Path) -> String {
    let output = std::process::Command::new(tool(name)).args(args).current_dir(dir).output().unwrap_or_else(|e| panic!("{name} does not run: {e}"));
    format!("{}{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr))
}

/// Checks an SMT-LIB file that trioc wrote: cvc5 with `--strict-parsing`
/// and z3 each read it, which checks that it is well sorted in its logic,
/// and give every `check-sat` the expected answer, read as the responses to
/// the script's commands (the `smtlib` crate reads the script and the
/// responses as syntax only).
fn check_smt2(path: &std::path::Path, expected: &[&str]) {
    use trion_verification::proof::smtlib::{Dialect, GeneralResponse, Script};
    let text = std::fs::read_to_string(path).unwrap();
    let script = Script::parse(&text).unwrap_or_else(|e| panic!("{}: not SMT-LIB 2.7 syntax: {e}\n{text}", path.display()));
    let dir = path.parent().unwrap();
    for (solver, flags) in [("cvc5", &["--strict-parsing", "--incremental", "--lang=smt2"][..]), ("z3", &[][..])] {
        let mut args: Vec<&std::ffi::OsStr> = flags.iter().map(std::ffi::OsStr::new).collect();
        args.push(path.as_os_str());
        let printed = run_tool(solver, &args, dir);
        let answers = GeneralResponse::parse_session(&printed, script.commands(), false, &Dialect::strict()).unwrap_or_else(|e| panic!("{solver} on {}: {e}\n{printed}", path.display()));
        let answers: Vec<String> = answers.iter().map(ToString::to_string).collect();
        assert_eq!(answers, expected, "{solver} on {}\n{text}", path.display());
    }
}

/// The expected answers that the header of an SMT-LIB certificate states.
fn expected_answers(text: &str) -> Vec<&str> {
    text.lines().find_map(|line| line.strip_prefix("; the expected answers, in order: ")).expect("the expected answers").split_whitespace().collect()
}

/// Runs the sort checker of moxi-mc-flow, the reference tool of MoXI, on a
/// file: the same two steps that its `sortcheck.py` takes for a `.moxi`
/// file (`src.parse_moxi.parse`, then `src.moxi.sort_check`), as the
/// differential tests of the `moxi` crate drive it (`crates/moxi/tests/common`).
fn sortcheck(path: &std::path::Path) -> (bool, String) {
    let mcflow = std::env::var_os("MOXI_MC_FLOW").map(std::path::PathBuf::from).unwrap_or_else(|| repo_root().join(".tools/moxi-mc-flow"));
    assert!(mcflow.join("sortcheck.py").is_file(), "this test needs moxi-mc-flow in .tools/moxi-mc-flow or at MOXI_MC_FLOW");
    let driver = "import sys, pathlib\nsys.path.insert(0, sys.argv[1])\nfrom src import parse_moxi, moxi\nprogram = parse_moxi.parse(pathlib.Path(sys.argv[2]))\nprint('ACCEPT' if program is not None and moxi.sort_check(program)[0] else 'REJECT')\n";
    let printed = run_tool("python3", &["-I".as_ref(), "-c".as_ref(), driver.as_ref(), mcflow.as_os_str(), path.as_os_str()], path.parent().unwrap());
    (printed.trim_end().ends_with("ACCEPT"), printed)
}

/// Checks a MoXI file that trioc wrote: the `moxi` crate reads it (its
/// grammar), the sort checker of moxi-mc-flow accepts it (its static
/// semantics), and each query is reachable exactly when its comment says
/// so. In a system whose `:init` is `true` and whose `:trans` keeps each
/// variable, the reachable states are all valuations, so a query is
/// reachable exactly when its condition is satisfiable: cvc5 and z3 decide
/// each condition.
fn check_moxi(path: &std::path::Path) {
    use trion_verification::proof::moxi;
    let text = std::fs::read_to_string(path).unwrap();
    let script: moxi::Script = text.parse().unwrap_or_else(|e| panic!("{}: the moxi crate cannot read it: {e}\n{text}", path.display()));
    let (accepted, printed) = sortcheck(path);
    assert!(accepted, "moxi-mc-flow refuses {}: {printed}\n{text}", path.display());
    let expected: Vec<&str> = text.lines().filter_map(|line| line.strip_prefix("; question ")).map(|rest| if rest.contains("expected reachable") { "sat" } else { "unsat" }).collect();
    let checks: Vec<&moxi::CheckSystem> = script.commands().iter().filter_map(|c| match c { moxi::Command::CheckSystem(check) => Some(&**check), _ => None }).collect();
    assert_eq!(checks.len(), expected.len(), "{text}");
    for (k, (check, answer)) in checks.iter().zip(&expected).enumerate() {
        let mut condition = String::from("(set-logic QF_LIA)\n");
        for variable in check.local().into_iter().flatten() {
            condition.push_str(&format!("(declare-const {} {})\n", variable.variable(), variable.sort()));
        }
        for formula in check.conditions() {
            condition.push_str(&format!("(assert {})\n", formula.formula()));
        }
        condition.push_str("(check-sat)\n");
        let file = path.with_extension(format!("query{}.smt2", k + 1));
        std::fs::write(&file, condition).unwrap();
        check_smt2(&file, &[answer]);
    }
}

/// Checks an Alethe pair that trioc wrote: the problem as an SMT-LIB file
/// that is unsatisfiable, and the proof found `valid` by Carcara, with no
/// warning and without `--ignore-unknown-rules`, so that a rule Carcara does
/// not know is an error rather than a hole. trioc checks no certificate;
/// this is where its proofs are checked by another prover.
fn check_alethe(problem: &std::path::Path) {
    check_smt2(problem, &["unsat"]);
    let proof = std::path::PathBuf::from(format!("{}.alethe", problem.display()));
    let printed = run_tool("carcara", &["check".as_ref(), proof.as_os_str(), problem.as_os_str()], problem.parent().unwrap());
    assert_eq!(printed.trim(), "valid", "Carcara on {}: {printed}", proof.display());
}

/// Checks a CPC document that trioc wrote: the problem it references as an
/// SMT-LIB file that is unsatisfiable, and the document accepted by Ethos
/// with the signature placed beside it, run from another directory so that
/// the document stands on its own.
fn check_cpc(document: &std::path::Path) {
    check_smt2(&document.with_extension("smt2"), &["unsat"]);
    place_cpc_signature(document.parent().unwrap());
    let printed = run_tool("ethos", &[document.as_os_str()], &repo_root());
    assert_eq!(printed.trim(), "correct", "Ethos on {}: {printed}", document.display());
}

/// The packages whose certificates are checked: the examples of this file,
/// one with quantities and an environment, and one whose obligations rest
/// on propositional refutations only.
fn certified_packages() -> Vec<String> {
    vec![
        CONSISTENT.to_string(),
        format!("primitive user, latency\nsystem API\nenvironment user\n{CONSISTENT}[SEND] The user sends the message.\n[FAST] When the user sends the message, the latency of the API shall be at most 20 ms within 3 seconds.\n"),
        // Two descriptions that contradict each other: the obligation is
        // proved by a refutation that needs no arithmetic.
        "primitive API, door\n[K1] The door is open.\n[K2] The door is never open.\n[A] The API shall stop.\n".to_string(),
    ]
}

#[test]
fn every_certificate_is_accepted_by_the_checkers_of_its_format() {
    let mut pairs = 0;
    for statements in certified_packages() {
        let f = package(&statements);
        assert_eq!(f.convert(&["--out", "out", "--format", "mmt"]).code, 0, "{statements}");
        let proved = f.prove(&["out", "--json", "--certificates", "certs", "--format", "smt2,alethe,cpc,moxi"]);
        let report = proved.json();
        // The contradiction of the descriptions refutes the compatibility,
        // which has no certificate; the consistency is proved by it.
        assert!(report["results"].as_array().unwrap().iter().any(|r| r["verdict"] == "proved"), "{report}");
        // Every certificate of a proved obligation is written, and the
        // checkers below accept each.
        assert!(report["notes"].as_array().unwrap().is_empty(), "{report}");
        let certs = f.path().join("certs");
        let files = |dir: &std::path::Path, extension: &str| -> Vec<std::path::PathBuf> {
            let mut out: Vec<_> = std::fs::read_dir(dir).map(|d| d.filter_map(std::result::Result::ok).map(|e| e.path()).filter(|p| p.extension().is_some_and(|e| e == extension)).collect()).unwrap_or_default();
            out.sort();
            out
        };
        let smt2 = files(&certs, "smt2");
        assert!(!smt2.is_empty(), "{report}");
        for path in smt2 {
            let text = std::fs::read_to_string(&path).unwrap();
            check_smt2(&path, &expected_answers(&text));
        }
        for path in files(&certs, "moxi") {
            check_moxi(&path);
        }
        for path in files(&certs.join("alethe"), "smt2") {
            check_alethe(&path);
            pairs += 1;
        }
        let documents = files(&certs.join("cpc"), "cpc");
        assert!(!documents.is_empty(), "{report}");
        for path in documents {
            check_cpc(&path);
        }
    }
    assert!(pairs > 0, "no Alethe pair was written, so Carcara checked nothing");
}

#[test]
fn a_cpc_document_is_bound_to_its_problem() {
    // The document references its problem: Ethos checks that each
    // assumption of the proof is an assertion of the problem, so the proof
    // proves that problem and no other.
    let f = package(CONSISTENT);
    assert_eq!(f.convert(&["--out", "out", "--format", "mmt"]).code, 0);
    assert_eq!(f.prove(&["out", "--certificates", "certs", "--format", "cpc"]).code, 0);
    let document = f.path().join("certs/cpc/compatibility-q1-witness.cpc");
    check_cpc(&document);
    // The problem with one value of the witness changed: `(= x v)` becomes
    // `(= x v+1)`.
    use trion_verification::proof::smtlib::command::{Command, Script};
    use trion_verification::proof::smtlib::{lexicon::SpecConstant, NonEmpty, Term};
    let problem = f.read("certs/cpc/compatibility-q1-witness.smt2");
    let script = Script::parse(&problem).unwrap();
    let mut changed_one = false;
    let commands: Vec<Command> = script
        .into_commands()
        .into_iter()
        .map(|c| {
            let Command::Assert(Term::Application(f, args)) = &c else { return c };
            let (false, "=", [x, Term::Constant(SpecConstant::Numeral(n))]) = (changed_one, f.to_string().as_str(), &args[..]) else { return c };
            changed_one = true;
            let n = n.to_string().parse::<u64>().unwrap();
            Command::Assert(Term::Application(f.clone(), NonEmpty::new(vec![x.clone(), Term::parse(&(n + 1).to_string()).unwrap()]).unwrap()))
        })
        .collect();
    assert!(changed_one, "no value of a quantity in\n{problem}");
    let changed = Script::new(commands).to_string();
    assert_ne!(problem, changed, "{problem}");
    f.write("certs/cpc/compatibility-q1-witness.smt2", &changed);
    let printed = run_tool("ethos", &[document.as_os_str()], &repo_root());
    assert!(printed.contains("was not part of the referenced assertions"), "{printed}");
}
