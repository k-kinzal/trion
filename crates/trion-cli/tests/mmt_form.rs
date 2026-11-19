//! The MMT form of a package: `trion` builds it as MMT objects with the
//! `mmt` crate, reads the printed text back and writes it as an archive;
//! `trioc` reads it with the same crate, refuses what does not read or is
//! not a form with the position of the error, and proves the obligations
//! that it reads. Neither needs Java or the tools of `.tools` to do so, and
//! neither type-checks: the `mmt` crate models the grammar of MMT only.
//! MMT itself (`.tools/mmt.jar`, MMT v27.0.0 over `.tools/urtheories` at
//! commit 8bc91e38df43decdd55b1eda471c4d7b9c75dfdd) is the oracle for what
//! the form means to MMT: it reads and type-checks every form these tests
//! write, here and only here.

mod common;
use common::*;
use trioc_cli::mmt::Form;

const STATEMENTS: &str = "primitive user, latency\nsystem API\nenvironment user\nprimitive API, message\n[STORE] The API shall store the message.\n    unsourced \"an example\"\n[LOG] The API shall not log the message.\n    unsourced \"an example\"\n[SEND] The user sends the message.\n[FAST] When the user sends the message, the latency of the API shall be at most 20 ms within 3 seconds.\n";

fn package() -> Fixture {
    Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", STATEMENTS)])
}

/// The form with the definition of its first formula replaced.
fn with_first_formula(source: &str, definition: &str) -> String {
    let (head, rest) = source.split_once(" : prop ❘ = ").expect("a formula of the form");
    let rest = rest.split_once('❙').unwrap().1;
    format!("{head} : prop ❘ = {definition}❙{rest}")
}

/// `line:column` of an error of the `mmt` crate in a message.
fn has_position(message: &str) -> bool {
    message.split(": ").any(|part| part.split(':').count() == 2 && part.split(':').all(|n| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit())))
}

#[test]
fn trioc_reads_back_exactly_what_trion_wrote() {
    let f = package();
    let run = f.convert(&["--out", "out", "--json"]);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let report = run.json();
    assert_eq!(f.read("out/META-INF/MANIFEST.MF"), "id: trion/p\nsource-base: http://trion.dev/form/p\nnarration-base: http://trion.dev/form/p\ndependencies: MMT/urtheories\n");
    let text = f.read("out/source/specification.mmt");
    let form = Form::read(&text).unwrap_or_else(|e| panic!("{e}\n{text}"));
    // The obligations that trion states are the ones that are read, in order.
    let stated: Vec<(String, String, String, Vec<String>)> = report["obligations"].as_array().unwrap().iter().map(|o| (o["name"].as_str().unwrap().to_string(), o["property"].as_str().unwrap().to_string(), o["proposition"].as_str().unwrap().to_string(), o["statements"].as_array().unwrap().iter().map(|s| s.as_str().unwrap().to_string()).collect())).collect();
    let read: Vec<(String, String, String, Vec<String>)> = form.obligations.obligations.iter().map(|o| (o.name.clone(), o.property.clone(), o.proposition.clone(), o.statements.clone())).collect();
    assert!(!stated.is_empty());
    assert_eq!(stated, read);
    // So are the contracts, by responsibility, and the actors.
    let contracts: Vec<(String, String)> = report["contracts"].as_array().unwrap().iter().map(|c| (c["statement"]["id"].as_str().unwrap().to_string(), c["role"].as_str().unwrap().to_string())).collect();
    assert_eq!(contracts, form.contracts.iter().map(|c| (c.id.clone(), c.role.clone())).collect::<Vec<_>>());
    let actors = |side: &str| report["control"][side].as_array().unwrap().iter().map(|a| a.as_str().unwrap().to_string()).collect::<Vec<_>>();
    assert_eq!((actors("system"), actors("environment")), (form.system.clone(), form.environment.clone()));
    assert!(form.system.contains(&"API".to_string()) && form.environment.contains(&"user".to_string()), "{form:?}");
    // Form → text → Form: what is read is written as the same text and read as the same form.
    let written = form.write().unwrap();
    assert_eq!(written, text);
    assert_eq!(Form::read(&written).unwrap(), form);
    // trioc proves from the form, one result for each obligation.
    let proved = f.prove(&["out", "--json"]);
    assert_eq!(proved.code, 0, "{}{}", proved.stdout, proved.stderr);
    let results: Vec<String> = proved.json()["results"].as_array().unwrap().iter().map(|r| r["obligation"].as_str().unwrap().to_string()).collect();
    assert_eq!(results, stated.iter().map(|o| o.0.clone()).collect::<Vec<_>>());
}

#[test]
fn conditional_sentence_patterns_preserve_responsibility_in_the_exported_contract() {
    use trion_solver::{Atom, Formula};

    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "system API
environment user
primitive API, user
[PLAIN] The API shall stop.
[EXTERNAL] The API shall stop if the user arrives.
[INTERNAL] The API shall stop if the API starts.
[BOTH] The API shall stop if the user arrives and the API is ready.
[EITHER] The API shall stop if the user arrives or the API starts.
")]);
    let run = f.convert(&["--out", "out"]);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let form = Form::read(&f.read("out/source/specification.mmt")).unwrap();
    let key = "API|stop".to_string();
    let response = Formula::And(vec![
        Formula::atom(Atom::Act { key: key.clone() }),
        Formula::not(Formula::atom(Atom::Forbid { key: key.clone() })),
        Formula::not(Formula::atom(Atom::Discouraged { key })),
    ]);
    let external = Formula::atom(Atom::Event { key: "user arrive".into() });
    let internal = Formula::atom(Atom::Event { key: "API start".into() });
    let state = Formula::atom(Atom::Val { attr: "API".into(), value: "ready".into() });
    let internal_response = Formula::implies(internal.clone(), response.clone());
    for (id, assume, guarantee) in [
        ("PLAIN", Formula::True, response.clone()),
        ("EXTERNAL", external.clone(), response.clone()),
        ("INTERNAL", Formula::True, internal_response),
        ("BOTH", external.clone(), Formula::implies(state, response.clone())),
        ("EITHER", Formula::True, Formula::implies(Formula::Or(vec![external, internal]), response)),
    ] {
        let contract = form.contracts.iter().find(|contract| contract.id == id).unwrap();
        assert_eq!((&contract.assume, &contract.guarantee), (&assume, &guarantee), "{id}");
    }
}

#[test]
fn an_unmapped_form_cannot_produce_an_mmt_archive() {
    let f = Fixture::new(&[
        ("trion.toml", MANIFEST),
        ("a.trion", "primitive API, message\nThe API shall send at most 3 messages per second.\n"),
    ]);
    let result = f.convert(&["--out", "out"]);
    assert_ne!(result.code, 0, "{}{}", result.stdout, result.stderr);
    assert!(result.stdout.contains("role-rate") || result.stderr.contains("role-rate"), "{}{}", result.stdout, result.stderr);
    assert!(!f.path().join("out/source/specification.mmt").exists());
}

#[test]
fn otherwise_negates_the_trigger_within_the_shared_condition() {
    use trion_solver::{Atom, Formula};

    let source = "system API\nenvironment room, door\nprimitive API, room, door, ready\n\
While the room is ready:\n    [BRANCH] If the door opens, then the API shall stop; otherwise, the API shall start.\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", source)]);
    let run = f.convert(&["--out", "out"]);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let form = Form::read(&f.read("out/source/specification.mmt")).unwrap();
    let state = Formula::atom(Atom::Val { attr: "room".into(), value: "ready".into() });
    let trigger = Formula::atom(Atom::Event { key: "door open".into() });
    for (id, guard) in [("BRANCH", trigger.clone()), ("BRANCH/otherwise", Formula::not(trigger))] {
        let branch = form.contracts.iter().find(|contract| contract.id == id).unwrap();
        assert_eq!(branch.assume, Formula::And(vec![state.clone(), guard]), "{id}");
    }
}

#[test]
fn otherwise_with_a_grounded_type_trigger_is_rejected() {
    let source = "individuals user\nprimitive API\nA manager means a user.\n\
[BRANCH] If a user is a manager, then the API shall stop; otherwise, the API shall start.\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", source)]);
    let run = f.convert(&["--out", "out", "--json"]);
    assert_eq!(run.code, 1, "{}{}", run.stdout, run.stderr);
    let report = run.json();
    assert!(report["opaque"].as_array().unwrap().iter().any(|finding|
        finding["code"] == "UNSUPPORTED_SEMANTICS"
            && finding["message"].as_str().unwrap().contains("`otherwise`")
    ), "{report}");
    assert!(!f.path().join("out/source/specification.mmt").exists());
}

#[test]
fn trioc_refuses_a_form_that_does_not_read_with_the_position_of_the_error() {
    let f = package();
    assert_eq!(f.convert(&["--out", "out"]).code, 0);
    let source = f.read("out/source/specification.mmt");
    // A literal where a string is expected: the object reads as MMT, and is no formula of the form.
    f.write("out/source/specification.mmt", &with_first_formula(&source, "(Act 5)"));
    let run = f.prove(&["out"]);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    assert!(run.stderr.contains("is no MMT form of trion: ") && run.stderr.contains("is no string") && has_position(&run.stderr), "{}", run.stderr);
    // A name that is declared nowhere: the notations of the theories do not read it.
    f.write("out/source/specification.mmt", &with_first_formula(&source, "(actt \"a\")"));
    let run = f.prove(&["out"]);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    assert!(run.stderr.contains("is no MMT form of trion: it does not read as MMT: ") && run.stderr.contains("unbound token: actt") && has_position(&run.stderr), "{}", run.stderr);
    // A well-typed replacement is read; the obligations still name the formula.
    f.write("out/source/specification.mmt", &with_first_formula(&source, "(not (Act \"a\"))"));
    let run = f.prove(&["out"]);
    assert_ne!(run.code, 2, "{}{}", run.stdout, run.stderr);
}

#[test]
fn a_form_that_the_meta_theory_does_not_describe_is_not_written() {
    let f = package();
    assert_eq!(f.convert(&["--out", "out"]).code, 0);
    let form = Form::read(&f.read("out/source/specification.mmt")).unwrap();
    // A role and a property that the meta-theory does not name, and a
    // question about a formula that the form does not hold.
    let mut wrong = form.clone();
    wrong.contracts[0].role = "wish".to_string();
    assert!(wrong.write().unwrap_err().contains("as_wish"));
    let mut wrong = form.clone();
    wrong.obligations.obligations[0].property = "beauty".to_string();
    assert!(wrong.write().unwrap_err().contains("beauty"));
    let mut wrong = form;
    wrong.obligations.obligations[0].question = trion_verification::ObligationQuestion::Satisfiable { query: vec![wrong.obligations.pool.len()] };
    assert!(wrong.write().is_err());
}

#[test]
fn the_form_is_written_and_proved_without_java_or_the_tools() {
    // Nothing is on the search path, and the package is outside the
    // repository: trion and trioc run no other program, and every
    // certificate is written without one.
    let f = package();
    let run = |program: &str, args: &[&str]| std::process::Command::new(program).env_clear().env("PATH", "").args(args).current_dir(f.path()).output().unwrap();
    let converted = run(env!("CARGO_BIN_EXE_trion"), &["--out", "out"]);
    assert!(converted.status.success(), "{}", String::from_utf8_lossy(&converted.stderr));
    let proved = run(env!("CARGO_BIN_EXE_trioc"), &["prove", "out", "--certificates", "certs", "--format", "smt2,alethe,cpc,moxi"]);
    assert!(proved.status.success(), "{}{}", String::from_utf8_lossy(&proved.stdout), String::from_utf8_lossy(&proved.stderr));
    for dir in ["certs/alethe", "certs/cpc"] {
        assert!(std::fs::read_dir(f.path().join(dir)).is_ok_and(|mut d| d.next().is_some()), "{dir}: {}", String::from_utf8_lossy(&proved.stdout));
    }
}

/// What MMT reports when it builds the archive of an MMT form: it reads the
/// source of the form and type-checks each declaration against the
/// meta-theory, over the archive `MMT/urtheories`; without the colours of
/// the terminal.
fn mmt(archive: &std::path::Path, id: &str) -> String {
    let tools = repo_root().join(".tools");
    let commands = format!("mathpath archive {} ; mathpath archive {} ; build {id} mmt-omdoc", tools.join("urtheories").display(), archive.display());
    let output = std::process::Command::new(tools.join("bin/java")).arg("-jar").arg(tools.join("mmt.jar")).arg("--noshell").arg(commands).current_dir(archive).output().expect("needs .tools/bin/java and .tools/mmt.jar (MMT v27.0.0)");
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
    plain
}

#[test]
fn mmt_accepts_the_form_and_rejects_what_trioc_rejects() {
    let f = package();
    let run = f.convert(&["--out", "out"]);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let report = mmt(&f.path().join("out"), "trion/p");
    assert!(report.contains("'build trion/p mmt-omdoc' finished") && !report.contains("error"), "{report}");
    // MMT wrote the theory of the package as OMDoc.
    let written = std::fs::read_dir(f.path().join("out/content/http..trion.dev/form/p")).map(|d| d.filter_map(std::result::Result::ok).map(|e| e.file_name().to_string_lossy().to_string()).collect::<Vec<_>>()).unwrap_or_default();
    assert!(written.iter().any(|name| name.ends_with(".omdoc.xz")), "{written:?} {report}");
    // A formula of the wrong type: MMT reports an error, and trioc refuses the form.
    let source = f.read("out/source/specification.mmt");
    f.write("out/source/specification.mmt", &with_first_formula(&source, "(Act 5)"));
    let report = mmt(&f.path().join("out"), "trion/p");
    assert!(report.contains("error") && report.contains("Act 5"), "{report}");
    let refused = f.prove(&["out"]);
    assert_eq!(refused.code, 2, "{}{}", refused.stdout, refused.stderr);
}

#[test]
fn mmt_accepts_long_lists_as_trion_writes_them() {
    // Lists longer than a run are written balanced with the `join` constants of the meta-theory.
    let f = package();
    assert_eq!(f.convert(&["--out", "out"]).code, 0);
    let mut form = Form::read(&f.read("out/source/specification.mmt")).unwrap();
    form.obligations.pool[0] = trion_solver::Formula::And((0..100).map(|i| trion_solver::Formula::Atom(trion_solver::Atom::Act { key: format!("API|step {i}") })).collect());
    form.contracts[0].timing = (0..20).map(|i| format!("moment {i}")).collect();
    let text = form.write().unwrap();
    assert!(text.contains("pjoin") && text.contains("sjoin"), "{text}");
    f.write("out/source/specification.mmt", &text);
    let report = mmt(&f.path().join("out"), "trion/p");
    assert!(report.contains("'build trion/p mmt-omdoc' finished") && !report.contains("error"), "{report}");
    assert_eq!(Form::read(&text).unwrap(), form);
}

#[test]
fn mmt_accepts_the_form_of_trions_own_specification() {
    // The self-hosting package: the largest form trion writes, with long lists.
    let out = tempfile::tempdir().unwrap();
    let run = convert_in(&repo_root(), &["--out", &out.path().to_string_lossy()]);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let text = std::fs::read_to_string(out.path().join("source/specification.mmt")).unwrap();
    assert!(text.contains("join"), "the self-hosting form has lists longer than a run");
    let form = Form::read(&text).unwrap();
    assert!(!form.obligations.obligations.is_empty());
    let report = mmt(out.path(), "trion/trion");
    assert!(report.contains("'build trion/trion mmt-omdoc' finished") && !report.contains("error"), "{report}");
}
