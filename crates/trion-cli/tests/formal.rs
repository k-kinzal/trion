//! The theorems that the rules of the composite vocabulary rest on: the
//! Lean package of `formal/` builds, each theorem that the rules name is
//! proved there, and each theorem there is named by a rule. A proof that is
//! left open fails the build: the package turns each warning into an error.

mod common;
use common::*;
use std::collections::BTreeSet;
use std::fs;
use std::process::Command;

/// The names that follow `before` in a text, each up to the first character
/// that is no part of a name.
fn names_after(text: &str, before: &str) -> BTreeSet<String> {
    text.split(before).skip(1).map(|rest| rest.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect::<String>()).filter(|name| !name.is_empty()).collect()
}

#[test]
fn each_rule_of_the_composite_vocabulary_rests_on_a_theorem_that_is_proved() {
    // The rules name their theorems where they are implemented.
    let rules = fs::read_to_string(repo_root().join("crates/trion-language/src/syntax/composite.rs")).unwrap();
    let named = names_after(&rules.replace("theorem\n//!   `", "theorem `"), "theorem `");
    let source = fs::read_to_string(repo_root().join("formal/Trion/Distribution.lean")).unwrap();
    let proved: BTreeSet<String> = source.lines().filter_map(|line| line.strip_prefix("theorem ")).map(|rest| rest.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect()).collect();
    assert!(named.len() >= 11, "{named:?}");
    assert_eq!(named, proved, "the rules name the theorems on the left, and formal/Trion/Distribution.lean proves those on the right");
    // No proof is left open, and a warning is an error of the build.
    for file in ["Contract.lean", "Distribution.lean"] {
        let text = fs::read_to_string(repo_root().join("formal/Trion").join(file)).unwrap();
        assert!(!text.contains("sorry") && !text.contains("axiom "), "{file} leaves a proof open");
    }
    assert!(fs::read_to_string(repo_root().join("formal/lakefile.lean")).unwrap().contains("warningAsError, true"));
    // The theorems are checked by Lean. Without Lean they are not checked,
    // and that is a failure and no skip.
    let build = Command::new("lake").arg("build").current_dir(repo_root().join("formal")).output().unwrap_or_else(|e| panic!("`lake build` did not run, so the theorems are not checked: {e}"));
    assert!(build.status.success(), "{}{}", String::from_utf8_lossy(&build.stdout), String::from_utf8_lossy(&build.stderr));
}

#[test]
fn each_refusal_of_the_composite_vocabulary_names_its_rule() {
    // Each rule that refuses a sentence is reported through one code, with
    // the reason of the rule in its message.
    for (statement, reason) in [
        ("Some user shall log in and log out.", "is counted"),
        ("The API shall store the message and log the call only when the door is open.", "as a whole"),
        ("The API shall store the message and log the call exactly when the door is open.", "as a whole"),
        ("The API shall validate the request and send the response within 5 seconds.", "written once"),
        ("The API shall create a report and send the report.", "another part names it"),
    ] {
        let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", statement)]);
        let report = f.verify(&["--json"]).json();
        let refusal = report["diagnostics"].as_array().unwrap().iter().find(|d| d["code"] == "composite-not-distributive").unwrap_or_else(|| panic!("{statement} is not refused: {report}"));
        assert!(refusal["message"].as_str().unwrap().contains(reason), "{statement}: {refusal}");
        // A refusal is an error of the conversion: the package is not converted, and nothing is proved.
        assert_eq!(report["conforms"], false, "{statement}");
        assert!(unverified(&report).contains(&"composite-not-distributive".to_string()) && report["proof"].is_null(), "{statement}: {report}");
    }
}

/// The shape of a sentence, as `formal/Trion/Expansion.lean` describes it.
#[derive(Clone)]
struct Shape {
    subjects: usize,
    counted: bool,
    whole: bool,
    /// Each verb phrase: whether it is denied, the number of its objects and whether a measure follows it.
    phrases: Vec<(bool, usize, bool)>,
}

const SUBJECTS: [&str; 2] = ["API", "gateway"];
const VERBS: [&str; 3] = ["store", "forward", "notify"];
const OBJECTS: [[&str; 2]; 3] = [["message", "call"], ["record", "event"], ["client", "auditor"]];

impl Shape {
    /// The line that the oracle reads.
    fn line(&self) -> String {
        let phrases: Vec<String> = self.phrases.iter().map(|(_, objects, measured)| format!("{objects} {}", u8::from(*measured))).collect();
        format!("{} {} {}|{}", self.subjects, u8::from(self.counted), u8::from(self.whole), phrases.join(";"))
    }

    /// A sentence of the shape. The subjects are joined by `and`; each verb
    /// phrase states its modal verb; the objects of a phrase are joined by
    /// `and`, or by `or` where the phrase is denied.
    fn sentence(&self) -> String {
        let determiner = if self.counted { "some" } else { "the" };
        let subjects: Vec<String> = SUBJECTS[..self.subjects].iter().map(|subject| format!("{determiner} {subject}")).collect();
        let phrases: Vec<String> = self
            .phrases
            .iter()
            .enumerate()
            .map(|(number, (denied, objects, measured))| {
                let objects: Vec<String> = OBJECTS[number][..*objects].iter().map(|object| format!("the {object}")).collect();
                format!("shall{} {} {}{}", if *denied { " not" } else { "" }, VERBS[number], objects.join(if *denied { " or " } else { " and " }), if *measured { " within 5 seconds" } else { "" })
            })
            .collect();
        let text = format!("{} {}{}.", subjects.join(" and "), phrases.join(" and "), if self.whole { " only when the door is open" } else { "" });
        let mut letters = text.chars();
        letters.next().map(|first| first.to_uppercase().chain(letters).collect()).unwrap_or_default()
    }

    /// What the implementation gives for the sentence, as the oracle writes
    /// it: the parts by their verb phrase, subject and object, or the rule
    /// that refuses the sentence.
    fn expanded(&self) -> String {
        let text = self.sentence();
        let sentence = match trion_language::parse_sentence(&text) {
            Ok(sentence) => sentence,
            Err(refused) => return format!("unread: {refused}"),
        };
        match trion_language::syntax::composite::expand(&sentence) {
            Err(refused) => {
                let rule = [("is counted", "counted"), ("written once", "measure"), ("as a whole", "whole")].iter().find(|(words, _)| refused.reason.contains(words)).map_or("another rule", |(_, rule)| rule);
                format!("refused {rule}")
            }
            Ok(parts) => {
                let number = |words: &[&str], part: &str| words.iter().position(|word| part.split(|c: char| !c.is_ascii_alphabetic()).any(|found| found == *word));
                let named: Option<Vec<String>> = parts
                    .iter()
                    .map(|part| {
                        let phrase = number(&VERBS, &part.source)?;
                        Some(format!("{phrase}.{}.{}", number(&SUBJECTS, &part.source)?, number(&OBJECTS[phrase], &part.source)?))
                    })
                    .collect();
                named.map_or_else(|| format!("unnamed: {:?}", parts.iter().map(|part| part.source.clone()).collect::<Vec<_>>()), |named| format!("ok {}", named.join(" ")))
            }
        }
    }
}

/// Every shape of up to two subjects and three verb phrases of up to two objects.
fn shapes() -> Vec<Shape> {
    let phrase: Vec<(bool, usize, bool)> = [false, true].iter().flat_map(|denied| [1, 2].iter().flat_map(move |objects| [false, true].iter().map(move |measured| (*denied, *objects, *measured)))).collect();
    let mut lists: Vec<Vec<(bool, usize, bool)>> = phrase.iter().map(|one| vec![*one]).collect();
    for length in 2..=3 {
        let longer: Vec<Vec<(bool, usize, bool)>> = lists.iter().filter(|list| list.len() == length - 1).flat_map(|list| phrase.iter().map(move |one| list.iter().copied().chain([*one]).collect())).collect();
        lists.extend(longer);
    }
    let mut out = Vec::new();
    for subjects in 1..=2 {
        for counted in [false, true] {
            for whole in [false, true] {
                out.extend(lists.iter().map(|phrases| Shape { subjects, counted, whole, phrases: phrases.clone() }));
            }
        }
    }
    out
}

#[test]
fn the_expansion_is_that_of_the_formal_specification() {
    use std::io::Write;
    use std::process::Stdio;
    let formal = repo_root().join("formal");
    let build = Command::new("lake").arg("build").current_dir(&formal).output().unwrap_or_else(|e| panic!("`lake build` did not run, so the implementation is not compared with the specification: {e}"));
    assert!(build.status.success(), "{}{}", String::from_utf8_lossy(&build.stdout), String::from_utf8_lossy(&build.stderr));
    let shapes = shapes();
    assert_eq!(shapes.len(), 8 * (8 + 64 + 512));
    let mut oracle = Command::new(formal.join(".lake/build/bin/trion-oracle")).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    let lines: String = shapes.iter().map(|shape| format!("{}\n", shape.line())).collect();
    let mut input = oracle.stdin.take().unwrap();
    let writer = std::thread::spawn(move || input.write_all(lines.as_bytes()).unwrap());
    let output = oracle.wait_with_output().unwrap();
    writer.join().unwrap();
    let stated: Vec<String> = String::from_utf8(output.stdout).unwrap().lines().map(str::to_string).collect();
    assert_eq!(stated.len(), shapes.len());
    // Each shape: the sentences of the implementation are those of the
    // specification, in the same order, or both refuse by the same rule.
    let mut differing: Vec<String> = shapes.iter().zip(&stated).filter(|(shape, stated)| shape.expanded() != **stated).map(|(shape, stated)| format!("  {}\n    the specification: {stated}\n    the implementation: {}", shape.sentence(), shape.expanded())).collect();
    differing.sort_by_key(String::len);
    assert!(differing.is_empty(), "{} sentences are expanded otherwise than the specification says; the shortest:\n{}", differing.len(), differing.iter().take(8).cloned().collect::<Vec<_>>().join("\n"));
    // One sentence by hand: two subjects and two verb phrases are four sentences, in this order.
    let four = Shape { subjects: 2, counted: false, whole: false, phrases: vec![(false, 1, false), (false, 1, false)] };
    assert_eq!(four.sentence(), "The API and the gateway shall store the message and shall forward the record.");
    assert_eq!(four.expanded(), "ok 0.0.0 0.1.0 1.0.0 1.1.0");
    // The comparison is of sentences that are expanded and of sentences that are refused.
    for answer in ["ok ", "refused counted", "refused measure", "refused whole"] {
        assert!(stated.iter().filter(|line| line.starts_with(answer)).count() > 100, "{answer}");
    }
}
