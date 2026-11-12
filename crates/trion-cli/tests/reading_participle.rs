//! A past participle after a noun is a relative clause without its marker:
//! it is no word of the name of that noun.

mod common;
use common::*;

fn package(body: &str) -> Fixture {
    let indented: String = body.lines().map(|line| if line.is_empty() { "\n".to_string() } else { format!("    {line}\n") }).collect();
    Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\nentry = \"a.trion\"\n"), ("a.trion", &format!("package p edition \"1\"\n\nnamespace p.x:\n{indented}"))])
}

const TERMS: &str = "primitive parser\nprimitive specification\nprimitive file\nprimitive report\n";

#[test]
fn a_past_participle_after_a_noun_is_no_word_of_its_name() {
    let folded = package(&format!("{TERMS}[A] The parser shall read each specification selected by the report.\n")).trion(&["verify"]);
    assert_eq!(folded.code, 1, "{}", folded.stdout);
    assert!(folded.stdout.contains("UNSUPPORTED_SEMANTICS") && folded.stdout.contains("`selected` is a past participle"), "{}", folded.stdout);
    assert!(folded.stdout.contains("that is"), "{}", folded.stdout);
    // The relative clause with its marker is read, and it says what the participle meant.
    let marked = package(&format!("{TERMS}[A] The parser shall read each specification that is selected by the report.\n")).trion(&["verify"]);
    assert_eq!(marked.code, 0, "{}", marked.stdout);
    // A participle before its noun is a word of the name.
    let before = package(&format!("{TERMS}primitive selected specification\n[A] The parser shall read each selected specification.\n")).trion(&["verify"]);
    assert_eq!(before.code, 0, "{}", before.stdout);
    // A declared term may end in a participle.
    let declared = package(&format!("{TERMS}primitive outcome proved\n[A] The parser shall report the outcome proved.\n")).trion(&["verify"]);
    assert_eq!(declared.code, 0, "{}", declared.stdout);
}
