mod common;
use common::*;
use trion_language::parse_sentence;
use trion_language::syntax::syntax_forms;

fn manifest() -> String {
    format!("[package]\nname = \"p\"\n\n[dependencies]\nears = {{ path = \"{}\" }}\n", repo_root().join("stdlib/ears").display())
}

fn ears_codes(spec: &str) -> Vec<String> {
    let manifest = manifest();
    report_codes(&Fixture::new(&[("trion.toml", &manifest), ("a.trion", spec)]).verify(&["--json"]).json())
}

/// As `ears_codes`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn ears_codes_of_the_analysis(spec: &str) -> Vec<String> {
    let manifest = manifest();
    analysis_codes(&Fixture::new(&[("trion.toml", &manifest), ("a.trion", spec)]).verify(&["--json"]).json())
}

fn forms(text: &str) -> Vec<&'static str> {
    syntax_forms(&parse_sentence(text).unwrap())
}

#[test]
fn each_pattern_is_classified() {
    assert_eq!(forms("The API shall stop."), ["Ubiquitous"]);
    assert_eq!(forms("While the door is open, the API shall stop."), ["State-driven"]);
    assert_eq!(forms("When the door opens, the API shall stop."), ["Event-driven"]);
    assert_eq!(forms("Where the car has a sunroof, the car shall stop."), ["Optional-feature"]);
    assert_eq!(forms("If the door opens, then the API shall stop."), ["Unwanted-behaviour"]);
    assert_eq!(forms("While the door is open, when the bell rings, the API shall stop."), ["Complex"]);
}

#[test]
fn forms_outside_ears_are_named() {
    assert_eq!(forms("The API must stop."), ["Ubiquitous", "Must"]);
    assert_eq!(forms("The API shall not stop."), ["Ubiquitous", "Prohibition"]);
    assert_eq!(forms("The API may stop."), ["Ubiquitous", "Permission"]);
    assert_eq!(forms("The API should stop."), ["Ubiquitous", "Recommendation"]);
    assert_eq!(forms("The API shall stop, unless the door is open."), ["Ubiquitous", "Exception"]);
    assert_eq!(forms("After the door opens, the API shall stop."), ["Event-driven", "Temporal-opener"]);
    assert_eq!(forms("room_type is Private."), ["Description"]);
    assert_eq!(forms("A room means a shared channel."), ["Definition"]);
}

#[test]
fn the_ears_package_closes_the_syntax() {
    assert_eq!(ears_codes("use ears\nroom_type is Private.\n"), ["syntax-not-allowed"]);
    assert!(ears_codes("room_type is Private.\n").is_empty());
}

#[test]
fn the_generic_syntax_is_accepted() {
    assert!(ears_codes_of_the_analysis("use ears\nWhile the door is open, when the bell rings, the API shall stop.\n").is_empty());
}

#[test]
fn a_second_trigger_is_rejected() {
    assert_eq!(ears_codes("use ears\nWhen the door opens, when the bell rings, the API shall stop.\n"), ["parse-sentence"]);
}

#[test]
fn unsupported_syntax_is_rejected() {
    for spec in ["The API shall not stop.", "The API may stop.", "The API should stop.", "The API must stop.", "The API shall stop, unless the door is open.", "A room means a shared channel."] {
        assert_eq!(ears_codes_of_the_analysis(&format!("use ears\n{spec}\n")), ["syntax-not-allowed"], "{spec}");
    }
}

#[test]
fn an_extension_allows_a_form() {
    assert!(ears_codes_of_the_analysis("use ears\nextend ears::syntax with Prohibition.\nThe API shall not stop.\n").is_empty());
}

#[test]
fn an_extension_is_scoped_to_its_namespace() {
    let manifest = manifest();
    let f = Fixture::new(&[
        ("trion.toml", &manifest),
        ("x.trion", "namespace p.x:\n    use ears\n    extend ears::syntax with Prohibition.\n    The API shall not stop.\n"),
        ("y.trion", "namespace p.y:\n    use ears\n    The bell shall not ring.\n"),
        ("z.trion", "namespace p.z:\n    The door shall not open.\n"),
    ]);
    let r = f.verify(&["--json"]).json();
    assert_eq!(analysis_codes(&r), ["syntax-not-allowed"]);
    assert_eq!(r["diagnostics"][0]["refs"][0]["file"], "y.trion");
}

#[test]
fn an_extension_adds_to_a_closed_domain() {
    let f = Fixture::new(&[("a.trion", "kind is A and B.\nextend kind with C.\nkind is C.\n")]);
    assert_eq!(f.verify(&["a.trion"]).code, 0);
    let f = Fixture::new(&[("a.trion", "kind is A and B.\nkind is C.\n")]);
    assert_eq!(f.verify(&["a.trion"]).code, 1);
}

#[test]
fn only_a_closed_domain_can_be_extended() {
    let f = Fixture::new(&[("a.trion", "kind is A.\nextend kind with C.\n")]);
    assert_eq!(report_codes(&f.verify(&["--json", "a.trion"]).json()), ["extend-open-domain"]);
}

#[test]
fn a_term_resolves_to_its_namespace_definition() {
    let vocab = {
        let manifest = manifest();
        Fixture::new(&[("trion.toml", &manifest), ("a.trion", "use ears\nThe API shall read an EARS pattern.\n")]).inspect(&["vocab", "--json"]).json()
    };
    let entry = &vocab["ears::EARS pattern"];
    assert!(entry["defined_at"]["text"].as_str().unwrap().contains("one fixed form"), "{vocab}");
    assert_eq!(entry["occurrences"], 2);
}

#[test]
fn every_pattern_has_a_definition() {
    let text = std::fs::read_to_string(repo_root().join("stdlib/ears/trion.trion")).unwrap();
    for pattern in ["Ubiquitous", "State-driven", "Event-driven", "Optional-feature", "Unwanted-behaviour", "Complex"] {
        assert!(text.contains(&format!(" {pattern} requirement means ")), "{pattern}");
    }
}
