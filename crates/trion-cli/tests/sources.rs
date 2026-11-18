mod common;
use common::*;

const SOURCE: &str = "要求その一です。要求その二です。";
const QUOTES: [(&str, &str); 2] = [("ONE", "要求その一です。"), ("TWO", "要求その二です。")];

fn requirement(quotes: &[(&str, &str)]) -> String {
    source_block("R", "requirement", "source.txt", SOURCE, "", quotes)
}

fn fixture_with(quotes: &[(&str, &str)], spec: &str) -> Fixture {
    Fixture::new(&[("trion.toml", MANIFEST), ("source.txt", SOURCE), ("sources.trion", &requirement(quotes)), ("a.trion", spec)])
}

fn fixture(spec: &str) -> Fixture {
    fixture_with(&QUOTES, spec)
}

/// What the conversion reports about the sources: the report of the
/// sources as its output, and 1 as its code when it holds an error, which
/// keeps the package from converting.
fn sources(f: &Fixture) -> Result {
    let report = f.verify(&["--json"]).json();
    let failed = report["sources"]["diagnostics"].as_array().unwrap().iter().any(|d| d["severity"] == "error");
    assert_eq!(failed, report["conforms"] == false && unverified(&report).iter().any(|code| code.starts_with("source")), "{report}");
    Result { code: i32::from(failed), stdout: report["sources"].to_string(), stderr: String::new() }
}

fn req(f: &Fixture) -> serde_json::Value {
    sources(f).json()
}

const FULL: &str = "[A] The API shall stop.\n  cite R#ONE\n[B] The API shall start.\n  cite R#TWO\n";

#[test]
fn full_coverage_passes() {
    let f = fixture(FULL);
    let r = sources(&f);
    assert_eq!(r.code, 0, "{}", r.stdout);
    assert_eq!(r.json()["sources"][0]["percent"], 100.0);
    assert_eq!(r.json()["sources"][0]["kind"], "requirement");
}

#[test]
fn a_quote_cuts_no_sentence() {
    let f = fixture_with(&[("ONE", "要求その一"), ("TWO", "要求その二です。")], FULL);
    assert_eq!(report_codes(&req(&f))[0], "source-quote-partial");
    let f = fixture_with(&[("ONE", "その一です。"), ("TWO", "要求その二です。")], FULL);
    assert_eq!(report_codes(&req(&f))[0], "source-quote-partial");
}

#[test]
fn a_quote_may_end_at_a_line_break() {
    let text = "A heading\nA sentence.\n";
    let block = source_block("C", "citation", "c.txt", text, "", &[("HEAD", "A heading"), ("BODY", "A sentence.")]);
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("c.txt", text), ("s.trion", &block), ("a.trion", "[A] The API shall stop.\n  cite C#HEAD\n  cite C#BODY\n")]);
    let r = req(&f);
    assert!(report_codes(&r).is_empty(), "{r}");
    assert_eq!(r["sources"][0]["percent"], 100.0);
}

#[test]
fn coverage_counts_characters_per_sentence() {
    let f = fixture("[A] The API shall stop.\n  cite R#ONE\n");
    let report = req(&f);
    let units = report["sources"][0]["units"].as_array().unwrap();
    assert_eq!(units.len(), 2);
    assert_eq!((units[0]["total"].as_u64(), units[0]["covered"].as_u64()), (Some(8), Some(8)));
    assert_eq!((units[1]["covered"].as_u64(), units[1]["uncovered"].as_str()), (Some(0), Some("要求その二です。")));
}

#[test]
fn only_a_cited_quote_counts() {
    let f = fixture("[A] The API shall stop.\n  cite R#ONE\n");
    let report = req(&f);
    assert_eq!(report["sources"][0]["percent"], 50.0);
    assert!(report_codes(&report).contains(&"source-quote-unused".to_string()));
}

#[test]
fn several_specifications_can_cite_one_quote() {
    let f = fixture("[A] The API shall stop.\n  cite R#ONE\n[B] The API shall start.\n  cite R#ONE\n[C] The API shall run.\n  cite R#TWO\n");
    assert_eq!(req(&f)["sources"][0]["percent"], 100.0);
}

#[test]
fn one_specification_can_cite_many_quotes() {
    let f = fixture("[A] The API shall stop.\n  cite R#ONE\n  cite R#TWO\n");
    assert_eq!(req(&f)["sources"][0]["percent"], 100.0);
}

#[test]
fn a_block_citation_covers_for_every_statement_in_it() {
    let f = fixture("section \"Stopping\":\n    cite R#ONE\n    cite R#TWO\n    [A] The API shall stop.\n    [B] The API shall start.\n");
    let r = req(&f);
    assert!(report_codes(&r).is_empty(), "{r}");
    assert_eq!(r["sources"][0]["percent"], 100.0);
}

#[test]
fn coverage_below_the_minimum_fails() {
    let f = fixture("[A] The API shall stop.\n  cite R#ONE\n");
    let r = sources(&f);
    assert_eq!(r.code, 1);
    assert_eq!(report_codes(&r.json()), ["source-quote-unused", "source-coverage-below-minimum"]);
}

#[test]
fn a_source_can_lower_its_minimum() {
    let block = source_block("R", "requirement", "source.txt", SOURCE, "minimum 50", &QUOTES);
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("source.txt", SOURCE), ("s.trion", &block), ("a.trion", "[A] The API shall stop.\n  cite R#ONE\n")]);
    let r = sources(&f);
    assert_eq!(r.code, 0, "{}", r.stdout);
}

#[test]
fn a_changed_quote_is_an_error() {
    let f = fixture_with(&[("ONE", "要求その壱です。"), ("TWO", "要求その二です。")], FULL);
    assert!(report_codes(&req(&f)).contains(&"source-quote-not-found".to_string()));
}

#[test]
fn an_ambiguous_quote_is_an_error() {
    let text = "同じ文です。同じ文です。";
    let block = source_block("R", "requirement", "r.txt", text, "", &[("SAME", "同じ文です。")]);
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("r.txt", text), ("s.trion", &block), ("a.trion", "[A] The API shall stop.\n  cite R#SAME\n")]);
    assert!(report_codes(&req(&f)).contains(&"source-quote-ambiguous".to_string()));
}

#[test]
fn a_changed_source_is_an_error() {
    let f = fixture(FULL);
    f.write("source.txt", "要求その一です。要求その二です。追加。");
    assert!(report_codes(&req(&f)).contains(&"source-changed".to_string()));
}

#[test]
fn an_unreadable_source_is_an_error() {
    let f = fixture(FULL);
    std::fs::remove_file(f.path().join("source.txt")).unwrap();
    assert!(report_codes(&req(&f)).contains(&"source-unreadable".to_string()));
}

#[test]
fn a_specification_without_a_source_is_a_warning() {
    let f = fixture(&format!("{FULL}[C] The API shall run.\n"));
    let report = req(&f);
    assert_eq!(report_codes(&report), ["unsourced"]);
    assert_eq!(report["diagnostics"][0]["severity"], "warning");
    // A warning keeps no package from converting.
    assert_eq!(sources(&f).code, 0);
}

#[test]
fn an_unknown_source_or_quote_is_unresolved() {
    let f = fixture(&format!("{FULL}[C] The API shall run.\n  cite X#ONE\n[D] The API shall wait.\n  cite R#NOPE\n"));
    let codes = analysis_codes(&f.verify(&["--json"]).json());
    assert_eq!(codes, ["UNRESOLVED_CITATION", "UNRESOLVED_CITATION"]);
}

#[test]
fn a_source_without_a_local_copy_has_no_coverage() {
    let block = "source WEB:\n    kind citation\n    locator \"https://example.com/\"\n";
    let f = fixture(&format!("{block}{FULL}[C] The API shall run.\n  cite WEB\n"));
    let r = req(&f);
    assert!(report_codes(&r).is_empty(), "{r}");
    assert_eq!(r["sources"].as_array().unwrap().len(), 1);
}

#[test]
fn specifications_without_a_source_are_listed_with_their_reason() {
    let f = fixture(&format!("{FULL}[C] The API shall run.\n  unsourced \"an internal decision\"\n"));
    let report = req(&f);
    assert_eq!(report["unsourced"][0]["id"], "C");
    assert_eq!(report["unsourced"][0]["reason"], "an internal decision");
    assert_eq!(report["sources"][0]["percent"], 100.0, "they do not count as coverage");
    let text = f.verify(&[]).stdout;
    assert!(text.contains("warning[unsourced]: this statement names no source: an internal decision"), "{text}");
}

#[test]
fn a_definition_needs_a_source_too() {
    let f = fixture(&format!("{FULL}[D] A room means a place.\n"));
    assert_eq!(report_codes(&req(&f)), ["unsourced"]);
}

#[test]
fn a_citation_has_its_own_coverage() {
    let text = "An outside authority.\n";
    let block = source_block("C", "citation", "c.txt", text, "locator \"https://example.com/\"", &[("ALL", "An outside authority.")]);
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("c.txt", text), ("s.trion", &block), ("a.trion", "[A] The API shall stop.\n  cite C#ALL\n")]);
    let report = sources(&f).json();
    assert_eq!(report["sources"][0]["kind"], "citation");
    assert_eq!(report["sources"][0]["percent"], 100.0);
}

#[test]
fn an_unknown_source_kind_is_an_error() {
    let block = source_block("C", "rumor", "c.txt", "x.", "", &[("X", "x.")]);
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("c.txt", "x."), ("s.trion", &block), ("a.trion", "[A] The API shall stop.\n  cite C#X\n")]);
    assert_eq!(report_codes(&req(&f)), ["source-kind-unknown"]);
}

#[test]
fn a_source_path_is_relative_to_the_declaring_file() {
    let block = source_block("C", "citation", "texts/c.txt", "x.", "", &[("X", "x.")]);
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("refs/texts/c.txt", "x."), ("refs/s.trion", &block), ("a.trion", "[A] The API shall stop.\n  cite C#X\n")]);
    let r = req(&f);
    assert!(report_codes(&r).is_empty(), "{r}");
}

#[test]
fn a_dependency_can_cite_its_own_source() {
    let text = "Cited text.\n";
    let block = source_block("C", "citation", "c.txt", text, "", &[("ALL", "Cited text.")]);
    let root = "[package]\nname = \"p\"\n\n[dependencies]\nd = { path = \"dep\" }\n";
    let f = Fixture::new(&[
        ("trion.toml", root),
        ("dep/trion.toml", "[package]\nname = \"d\"\n"),
        ("dep/c.txt", text),
        ("dep/s.trion", &block),
        ("dep/d.trion", "[D] The bell shall ring.\n  cite C#ALL\n"),
        ("a.trion", "use d\n[A] The API shall stop.\n  unsourced \"Not needed.\"\n"),
    ]);
    let report = sources(&f).json();
    assert_eq!(report["sources"][0]["id"], "C");
    assert_eq!(report["sources"][0]["percent"], 100.0);
}

#[test]
fn a_quote_can_span_lines() {
    let text = "Heading\nHeading again.\n";
    let block = format!("source C:\n    kind citation\n    path \"c.txt\"\n    sha256 \"{}\"\n    quote BOTH \"\"\"\nHeading\nHeading again.\n\"\"\"\n", sha256(text));
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("c.txt", text), ("s.trion", &block), ("a.trion", "[A] The API shall stop.\n  cite C#BOTH\n")]);
    assert_eq!(sources(&f).json()["sources"][0]["percent"], 100.0);
}


/// A quote that reads as trion sentences is a reference of the statements
/// that cite it (spec/verification.trion, `A source is a reference only if
/// the quotes of the source are statements of the trion language`): they
/// owe correctness and completeness against it. A quote in other prose is
/// traced and is no reference.
#[test]
fn a_quote_that_reads_as_trion_sentences_is_a_reference_of_the_statements_that_cite_it() {
    const TEXT: &str = "The API shall store the message.\n要求その二です。\n";
    let block = source_block("R", "requirement", "r.txt", TEXT, "", &[("STOP", "The API shall store the message."), ("PROSE", "要求その二です。")]);
    let run = |spec: &str| {
        let f = Fixture::new(&[("trion.toml", MANIFEST), ("r.txt", TEXT), ("s.trion", &block), ("a.trion", &format!("system API\nprimitive API, message\n{spec}"))]);
        f.verify(&["--json"]).json()
    };
    // The statement says what the quote says: it refines it.
    let same = run("[A] The API shall store the message.\n  cite R#STOP\n[B] The API shall log the message.\n  cite R#PROSE\n");
    let found = verdicts(&same);
    assert_eq!(found.get("reference/R#STOP").map(String::as_str), Some("proved"), "{same}");
    assert_eq!(found.get("completeness/R#STOP").map(String::as_str), Some("proved"), "{same}");
    // The prose quote is no reference: nothing is owed against it.
    assert!(!found.keys().any(|name| name.contains("PROSE")), "{found:?}");
    // A statement that says something else does not refine the quote, and
    // together they can be kept: more statements would complete it.
    let other = run("[A] The API shall log the message.\n  cite R#STOP\n[B] The API shall log the message.\n  cite R#PROSE\n");
    let found = verdicts(&other);
    assert_eq!(found.get("reference/R#STOP").map(String::as_str), Some("refuted"), "{other}");
    assert_eq!(found.get("completeness/R#STOP").map(String::as_str), Some("refuted"), "{other}");
    // A statement that contradicts the quote does not refine it, and no
    // consistent document refines both: it is not incomplete.
    let against = run("[A] The API shall not store the message.\n  cite R#STOP\n[B] The API shall log the message.\n  cite R#PROSE\n");
    let found = verdicts(&against);
    assert_eq!(found.get("reference/R#STOP").map(String::as_str), Some("refuted"), "{against}");
    assert_eq!(found.get("completeness/R#STOP").map(String::as_str), Some("proved"), "{against}");
}
