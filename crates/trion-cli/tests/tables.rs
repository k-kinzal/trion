mod common;

use common::Fixture;
use trioc_cli::mmt::Form;

const MANIFEST: &str = "[package]\nname = \"p\"\n";

#[test]
fn statement_tables_have_the_same_mmt_meaning_as_their_sentences() {
    let prefix = "namespace p:\n    system API\n    environment door\n    primitive API, door, open\n    While the door is open:\n";
    let sentence = format!("{prefix}        [STOP] The API shall stop.\n");
    let table = format!(
        "{prefix}{}",
        r#"        table "Requirements":
            | Rule {id} | Reading {statement} |
            | --- | --- |
            | [STOP] | The API shall stop. |
"#
    );

    let read = |source: &str| {
        let fixture = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", source)]);
        let result = fixture.convert(&["--out", "out"]);
        assert_eq!(result.code, 0, "{}{}", result.stdout, result.stderr);
        Form::read(&fixture.read("out/source/specification.mmt")).unwrap()
    };
    let ordinary = read(&sentence);
    let tabular = read(&table);
    assert_eq!(ordinary.obligations, tabular.obligations);
    let [original] = ordinary.contracts.as_slice() else {
        panic!("one ordinary contract");
    };
    let [row] = tabular.contracts.as_slice() else {
        panic!("one table contract");
    };
    assert_eq!(row.id, "STOP");
    assert_eq!(row.line, 9);
    assert_eq!(row.assume, original.assume);
    assert_eq!(row.guarantee, original.guarantee);
}

#[test]
fn mapping_tables_resolve_references_and_render_as_tables() {
    let fixture = Fixture::new(&[
        ("trion.toml", MANIFEST),
        (
            "obligations.trion",
            r#"namespace p:
    system API
    primitive API
    table "Requirements":
        | Rule {id} | Reading {statement} |
        | --- | --- |
        | [STOP] | The API shall stop. |
"#,
        ),
        (
            "forms.trion",
            r#"namespace p:
    table "Obligation mappings":
        | Form | Rule {references} |
        | --- | --- |
        | Stop \| Halt | [STOP] |
"#,
        ),
    ]);
    let result = fixture.convert(&[
        "--format", "mmt", "--format", "html", "--format", "markdown", "--out", "out",
    ]);
    assert_eq!(result.code, 0, "{}{}", result.stdout, result.stderr);
    let html = fixture.read("out/specification.html");
    assert!(
        html.contains("<caption>Obligation mappings</caption>"),
        "{html}"
    );
    assert!(html.contains("<td>Stop | Halt</td>"), "{html}");
    assert!(html.contains("href=\"#STOP\""), "{html}");
    assert!(html.contains("id=\"STOP\""), "{html}");
    let markdown = fixture.read("out/specification.md");
    assert!(
        markdown.contains("| Stop \\| Halt | [`STOP`](#STOP) |"),
        "{markdown}"
    );
    assert!(markdown.contains("G = Act(API|stop)"), "{markdown}");

    let changed = fixture.read("forms.trion").replace("[STOP]", "[MISSING]");
    fixture.write("forms.trion", &changed);
    let result = fixture.convert(&["--out", "invalid"]);
    assert_eq!(result.code, 1, "{}{}", result.stdout, result.stderr);
    assert!(
        result.stdout.contains("error[UNRESOLVED_REFERENCE]")
            && result.stdout.contains("forms.trion:5"),
        "{}",
        result.stdout
    );
    assert!(!fixture
        .path()
        .join("invalid/source/specification.mmt")
        .exists());
}

#[test]
fn invalid_rows_have_positioned_diagnostics() {
    for (heading, row) in [
        ("| Form | References {references} |", "| Stop | |"),
        (
            "| Form | References {references} |",
            "| Stop | [STOP] | Extra |",
        ),
        (
            "| Rule {id} | Reading {statement} |",
            "| STOP | The API shall stop. |",
        ),
        (
            "| Rule {id} | Reading {statement} |",
            "| [STOP] | The API shall stop. The API shall stop. |",
        ),
        (
            "| Rule {id} | Reading {unknown} |",
            "| [STOP] | The API shall stop. |",
        ),
    ] {
        let source = format!("namespace p:\n    table \"Invalid row\":\n        {heading}\n        | --- | --- |\n        {row}\n");
        let (parsed, diagnostics) = trion_language::parse_document(&source, "table.trion");
        assert!(
            diagnostics.iter().any(|d| d.code == "parse-table"
                && d.refs
                    .iter()
                    .any(|r| r.file == "table.trion" && [3, 5].contains(&r.line))),
            "{diagnostics:?}"
        );
        assert!(parsed
            .documents
            .iter()
            .all(|d| d.tables.is_empty() && d.specs.is_empty()));
    }
}
