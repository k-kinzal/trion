use trion_language::{parse_document, scan_imports, Document, Meta};

fn parsed_file(src: &str) -> trion_language::ParsedFile {
    let (file, diags) = parse_document(src, "a.trion");
    assert!(diags.is_empty(), "{diags:?}");
    file
}

fn parsed(body: &str) -> Document {
    parsed_file(&format!("namespace p\n{body}\n")).documents.remove(0)
}

fn codes(src: &str) -> Vec<String> {
    parse_document(src, "a.trion").1.into_iter().map(|d| d.code).collect()
}

fn first_code(body: &str) -> String {
    codes(&format!("namespace p\n{body}\n")).first().expect("a diagnostic").clone()
}

#[test]
fn reads_declarations_and_specifications() {
    let doc = parsed("use grpc\nterm room_type: attribute\nalias the service = API\nbind API as grpc.service.\n[S-1] The API shall stop.\n");
    assert_eq!(doc.namespace, "p");
    assert_eq!(doc.imports[0].name, "grpc");
    assert_eq!(doc.vocabulary[0].kind, "attribute");
    assert_eq!(doc.aliases[0].canonical, "API");
    assert_eq!(doc.bindings[0].role, "grpc.service");
    assert_eq!(doc.specs[0].id.as_deref(), Some("S-1"));
}

#[test]
fn reads_the_package_declaration_and_includes() {
    let file = parsed_file("// entry\npackage chat edition \"0.1\"\ninclude \"a/b.trion\"\nnamespace chat.rooms:\n    The API shall stop.\nnamespace chat:\n");
    let package = file.package.expect("a package");
    assert_eq!((package.name.as_str(), package.edition.as_str()), ("chat", "0.1"));
    assert_eq!(file.includes[0].path, "a/b.trion");
    assert_eq!(file.documents.len(), 2);
    assert_eq!(file.documents[0].namespace, "chat.rooms");
}

#[test]
fn rejects_malformed_file_level_declarations() {
    assert_eq!(codes("package chat\n"), ["parse-package"]);
    assert_eq!(codes("package a edition \"1\"\npackage b edition \"1\"\n"), ["parse-package"]);
    assert_eq!(codes("include a.trion\n"), ["parse-include"]);
    assert_eq!(codes("The API shall stop.\n"), ["parse-placement"]);
    // A block closes where its indentation ends, and `end` is not written.
    assert!(codes("namespace p:\n    The API shall stop.\n").is_empty());
    assert_eq!(codes("namespace p:\n    The API shall stop.\nend\n"), ["parse-placement"]);
    assert_eq!(codes("namespace p:\n    The API shall stop.\n    end\n"), ["parse-block"]);
    // Without a colon a namespace runs to the next namespace line.
    assert!(codes("namespace p\nThe API shall stop.\nnamespace p.q\nThe bell shall ring.\n").is_empty());
    assert_eq!(codes("namespace p:\n    namespace q:\n"), ["parse-placement"]);
}

#[test]
fn a_specification_without_an_id_is_identified_by_position() {
    let doc = parsed("\n// note\nThe API shall stop.\n");
    assert_eq!(doc.specs[0].display_id(), "a.trion:4");
    // A later sentence that begins on the same line is told apart by its column.
    let doc = parsed("The API shall stop. The bell shall ring.\n");
    assert_eq!(doc.specs[1].display_id(), "a.trion:2:21");
}

#[test]
fn reads_annotations() {
    let doc = parsed("[S-1] The API shall stop.\n  cite R#QUOTE\n[S-2] The API shall start.\n  unsourced \"an internal decision\"\n");
    assert_eq!(doc.specs[0].meta[0], Meta::Cite { source: "R".into(), quote: Some("QUOTE".into()) });
    assert_eq!(doc.specs[1].meta[0], Meta::Unsourced { reason: "an internal decision".into() });
}

#[test]
fn a_block_citation_applies_to_every_statement_in_the_block() {
    let doc = parsed("section \"Stopping\":\n    cite R\n    [S-1] The API shall stop.\n    [S-2] The API shall start.\n[S-3] The API shall pause.\n");
    assert_eq!(doc.specs[0].meta, [Meta::Cite { source: "R".into(), quote: None }]);
    assert_eq!(doc.specs[1].meta, [Meta::Cite { source: "R".into(), quote: None }]);
    assert!(doc.specs[2].meta.is_empty());
    assert_eq!(doc.specs[0].sections, ["Stopping"]);
}

#[test]
fn a_sentence_continues_on_indented_lines() {
    let doc = parsed("[S-1] The API\n    shall return\n    foo.\n  cite R\n");
    assert_eq!(doc.specs[0].sentence.source, "The API shall return foo.");
    assert_eq!(doc.specs[0].line, 2);
    assert_eq!(doc.specs[0].meta.len(), 1);
}

#[test]
fn a_sentence_may_start_with_a_directive_word() {
    let doc = parsed("Package names are short.\nImport errors are logged.\n");
    assert!(doc.imports.is_empty());
    assert_eq!(doc.specs.len(), 2);
}

#[test]
fn reads_a_role() {
    let doc = parsed("role service:\n    activate: The $subject shall use gRPC.\n    form F: The $subject $op shall $action. where $op matches /^x$/ when $op matches /^x/\n    form G: The $subject $op shall $action. where $op does not match /^y$/\n    required R: The $subject shall define errors.\nThe API shall stop.\n");
    let role = &doc.roles[0];
    assert_eq!(role.activations.len(), 1);
    assert_eq!((role.forms[0].variable.as_str(), role.forms[0].regex.as_str()), ("$op", "^x$"));
    assert_eq!(role.forms[0].applies_when.as_deref(), Some("^x"));
    assert!(role.forms[1].negated);
    assert_eq!(role.required[0].id, "R");
    assert_eq!(doc.specs.len(), 1);
}

#[test]
fn reads_a_source_with_quotes() {
    let doc = parsed("source R:\n    title \"Brief\"\n    kind requirement\n    path \"r.txt\"\n    sha256 \"abc\"\n    locator \"https://example.com\"\n    quote ONE \"\"\"\nline one.\nline two.\n\"\"\"\n    quote TWO \"short.\"\n");
    let source = &doc.sources[0];
    assert_eq!(source.name, "R");
    assert_eq!(source.kind.as_deref(), Some("requirement"));
    assert_eq!(source.path.as_deref(), Some("r.txt"));
    assert_eq!(source.quotes[0].text, "line one.\nline two.");
    assert_eq!(source.quotes[1].name, "TWO");
}

#[test]
fn reports_each_malformed_line_and_continues() {
    let (file, diags) = parse_document("namespace p:\n    The API for gRPC.\n    The API shall stop.\n    cite\n", "a.trion");
    assert_eq!(file.documents[0].specs.len(), 1);
    let codes: Vec<&str> = diags.iter().map(|d| d.code.as_str()).collect();
    assert_eq!(codes, ["MISSING_PREDICATE", "parse-sentence"]);
    assert_eq!(diags[0].refs[0].line, 2);
}

#[test]
fn rejects_malformed_declarations() {
    assert_eq!(first_code("[bad id] The API shall stop.\n"), "parse-spec-id");
    assert_eq!(first_code("[S-1] The API shall stop.\n  cite r#q\n"), "parse-citation");
    assert_eq!(first_code("[S-1] The API shall stop.\n  unsourced because\n"), "parse-citation");
    assert_eq!(first_code("role r:\n    nonsense\n"), "parse-role-line");
    assert_eq!(first_code("role r:\n    form F: The $s shall stop.\n"), "parse-form-rule");
    assert_eq!(first_code("role r:\n    form F: The $s $o shall $a. where $o matches /(/\n"), "parse-form-regex");
    assert_eq!(first_code("source R:\n    colour \"red\"\n"), "parse-source");
    assert_eq!(first_code("section untitled:\n"), "parse-block");
}

#[test]
fn a_japanese_sentence_is_not_controlled_english() {
    assert_eq!(first_code("[S-1] APIはgRPC通信をする。\n"), "NOT_CONTROLLED_ENGLISH");
}

#[test]
fn scans_imports_without_parsing_sentences() {
    assert_eq!(scan_imports("use grpc\nuse errors are logged.\n  use http\n"), ["grpc", "http"]);
}

#[test]
fn annotations_of_a_malformed_sentence_are_dropped() {
    let (file, diags) = parse_document("namespace p:\n    [A] The API shall stop.\n    [B] The API for gRPC.\n      cite R\n", "a.trion");
    assert_eq!(diags.len(), 1, "{diags:?}");
    assert!(file.documents[0].specs[0].meta.is_empty());
}

#[test]
fn one_primitive_declaration_names_one_or_more_terms() {
    let doc = parsed("primitive room\nprimitive source file, owner, entry\n");
    let names: Vec<&str> = doc.primitives.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(names, ["room", "source file", "owner", "entry"]);
    // Each term of the list is declared at the line of the declaration.
    assert_eq!(doc.primitives.iter().map(|p| p.line).collect::<Vec<_>>(), [2, 3, 3, 3]);
}
