mod common;
use common::*;
use serde_json::{json, Value};
use std::path::Path;
use trion_lsp::serve;

fn frame(message: &Value) -> String {
    let body = message.to_string();
    format!("Content-Length: {}\r\n\r\n{body}", body.len())
}

fn uri(path: &Path) -> String {
    format!("file://{}", path.canonicalize().unwrap().display())
}

/// Sends the messages and returns everything the server wrote.
fn exchange(messages: &[Value]) -> Vec<Value> {
    let input: String = messages.iter().map(frame).collect();
    let mut output = Vec::new();
    serve(&mut input.as_bytes(), &mut output).unwrap();
    let text = String::from_utf8(output).unwrap();
    text.split("Content-Length: ").filter(|part| !part.is_empty()).map(|part| serde_json::from_str(part.split_once("\r\n\r\n").unwrap().1).unwrap()).collect()
}

fn open(path: &Path, text: &str) -> Value {
    json!({ "jsonrpc": "2.0", "method": "textDocument/didOpen", "params": { "textDocument": { "uri": uri(path), "languageId": "trion", "version": 1, "text": text } } })
}

fn at(id: u64, method: &str, path: &Path, line: u64, character: u64) -> Value {
    json!({ "jsonrpc": "2.0", "id": id, "method": method, "params": { "textDocument": { "uri": uri(path) }, "position": { "line": line, "character": character } } })
}

fn result(replies: &[Value], id: u64) -> Value {
    replies.iter().find(|m| m.get("id") == Some(&json!(id))).unwrap()["result"].clone()
}

fn diagnostics_of(replies: &[Value], path: &Path) -> Vec<Value> {
    let uri = uri(path);
    replies.iter().rfind(|m| m["method"] == "textDocument/publishDiagnostics" && m["params"]["uri"] == uri.as_str()).unwrap()["params"]["diagnostics"].as_array().unwrap().clone()
}

const DEFINING: &str = "namespace p.defs:\n    An EARS pattern is a fixed form.\n";
const USING: &str = "namespace p.app:\n    use p.defs\n    [USE] The API shall read an EARS pattern.\n        unsourced \"Example.\"\n";

fn tree() -> Fixture {
    Fixture::new(&[("trion.toml", MANIFEST), ("defs/d.trion", DEFINING), ("app/a.trion", USING)])
}

#[test]
fn the_server_announces_its_features() {
    let replies = exchange(&[json!({ "jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {} })]);
    let capabilities = &result(&replies, 1)["capabilities"];
    for key in ["hoverProvider", "definitionProvider", "completionProvider", "semanticTokensProvider"] {
        assert!(!capabilities[key].is_null(), "{key}");
    }
}

#[test]
fn diagnostics_follow_the_unsaved_text() {
    let f = Fixture::new(&[("a.trion", "The API shall stop.\n")]);
    let path = f.path().join("a.trion");
    let replies = exchange(&[open(&path, "namespace main:\n    kind is A and B.\n    kind is C.\n")]);
    // The two descriptions leave no environment: the obligation of
    // compatibility is refuted, from the text that is not saved.
    let found: Vec<Value> = diagnostics_of(&replies, &path).into_iter().filter(|d| d["severity"] == 1).collect();
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0]["code"], "incompatible");
}

#[test]
fn hover_shows_a_definition_from_another_namespace() {
    let f = tree();
    let path = f.path().join("app/a.trion");
    let replies = exchange(&[open(&path, USING), at(2, "textDocument/hover", &path, 2, 34)]);
    let text = result(&replies, 2)["contents"]["value"].as_str().unwrap().to_string();
    assert!(text.contains("EARS pattern") && text.contains("defs") && text.contains("a fixed form"), "{text}");
}

#[test]
fn an_ambiguous_name_offers_the_qualified_spelling_of_each_owner() {
    let input = r#"package p
namespace p.left:
    The codec is a tool.
namespace p.right:
    The codec is a tool.
namespace p.app:
    use p.left
    use p.right
    The codec is a service.
"#;
    let fixture = Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\n"), ("trion.trion", input)]);
    let path = fixture.path().join("trion.trion");
    let mut request = at(2, "textDocument/codeAction", &path, 8, 8);
    request["params"]["range"] = json!({
        "start": { "line": 8, "character": 8 },
        "end": { "line": 8, "character": 13 }
    });
    let replies = exchange(&[open(&path, input), request]);
    assert!(diagnostics_of(&replies, &path).iter().any(|entry| entry["code"] == "AMBIGUOUS_TERM"));
    let actions = result(&replies, 2);
    let actions = actions.as_array().unwrap();
    assert_eq!(actions.len(), 2, "{actions:?}");
    for (owner, action) in ["left", "right"].into_iter().zip(actions) {
        let changes = action["edit"]["changes"].as_object().unwrap();
        let edit = &changes.values().next().unwrap()[0];
        assert_eq!(edit["newText"], format!("{owner}::codec"));
        assert_eq!(edit["range"]["start"]["character"], 8);
        assert_eq!(edit["range"]["end"]["character"], 13);
    }
    let fixed = input.replace("The codec is a service.", "The left::codec is a service.");
    let repaired = exchange(&[open(&path, &fixed)]);
    assert!(diagnostics_of(&repaired, &path).iter().all(|entry| entry["code"] != "AMBIGUOUS_TERM"));
}

#[test]
fn predicate_hover_reports_the_resolved_signature() {
    let text = "package p\nnamespace p.wire:\n    system codec\n    term message: object\n    predicate send(codec, message)\n    The codec shall send a message.\n";
    let fixture = Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\n"), ("trion.trion", text)]);
    let path = fixture.path().join("trion.trion");
    let replies = exchange(&[open(&path, text), at(2, "textDocument/hover", &path, 5, 21)]);
    let answer = result(&replies, 2);
    let hover = answer["contents"]["value"].as_str().unwrap();
    assert!(hover.contains("wire::send(wire::codec, wire::message)"), "{hover}");
}

#[test]
fn hovering_an_applied_specification_source_uses_its_authored_names() {
    let manifest = "[package]\nname = \"p\"\n[dependencies]\nprofile.path = \"profile\"\n";
    let root = "package p\nnamespace p:\n    refer profile\n    system receiver\n    There is a receiver.\n    apply profile as receipt with endpoint = receiver\n";
    let dependency = "package profile\nnamespace profile:\n    system endpoint\n    [START] The endpoint shall start.\n";
    let fixture = Fixture::raw(&[
        ("trion.toml", manifest),
        ("trion.trion", root),
        ("profile/trion.toml", "[package]\nname = \"profile\"\n"),
        ("profile/trion.trion", dependency),
    ]);
    let root_path = fixture.path().join("trion.trion");
    let source_path = fixture.path().join("profile/trion.trion");
    let replies = exchange(&[
        open(&root_path, root),
        at(1, "textDocument/hover", &root_path, 5, 7),
        at(2, "textDocument/hover", &source_path, 3, 19),
    ]);
    let application = result(&replies, 1);
    assert!(application.to_string().contains("symbol mapping"), "{application}");
    let source = result(&replies, 2);
    let hover = source["contents"]["value"].as_str().unwrap();
    assert!(hover.contains("**endpoint** in namespace `profile`"), "{hover}");
}

#[test]
fn hover_shows_the_form_and_sources_of_a_specification() {
    let f = tree();
    let path = f.path().join("app/a.trion");
    let replies = exchange(&[open(&path, USING), at(2, "textDocument/hover", &path, 2, 6)]);
    let text = result(&replies, 2)["contents"]["value"].as_str().unwrap().to_string();
    assert!(text.contains("Syntax: Ubiquitous") && text.contains("No source"), "{text}");
}

#[test]
fn hover_shows_the_reading_of_a_statement_over_individuals() {
    // The same lines that `verify` prints and the document shows: what the
    // statement is about, where it applies and what it requires.
    let text = "individuals user, room, ticket\nprimitive system, member\n\nEach member is a user.\n\n[N] When a user enters a room, the system shall notify a member of the room within 2 seconds.\n    unsourced \"Example.\"\n\n[K] Each room has exactly one member.\n    unsourced \"Example.\"\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", text)]);
    let path = f.path().join("a.trion");
    let line = |id: &str| f.read("a.trion").lines().position(|l| l.starts_with(id)).unwrap() as u64;
    let replies = exchange(&[open(&path, &f.read("a.trion")), at(2, "textDocument/hover", &path, line("[N]"), 1), at(3, "textDocument/hover", &path, line("[K]"), 1)]);
    let shown = result(&replies, 2)["contents"]["value"].as_str().unwrap().to_string();
    assert!(shown.contains("Reading over individuals (domains of 3 individuals):"), "{shown}");
    for part in ["- about: each user; each room; some member (an individual of `user`) that is a member of the room, chosen by the response", "- applies at each occurrence at which: [the user enter the room] occurs", "- requires: [the system notify the member], completed at most 2000 ms after the occurrence (the end included)"] {
        assert!(shown.contains(part), "{part}\n{shown}");
    }
    let domain = result(&replies, 3)["contents"]["value"].as_str().unwrap().to_string();
    assert!(domain.contains("Reading over individuals: a statement about the domain"), "{domain}");
}

#[test]
fn hover_explains_an_ears_keyword() {
    let f = Fixture::new(&[("a.trion", "While the door is open, the API shall stop.\n")]);
    let path = f.path().join("a.trion");
    let text = "namespace main:\n    While the door is open, the API shall stop.\n";
    let replies = exchange(&[open(&path, text), at(2, "textDocument/hover", &path, 1, 5)]);
    assert!(result(&replies, 2)["contents"]["value"].as_str().unwrap().contains("state-driven"));
}

#[test]
fn definition_jumps_to_the_namespace_that_defines_the_term() {
    let f = tree();
    let path = f.path().join("app/a.trion");
    let replies = exchange(&[open(&path, USING), at(2, "textDocument/definition", &path, 2, 34)]);
    let location = result(&replies, 2);
    assert_eq!(location["uri"], uri(&f.path().join("defs/d.trion")));
    assert_eq!(location["range"]["start"]["line"], 1);
}

#[test]
fn completion_offers_terms_and_keywords() {
    let f = tree();
    let path = f.path().join("app/a.trion");
    let replies = exchange(&[open(&path, USING), at(2, "textDocument/completion", &path, 2, 4)]);
    let labels: Vec<String> = result(&replies, 2).as_array().unwrap().iter().map(|i| i["label"].as_str().unwrap().to_string()).collect();
    assert!(labels.contains(&"defs::EARS pattern".to_string()) && labels.contains(&"shall".to_string()) && labels.contains(&"cite".to_string()) && labels.contains(&"namespace".to_string()), "{labels:?}");
}

#[test]
fn semantic_tokens_mark_keywords_terms_and_annotations() {
    let f = tree();
    let path = f.path().join("app/a.trion");
    let replies = exchange(&[open(&path, USING), at(2, "textDocument/semanticTokens/full", &path, 0, 0)]);
    let data: Vec<u64> = result(&replies, 2)["data"].as_array().unwrap().iter().map(|v| v.as_u64().unwrap()).collect();
    let kinds: Vec<u64> = data.chunks(5).map(|t| t[3]).collect();
    assert!(kinds.contains(&0), "keyword: {kinds:?}");
    assert!(kinds.contains(&2), "term: {kinds:?}");
    assert!(kinds.contains(&7), "annotation: {kinds:?}");
    assert!(data.chunks(5).any(|t| t[3] == 2 && t[4] == 1), "an introduced term is marked: {data:?}");
}

#[test]
fn the_command_serves_on_standard_streams() {
    use std::io::{Read, Write};
    use std::process::{Command, Stdio};
    let mut child = Command::new(env!("CARGO_BIN_EXE_trion-lsp")).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(frame(&json!({ "jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {} })).as_bytes()).unwrap();
    let mut out = String::new();
    child.stdout.take().unwrap().read_to_string(&mut out).unwrap();
    assert!(child.wait().unwrap().success());
    assert!(out.contains("semanticTokensProvider"));
}

#[test]
fn hover_on_a_citation_shows_the_quoted_text() {
    let source = "namespace p.refs:\n    source R:\n        kind requirement\n        title \"The request\"\n        quote ONE \"Stop the API.\"\n";
    let using = "namespace p.app:\n    [A] The API shall stop.\n        cite R#ONE\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("refs.trion", source), ("a.trion", using)]);
    let path = f.path().join("a.trion");
    let replies = exchange(&[open(&path, using), at(2, "textDocument/hover", &path, 2, 9), at(3, "textDocument/hover", &path, 1, 6)]);
    let annotation = result(&replies, 2)["contents"]["value"].as_str().unwrap().to_string();
    assert!(annotation.contains("requirement `R`") && annotation.contains("Stop the API."), "{annotation}");
    let spec = result(&replies, 3)["contents"]["value"].as_str().unwrap().to_string();
    assert!(spec.contains("R#ONE") && spec.contains("Stop the API."), "{spec}");
}

#[test]
fn semantic_tokens_mark_comments_strings_and_structure() {
    let text = "// a comment\nnamespace p.app\nsection \"Title\"\nThe API shall stop.\nsection \"Other\":\n    The bell shall ring.\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", text)]);
    let path = f.path().join("a.trion");
    let replies = exchange(&[open(&path, text), at(2, "textDocument/semanticTokens/full", &path, 0, 0)]);
    let data: Vec<u64> = result(&replies, 2)["data"].as_array().unwrap().iter().map(|v| v.as_u64().unwrap()).collect();
    let kinds: Vec<u64> = data.chunks(5).map(|t| t[3]).collect();
    assert_eq!(kinds[0], 6, "comment: {kinds:?}");
    assert!(kinds.contains(&4), "string: {kinds:?}");
    assert!(kinds.iter().filter(|k| **k == 0).count() >= 5, "namespace, two sections and two modals: {kinds:?}");
}

const REFINED: &str = "namespace p\n[TOP] The API shall keep each record.\n    detailed by [SAVE], [LOAD]\n[SAVE] The API shall save each record.\n[LOAD] The API shall load each record.\nprimitive record\n[LONE] The gadget shall frobnicate the widget.\n";

#[test]
fn a_refinement_line_leads_to_the_statements_it_names() {
    let f = Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\nentry = \"a.trion\"\n"), ("a.trion", &format!("package p\n{REFINED}"))]);
    let path = f.path().join("a.trion");
    let text = f.read("a.trion");
    // Line 3 (0-based) is `    detailed by [SAVE], [LOAD]`; column 25 is inside `[LOAD]`.
    let replies = exchange(&[open(&path, &text), at(1, "textDocument/hover", &path, 3, 25), at(2, "textDocument/definition", &path, 3, 17), json!({ "jsonrpc": "2.0", "id": 3, "method": "textDocument/semanticTokens/full", "params": { "textDocument": { "uri": uri(&path) } } }), json!({ "jsonrpc": "2.0", "id": 4, "method": "textDocument/completion", "params": { "textDocument": { "uri": uri(&path) }, "position": { "line": 0, "character": 0 } } })]);
    let hover = result(&replies, 1)["contents"]["value"].as_str().unwrap_or_default().to_string();
    assert!(hover.contains("LOAD") || hover.contains("load each record"), "{hover}");
    // `[SAVE]` is declared on line 4 (0-based).
    assert_eq!(result(&replies, 2)["range"]["start"]["line"], 4);
    // The refinement line holds a decorator and two identifier tokens.
    let data: Vec<u64> = result(&replies, 3)["data"].as_array().unwrap().iter().map(|v| v.as_u64().unwrap()).collect();
    let mut line = 0;
    let on_refinement: Vec<u64> = data.chunks(5).filter_map(|t| { line += t[0]; (line == 3).then_some(t[3]) }).collect();
    assert_eq!(on_refinement, [7, 9, 9], "decorator, identifier, identifier");
    let labels: Vec<String> = result(&replies, 4).as_array().unwrap().iter().map(|i| i["label"].as_str().unwrap().to_string()).collect();
    for keyword in ["detailed by", "primitive", "predicate", "compatibility", "diagram"] {
        assert!(labels.iter().any(|l| l == keyword), "{keyword}");
    }
}

#[test]
fn an_unread_part_is_marked_where_it_occurs() {
    let f = Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\nentry = \"a.trion\"\n"), ("a.trion", &format!("package p\n{REFINED}primitive checker\n[OTHER] The checker shall report\n    another record.\n"))]);
    let path = f.path().join("a.trion");
    let replies = exchange(&[open(&path, &f.read("a.trion"))]);
    let all = diagnostics_of(&replies, &path);
    // The unread word is marked where it stands, on the second line of its sentence.
    let unread: Vec<&Value> = all.iter().filter(|d| d["code"] == "UNSUPPORTED_SEMANTICS").collect();
    assert_eq!(unread.len(), 1, "{all:?}");
    assert_eq!(unread[0]["severity"], 1);
    assert_eq!(unread[0]["range"]["start"], json!({ "line": 10, "character": 4 }), "{unread:?}");
    assert_eq!(unread[0]["range"]["end"], json!({ "line": 10, "character": 11 }), "{unread:?}");
}

const RANKED: &str = "namespace p\nenvironment user\nsystem API\n[OPEN] The door shall be open.\n[ALARM] While the alarm is active, the door shall be closed.\n    overrides [OPEN]\n[S] The API should log the call.\n    weight 3\n[D] The API shall accept the request.\n    default\n";

#[test]
fn a_priority_line_leads_to_the_statements_it_overrides() {
    let f = Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\nentry = \"a.trion\"\n"), ("a.trion", &format!("package p\n{RANKED}"))]);
    let path = f.path().join("a.trion");
    let text = f.read("a.trion");
    // Line 6 (0-based) is `    overrides [OPEN]`; column 16 is inside `[OPEN]`.
    let replies = exchange(&[open(&path, &text), at(1, "textDocument/hover", &path, 6, 16), at(2, "textDocument/definition", &path, 6, 16), json!({ "jsonrpc": "2.0", "id": 3, "method": "textDocument/semanticTokens/full", "params": { "textDocument": { "uri": uri(&path) } } }), json!({ "jsonrpc": "2.0", "id": 4, "method": "textDocument/completion", "params": { "textDocument": { "uri": uri(&path) }, "position": { "line": 0, "character": 0 } } })]);
    let hover = result(&replies, 1)["contents"]["value"].as_str().unwrap_or_default().to_string();
    assert!(hover.contains("OPEN") || hover.contains("The door shall be open"), "{hover}");
    // `[OPEN]` is declared on line 4 (0-based).
    assert_eq!(result(&replies, 2)["range"]["start"]["line"], 4);
    let data: Vec<u64> = result(&replies, 3)["data"].as_array().unwrap().iter().map(|v| v.as_u64().unwrap()).collect();
    let on = |wanted: u64| {
        let mut line = 0;
        data.chunks(5).filter_map(|t| { line += t[0]; (line == wanted).then_some(t[3]) }).collect::<Vec<u64>>()
    };
    assert_eq!(on(6), [7, 9], "overrides: decorator, identifier");
    assert_eq!(on(8), [7, 5], "weight: decorator, number");
    assert_eq!(on(10), [7], "default: decorator");
    // The control declarations open with a keyword.
    assert_eq!(on(2).first(), Some(&0), "environment is a keyword: {:?}", on(2));
    assert_eq!(on(3).first(), Some(&0), "system is a keyword: {:?}", on(3));
    let labels: Vec<String> = result(&replies, 4).as_array().unwrap().iter().map(|i| i["label"].as_str().unwrap().to_string()).collect();
    for keyword in ["overrides", "default", "weight", "environment", "system"] {
        assert!(labels.iter().any(|l| l == keyword), "{keyword}");
    }
}

#[test]
fn a_conflict_of_conditions_that_hold_together_is_an_error_on_each_statement() {
    let overlap = "namespace p\n[J1] When a user sends a message, the API shall store the message.\n[J2] While the room is archived, the API shall not store the message.\n";
    let f = Fixture::raw(&[("trion.toml", "[package]\nname = \"p\"\nentry = \"a.trion\"\n"), ("a.trion", &format!("package p\n{overlap}"))]);
    let path = f.path().join("a.trion");
    let all = diagnostics_of(&exchange(&[open(&path, &f.read("a.trion"))]), &path);
    let conflict: Vec<&Value> = all.iter().filter(|d| d["code"] == "contradiction").collect();
    assert!(!conflict.is_empty(), "{all:?}");
    assert!(conflict.iter().all(|d| d["severity"] == 1), "{conflict:?}");
    assert!(conflict[0]["message"].as_str().unwrap().contains("the environment can bring that about"), "{conflict:?}");
}

#[test]
fn inferred_export_jumps_to_its_description() {
    let usage = "namespace p.app:\n    use p.catalog\n    [WRITE] The codec shall record a message.\n";
    let introduction = "namespace p.catalog:\n    The codec is a specification language.\n";
    let fixture = Fixture::raw(&[
        ("trion.toml", MANIFEST),
        ("trion.trion", "package p\ninclude \"app.trion\"\ninclude \"catalog.trion\"\n"),
        ("app.trion", usage),
        ("catalog.trion", introduction),
    ]);
    let path = fixture.path().join("app.trion");
    let replies = exchange(&[
        open(&path, usage),
        at(2, "textDocument/hover", &path, 2, 18),
        at(3, "textDocument/definition", &path, 2, 18),
    ]);
    let hover = result(&replies, 2);
    let text = hover["contents"]["value"].as_str().expect("hover reads the symbol");
    assert!(text.contains("Inferred from `catalog.trion:2`"), "{text}");
    assert!(text.contains("The codec is a specification language."), "{text}");
    let definition = result(&replies, 3);
    assert_eq!(definition["uri"], uri(&fixture.path().join("catalog.trion")));
    assert_eq!(definition["range"]["start"]["line"], 1);
}
