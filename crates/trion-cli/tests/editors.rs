mod common;
use common::*;
use serde_json::Value;
use std::fs;

fn editor_text(path: &str) -> String {
    fs::read_to_string(repo_root().join("editors").join(path)).unwrap()
}

fn editor_json(path: &str) -> Value {
    serde_json::from_str(&editor_text(path)).unwrap()
}

#[test]
fn the_vscode_extension_starts_the_language_server() {
    let manifest = editor_json("vscode/package.json");
    let language = &manifest["contributes"]["languages"][0];
    assert_eq!(language["id"], "trion");
    assert_eq!(language["extensions"][0], ".trion");
    // The server is the `trion-lsp` command, which takes no argument.
    let extension = editor_text("vscode/src/extension.ts");
    assert!(extension.contains("'trion-lsp'") && extension.contains("args: [],"), "{extension}");
}

#[test]
fn the_vscode_extension_uses_the_shared_grammar() {
    let manifest = editor_json("vscode/package.json");
    let grammar = &manifest["contributes"]["grammars"][0];
    assert_eq!(grammar["language"], "trion");
    assert_eq!(grammar["scopeName"], editor_json("grammar/trion.tmLanguage.json")["scopeName"]);
    assert!(editor_text("vscode/scripts/copy-grammar.mjs").contains("grammar"));
}

#[test]
fn the_intellij_plugin_starts_the_language_server() {
    let plugin = editor_text("intellij/src/main/resources/META-INF/plugin.xml");
    assert!(plugin.contains("extensions=\"trion\""));
    // The server is wired in where the LSP4IJ plugin is installed.
    assert!(plugin.contains("config-file=\"trion-lsp.xml\">com.redhat.devtools.lsp4ij"));
    assert!(editor_text("intellij/src/main/resources/META-INF/trion-lsp.xml").contains("languageId=\"trion\""));
    assert!(editor_text("intellij/src/main/kotlin/dev/trion/intellij/TrionLanguageServerFactory.kt").contains("\"trion-lsp\""));
}

#[test]
fn the_grammar_names_the_language_constructs() {
    let grammar = editor_text("grammar/trion.tmLanguage.json");
    for word in ["shall", "while", "extend", "classify", "namespace", "include", "use", "section", "source", "quote", "cite", "unsourced", "ratified", "check", "example", "trace", "::"] {
        assert!(grammar.contains(word), "{word}");
    }
}
