//! The language server of trion: diagnostics, hover, go-to-definition,
//! completion and semantic highlighting over the Language Server Protocol on
//! standard streams. The diagnostics are those of the light check of `trioc`.

#![warn(unreachable_pub)]

use std::process::ExitCode;
use trioc_cli::project::{self, Overlay, Project};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};
use trion_language::{Diagnostic, Document, Lexicon, Meta, Severity, Spec, SpecRef, VocabEntry};
use trion_verification::Analysis;

const TOKEN_TYPES: [&str; 10] = ["keyword", "namespace", "type", "variable", "string", "number", "comment", "decorator", "regexp", "function"];
const TOKEN_MODIFIERS: [&str; 1] = ["definition"];

const FRAME_WORDS: [&str; 13] = ["where", "while", "when", "if", "then", "unless", "after", "once", "upon", "before", "until", "during", "on"];
const MODAL_WORDS: [&str; 7] = ["shall", "must", "should", "may", "not", "never", "means"];
const STRUCTURE_WORDS: [&str; 11] = ["is", "are", "and", "or", "either", "both", "at", "least", "most", "exactly", "no"];
/// Words that open a structural line.
const DIRECTIVES: [&str; 55] = [
    "environment", "system", "package", "include", "namespace", "use", "section", "note", "ref", "source", "quote", "term", "predicate", "primitive", "alias", "bind", "extend", "classify", "role", "check", "example", "step", "start", "finish", "choose", "otherwise", "concept", "diagram", "compatibility", "title", "locator", "revision", "select", "kind", "path", "sha256", "retrieved", "minimum", "relation", "expect", "form", "element", "types", "expansion", "preserves", "input", "left", "right", "base", "candidate", "measure", "individuals", "scenario", "given", "at",
];
const ROLE_ITEMS: [&str; 3] = ["activate:", "form", "required"];
/// Words that annotate the statement above them or the block they open.
const ANNOTATIONS: [&str; 2] = ["cite", "unsourced"];
/// The line that names the statements that detail the statement above it.
const REFINEMENT: &str = "detailed by";

/// The line that names the statements that the statement above it wins against.
const PRIORITY: &str = "overrides";
/// The lines that rank the statement above them and name no other statement.
const RANKS: [&str; 2] = ["default", "weight"];

/// The kinds of an `example`, as its `kind` line names them.
const EXAMPLE_KINDS: [&str; 4] = ["syntax", "comparison", "consistency", "reading"];

/// The words that open a line of identifiers under a statement.
fn relation_word(line: &str) -> Option<&'static str> {
    let trimmed = line.trim_start();
    [REFINEMENT, PRIORITY].into_iter().find(|word| trimmed.strip_prefix(word).is_some_and(|rest| rest.starts_with(' ')))
}

/// `default` or `weight N` under a statement: the byte range of its word.
fn rank_word(line: &str) -> Option<(usize, usize)> {
    let trimmed = line.trim_start();
    let indent = line.len() - trimmed.len();
    if indent == 0 {
        return None;
    }
    let is_weight = trimmed.strip_prefix("weight ").is_some_and(|n| !n.is_empty() && n.trim().chars().all(|c| c.is_ascii_digit()));
    if trimmed == "default" || is_weight {
        let word = trimmed.split_whitespace().next().unwrap_or_default();
        return Some((indent, indent + word.len()));
    }
    None
}

/// The identifiers of a `detailed by [A], [B]` or `overrides [A], [B]` line,
/// as (start byte, end byte) of each bracketed name.
fn refinement_ids(line: &str) -> Option<Vec<(usize, usize)>> {
    let trimmed = line.trim_start();
    let rest = trimmed.strip_prefix(relation_word(line)?)?;
    let base = line.len() - rest.len();
    let mut found = Vec::new();
    let mut from = 0;
    while let Some(open) = rest[from..].find('[') {
        let open = from + open;
        let Some(close) = rest[open..].find(']') else { break };
        found.push((base + open, base + open + close + 1));
        from = open + close + 1;
    }
    Some(found)
}

struct State {
    project: Project,
    analysis: Analysis,
}

#[derive(Default)]
struct Server {
    overlay: Overlay,
    state: Option<State>,
    published: BTreeSet<String>,
}

fn read_message(input: &mut impl BufRead) -> io::Result<Option<Value>> {
    let mut length = None;
    loop {
        let mut line = String::new();
        if input.read_line(&mut line)? == 0 {
            return Ok(None);
        }
        let line = line.trim_end();
        if line.is_empty() {
            break;
        }
        if let Some(value) = line.strip_prefix("Content-Length:") {
            length = value.trim().parse::<usize>().ok();
        }
    }
    let length = length.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing Content-Length"))?;
    let mut body = vec![0; length];
    input.read_exact(&mut body)?;
    serde_json::from_slice(&body).map(Some).map_err(io::Error::from)
}

fn write_message(output: &mut impl Write, message: &Value) -> io::Result<()> {
    let body = message.to_string();
    write!(output, "Content-Length: {}\r\n\r\n{body}", body.len())?;
    output.flush()
}

fn uri_to_path(uri: &str) -> PathBuf {
    let raw = uri.strip_prefix("file://").unwrap_or(uri);
    let bytes = raw.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        let hex = (bytes[i] == b'%').then(|| raw.get(i + 1..i + 3).and_then(|h| u8::from_str_radix(h, 16).ok())).flatten();
        match hex {
            Some(byte) => {
                out.push(byte);
                i += 3;
            }
            None => {
                out.push(bytes[i]);
                i += 1;
            }
        }
    }
    PathBuf::from(String::from_utf8_lossy(&out).into_owned())
}

fn path_to_uri(path: &Path) -> String {
    let mut uri = String::from("file://");
    for byte in path.to_string_lossy().bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'/' | b'-' | b'_' | b'.' | b'~') {
            uri.push(byte as char);
        } else {
            uri.push_str(&format!("%{byte:02X}"));
        }
    }
    uri
}

/// A position in UTF-16 code units, as the protocol counts them.
fn utf16_len(text: &str) -> usize {
    text.encode_utf16().count()
}

/// The words of a line as (start byte, end byte), with a backtick literal as one word.
fn word_spans(line: &str) -> Vec<(usize, usize)> {
    let bytes = line.as_bytes();
    let mut spans = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i].is_ascii_whitespace() {
            i += 1;
            continue;
        }
        let start = i;
        if bytes[i] == b'`' {
            if let Some(close) = line[i + 1..].find('`') {
                i += close + 2;
            }
        }
        while i < bytes.len() && !bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        let mut end = i;
        while end > start + 1 && matches!(bytes[end - 1], b',' | b'.' | b':') {
            end -= 1;
        }
        spans.push((start, end));
    }
    spans
}

fn bare(word: &str) -> &str {
    word.strip_prefix('`').and_then(|w| w.strip_suffix('`')).unwrap_or(word)
}

fn is_number_word(word: &str) -> bool {
    let word = word.strip_prefix('-').unwrap_or(word);
    word.starts_with(|c: char| c.is_ascii_digit()) && word.chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | ',' | '%'))
}

fn in_ignore_case(list: &[&str], word: &str) -> bool {
    list.iter().any(|w| w.eq_ignore_ascii_case(word))
}

/// The longest term that spans `word_index`, as (first word, last word, entry).
fn term_at<'a>(line: &str, spans: &[(usize, usize)], word_index: usize, lex: &Lexicon, vocabulary: &'a BTreeMap<String, VocabEntry>) -> Option<(usize, usize, &'a VocabEntry)> {
    const LONGEST: usize = 6;
    let mut best: Option<(usize, usize, &VocabEntry)> = None;
    for first in word_index.saturating_sub(LONGEST - 1)..=word_index {
        for last in word_index..spans.len().min(first + LONGEST) {
            let (start, end) = (spans[first].0, spans[last].1);
            let key = lex.resolve(&lex.canon(&line[start..end]));
            if let Some(entry) = vocabulary.get(&key) {
                let wider = best.is_none_or(|(a, b, _)| last - first > b - a);
                if wider {
                    best = Some((first, last, entry));
                }
            }
        }
    }
    best
}

fn is_keyword(word: &str) -> bool {
    in_ignore_case(&FRAME_WORDS, word) || in_ignore_case(&MODAL_WORDS, word) || in_ignore_case(&STRUCTURE_WORDS, word)
}

/// The semantic tokens of one line, as (start byte, end byte, type, is definition).
fn classify_line(line: &str, lex: &Lexicon, vocabulary: &BTreeMap<String, VocabEntry>) -> Vec<(usize, usize, usize, bool)> {
    const KEYWORD: usize = 0;
    const NAMESPACE: usize = 1;
    const TERM: usize = 2;
    const VARIABLE: usize = 3;
    const STRING: usize = 4;
    const NUMBER: usize = 5;
    const COMMENT: usize = 6;
    const DECORATOR: usize = 7;
    const REGEXP: usize = 8;
    const IDENTIFIER: usize = 9;
    let trimmed = line.trim_start();
    let indent = line.len() - trimmed.len();
    if trimmed.starts_with("//") {
        return vec![(indent, line.len(), COMMENT, false)];
    }
    if let Some(ids) = refinement_ids(line) {
        let word = relation_word(line).unwrap_or(REFINEMENT);
        let mut tokens = vec![(indent, indent + word.len(), DECORATOR, false)];
        tokens.extend(ids.into_iter().map(|(start, end)| (start, end, IDENTIFIER, false)));
        return tokens;
    }
    if let Some((start, end)) = rank_word(line) {
        let mut tokens = vec![(start, end, DECORATOR, false)];
        if end < line.len() {
            tokens.push((end + 1, line.len(), NUMBER, false));
        }
        return tokens;
    }
    let first = trimmed.split_whitespace().next().unwrap_or_default();
    if in_ignore_case(&ANNOTATIONS, first) {
        let word_end = indent + first.len();
        let mut tokens = vec![(indent, word_end, DECORATOR, false)];
        if word_end < line.len() {
            let rest = line[word_end..].trim_start();
            tokens.push((line.len() - rest.len(), line.len(), STRING, false));
        }
        return tokens;
    }
    let spans = word_spans(line);
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < spans.len() {
        let (start, end) = spans[i];
        let word = &line[start..end];
        if word.starts_with('"') {
            // A string runs to its closing quote, across the words inside it.
            let close = line[start + 1..].find('"').map_or(line.len(), |c| start + 2 + c);
            tokens.push((start, close, STRING, false));
            while i < spans.len() && spans[i].0 < close {
                i += 1;
            }
            continue;
        }
        if word.starts_with("//") {
            tokens.push((start, line.len(), COMMENT, false));
            break;
        }
        if i == 0 && (in_ignore_case(&DIRECTIVES, word) || in_ignore_case(&ROLE_ITEMS, word) || ROLE_ITEMS.contains(&&line[start..(end + 1).min(line.len())])) {
            tokens.push((start, end, KEYWORD, false));
            i += 1;
            continue;
        }
        if i == 0 && word.starts_with('[') && word.ends_with(']') {
            tokens.push((start, end, IDENTIFIER, true));
            i += 1;
            continue;
        }
        if word.starts_with('/') && word.len() > 1 && word.ends_with('/') {
            tokens.push((start, end, REGEXP, false));
            i += 1;
            continue;
        }
        if let Some((first, last, entry)) = term_at(line, &spans, i, lex, vocabulary).filter(|(first, _, _)| *first == i) {
            let known = entry.defined_at.is_some() || entry.declared_at.is_some();
            tokens.push((spans[first].0, spans[last].1, TERM, known));
            i = last + 1;
            continue;
        }
        if is_keyword(word) {
            tokens.push((start, end, KEYWORD, false));
        } else if word.starts_with('$') {
            tokens.push((start, end, VARIABLE, false));
        } else if word.starts_with('`') {
            tokens.push((start, end, STRING, false));
        } else if is_number_word(word) {
            tokens.push((start, end, NUMBER, false));
        } else if let Some(split) = word.find("::") {
            tokens.push((start, start + split, NAMESPACE, false));
            tokens.push((start + split + 2, end, TERM, false));
        }
        i += 1;
    }
    tokens
}

/// What a frame keyword means, for hover.
fn keyword_doc(word: &str) -> Option<&'static str> {
    Some(match word.to_ascii_lowercase().as_str() {
        "while" => "**While**: EARS state-driven. The rule is active as long as the state holds.",
        "when" => "**When**: EARS event-driven. The rule responds to the trigger.",
        "where" => "**Where**: EARS optional feature. The rule applies where the feature is included.",
        "if" | "then" => "**If / then**: EARS unwanted behaviour. The rule states the response to an undesired situation.",
        "unless" => "**unless**: a trion extension to EARS. The rule does not apply when the exception holds.",
        "after" | "once" | "upon" | "on" => "A trion extension to EARS: a temporal opener, read as a trigger.",
        "before" => "A trion extension to EARS: the moment before the event.",
        "until" => "A trion extension to EARS: active while the condition does not yet hold.",
        "during" => "A trion extension to EARS: active during the named period, read as a state.",
        "shall" => "**shall**: an obligation.",
        "must" => "**must**: an obligation. A trion extension to EARS, which uses `shall`.",
        "should" => "**should**: a recommendation. A trion extension to EARS.",
        "may" => "**may**: a permission. A trion extension to EARS.",
        "never" => "**never**: reads as `not`.",
        "means" => "**means**: defines a term. A trion extension to EARS.",
        _ => return None,
    })
}

fn describe_entry(entry: &VocabEntry) -> String {
    let (name, namespace) = match entry.term.rsplit_once("::") {
        Some((namespace, name)) => (name, namespace),
        None => (entry.term.as_str(), ""),
    };
    let mut text = format!("**{name}**");
    if !namespace.is_empty() {
        text.push_str(&format!(" in namespace `{namespace}`"));
    }
    if let Some(kind) = &entry.declared_kind {
        text.push_str(&format!(" ({kind})"));
    } else if !entry.inferred_kinds.is_empty() {
        let kinds: Vec<&str> = entry.inferred_kinds.iter().map(String::as_str).collect();
        text.push_str(&format!(" (inferred: {})", kinds.join(", ")));
    }
    if let Some(at) = &entry.defined_at {
        text.push_str(&format!("\n\n{}\n\n`{}:{}`", at.text, at.file, at.line));
    } else if let Some(at) = &entry.declared_at {
        text.push_str(&format!("\n\nDeclared at `{}:{}`", at.file, at.line));
    } else {
        text.push_str("\n\nNot defined. The term is inferred from its use.");
    }
    text.push_str(&format!("\n\nUsed {} time(s).", entry.occurrences));
    text
}

fn source_decl<'a>(state: &'a State, name: &str) -> Option<&'a trion_language::document::SourceDecl> {
    state.project.set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.sources).find(|s| s.name == name)
}

fn describe_spec(spec: &Spec, state: &State) -> String {
    let mut text = format!("**{}**\n\nSyntax: {}", spec.display_id(), trion_language::syntax::syntax_forms(&spec.sentence).join(", "));
    for meta in &spec.meta {
        match meta {
            Meta::Cite { source, quote } => {
                let decl = source_decl(state, source);
                let kind = decl.and_then(|d| d.kind.as_deref()).unwrap_or("source");
                let text_of = quote.as_ref().and_then(|q| decl?.quotes.iter().find(|x| &x.name == q)).map(|q| q.text.as_str());
                match (quote, text_of) {
                    (Some(q), Some(body)) => text.push_str(&format!("\n\n{kind} `{source}#{q}`: {body}")),
                    (Some(q), None) => text.push_str(&format!("\n\n{kind} `{source}#{q}`")),
                    (None, _) => text.push_str(&format!("\n\n{kind} `{source}`")),
                }
            }
            Meta::Unsourced { reason } => text.push_str(&format!("\n\nNo source: {reason}")),
        }
    }
    // The reading over individuals, as the verification states it.
    if let Some(individuals) = &state.analysis.model.individuals {
        let id = spec.display_id();
        if let Some(meaning) = individuals.meanings.iter().find(|m| m.statement == id) {
            text.push_str(&format!("\n\nReading over individuals (semantic version {}, domains of {} individuals):", meaning.version, individuals.scope));
            for line in meaning.lines() {
                text.push_str(&format!("\n- {line}"));
            }
        } else if individuals.domain.iter().any(|d| d.statement == id) {
            text.push_str("\n\nReading over individuals: a statement about the domain");
        } else if let Some(outside) = individuals.outside.iter().find(|o| o.statement.id == id) {
            text.push_str(&format!("\n\nNo reading over individuals: {}", outside.why));
        }
    }
    text
}


/// The byte offset in `line` of a UTF-16 column.
fn byte_at(line: &str, character: usize) -> usize {
    let mut units = 0;
    for (byte, c) in line.char_indices() {
        if units >= character {
            return byte;
        }
        units += c.len_utf16();
    }
    line.len()
}

impl Server {
    fn document_text(&self, path: &Path) -> Option<String> {
        self.overlay.get(path).cloned().or_else(|| std::fs::read_to_string(path).ok())
    }

    /// The namespace blocks of a file, each with the first line it occupies.
    fn documents<'a>(state: &'a State, path: &Path) -> Vec<(usize, &'a Document)> {
        let Some(label) = state.project.files.iter().find(|(_, p)| p.as_path() == path).map(|(l, _)| l) else { return Vec::new() };
        let mut found: Vec<(usize, &Document)> = state
            .project
            .set
            .packages
            .iter()
            .flat_map(|p| &p.documents)
            .filter(|d| d.file == *label || d.specs.iter().any(|s| &s.file == label) || d.imports.iter().any(|i| &i.file == label) || Self::declares_in(d, label))
            .map(|d| {
                let lines = d.specs.iter().filter(|s| &s.file == label).map(|s| s.line).chain(d.imports.iter().filter(|i| &i.file == label).map(|i| i.line)).chain(d.sources.iter().filter(|s| &s.file == label).map(|s| s.line)).chain(d.aliases.iter().filter(|a| &a.file == label).map(|a| a.line));
                (lines.min().unwrap_or(usize::MAX), d)
            })
            .collect();
        found.sort_by_key(|(line, _)| *line);
        found
    }

    /// The namespace block that holds a line (0-based) of a file.
    fn document_at<'a>(state: &'a State, path: &Path, line: usize) -> Option<&'a Document> {
        let all = Self::documents(state, path);
        all.iter().rev().find(|(first, _)| *first <= line + 1).or(all.first()).map(|(_, d)| *d)
    }

    fn declares_in(doc: &Document, label: &str) -> bool {
        doc.vocabulary.iter().any(|v| v.file == label) || doc.aliases.iter().any(|a| a.file == label) || doc.bindings.iter().any(|b| b.file == label) || doc.extensions.iter().any(|e| e.file == label) || doc.classifications.iter().any(|c| c.file == label) || doc.roles.iter().any(|r| r.forms.iter().any(|f| f.file == label))
    }

    fn lexicon_for(state: &State, path: &Path, line: usize) -> Lexicon {
        match Self::document_at(state, path, line) {
            Some(doc) => state.analysis.lexicon.in_document(doc),
            None => state.analysis.lexicon.clone(),
        }
    }

    fn refresh(&mut self, path: &Path, output: &mut impl Write) -> io::Result<()> {
        let base = path.parent().unwrap_or(path);
        let target = project::find_manifest_dir(base).unwrap_or_else(|| path.to_path_buf());
        let mut published: BTreeMap<String, Vec<Value>> = BTreeMap::new();
        match project::load_with(&target, &self.overlay) {
            Ok(project) => {
                // The editor shows what `trion` and `trioc prove` report: the
                // conversion proves nothing, and a finding of the proof comes
                // from the obligations of the MMT form.
                let trion_cli::Findings { analysis, diagnostics: all } = trion_cli::findings(&project);
                // A statement that constrains nothing and a part of a sentence without a
                // formal reading are errors: nothing that passes may be unread. The mark
                // stands on the part that the diagnostic names, where it names one.
                let unread: Vec<Diagnostic> = trioc_cli::check::unread_of(&analysis);
                for diagnostic in &unread {
                    let Some(at) = diagnostic.refs.first() else { continue };
                    let Some(file) = project.files.get(&at.file).cloned() else { continue };
                    let text = self.document_text(&file).unwrap_or_default();
                    let mut error = lsp_diagnostic(diagnostic, Some(at), &text, &project);
                    error["severity"] = json!(1);
                    if let Some((line, start, end)) = named_part(&diagnostic.message, &text, at.line) {
                        error["range"] = json!({ "start": { "line": line, "character": start }, "end": { "line": line, "character": end } });
                    }
                    published.entry(path_to_uri(&file)).or_default().push(error);
                }
                for label_path in project.files.values() {
                    published.entry(path_to_uri(label_path)).or_default();
                }
                for diagnostic in &all {
                    let file = diagnostic.refs.first().and_then(|r| project.files.get(&r.file)).cloned().unwrap_or_else(|| path.to_path_buf());
                    let at = diagnostic.refs.first();
                    let text = self.document_text(&file).unwrap_or_default();
                    published.entry(path_to_uri(&file)).or_default().push(lsp_diagnostic(diagnostic, at, &text, &project));
                }
                self.state = Some(State { project, analysis });
            }
            Err(message) => {
                self.state = None;
                published.entry(path_to_uri(path)).or_default().push(json!({ "range": { "start": { "line": 0, "character": 0 }, "end": { "line": 0, "character": 1 } }, "severity": 1, "source": "trion", "message": message }));
            }
        }
        let stale: Vec<String> = self.published.iter().filter(|uri| !published.contains_key(*uri)).cloned().collect();
        for uri in stale {
            published.entry(uri).or_default();
        }
        self.published = published.keys().cloned().collect();
        for (uri, diagnostics) in published {
            write_message(output, &json!({ "jsonrpc": "2.0", "method": "textDocument/publishDiagnostics", "params": { "uri": uri, "diagnostics": diagnostics } }))?;
        }
        Ok(())
    }

    fn hover(&self, path: &Path, line_no: usize, character: usize) -> Value {
        let (Some(state), Some(text)) = (&self.state, self.document_text(path)) else { return Value::Null };
        let Some(line) = text.lines().nth(line_no) else { return Value::Null };
        let spans = word_spans(line);
        let byte = byte_at(line, character);
        let Some(index) = spans.iter().position(|&(s, e)| byte >= s && byte < e) else { return Value::Null };
        let word = bare(&line[spans[index].0..spans[index].1]);
        let doc = Self::document_at(state, path, line_no);
        let in_spec_line = |spec: &&Spec| spec.line == line_no + 1;
        let detail = refinement_ids(line).and_then(|ids| ids.into_iter().find(|&(s, e)| byte >= s && byte < e)).map(|(s, e)| line[s + 1..e - 1].to_string());
        let contents = if let Some(id) = detail {
            Self::statement(state, &id).map(|s| describe_spec(s, state))
        } else if word.starts_with('[') {
            doc.and_then(|d| d.specs.iter().find(in_spec_line)).map(|s| describe_spec(s, state))
        } else if index == 0 && in_ignore_case(&ANNOTATIONS, word) {
            let cited = line.split_whitespace().nth(1).unwrap_or("");
            let (name, quote) = cited.split_once('#').unwrap_or((cited, ""));
            let found = source_decl(state, name);
            Some(found.map_or(format!("Annotation `{word}`"), |s| {
                let mut text = format!("{} `{}`", s.kind.as_deref().unwrap_or("source"), s.name);
                for field in [&s.title, &s.path, &s.locator].into_iter().flatten() {
                    text.push_str(&format!("\n\n{field}"));
                }
                if let Some(q) = s.quotes.iter().find(|q| q.name == quote) {
                    text.push_str(&format!("\n\n> {}", q.text));
                }
                text
            }))
        } else {
            let lex = Self::lexicon_for(state, path, line_no);
            term_at(line, &spans, index, &lex, &state.analysis.vocabulary).map(|(_, _, e)| describe_entry(e)).or_else(|| keyword_doc(word).map(str::to_string)).or_else(|| {
                let sentence = doc.and_then(|d| d.specs.iter().find(in_spec_line))?;
                Some(format!("Syntax: {}", trion_language::syntax::syntax_forms(&sentence.sentence).join(", ")))
            })
        };
        contents.map_or(Value::Null, |value| json!({ "contents": { "kind": "markdown", "value": value } }))
    }

    /// The statement of the root package with this identifier, or the statement that holds it as an item.
    fn statement<'a>(state: &'a State, id: &str) -> Option<&'a Spec> {
        state.project.root_specs().find(|s| s.id.as_deref() == Some(id) || s.parts.iter().any(|p| p == id))
    }

    fn location_of(&self, state: &State, at: &SpecRef) -> Value {
        let Some(path) = state.project.files.get(&at.file) else { return Value::Null };
        let line = at.line.saturating_sub(1);
        let text = self.document_text(path).unwrap_or_default();
        let length = text.lines().nth(line).map_or(0, utf16_len);
        json!({ "uri": path_to_uri(path), "range": { "start": { "line": line, "character": 0 }, "end": { "line": line, "character": length } } })
    }

    fn definition(&self, path: &Path, line_no: usize, character: usize) -> Value {
        let (Some(state), Some(text)) = (&self.state, self.document_text(path)) else { return Value::Null };
        let Some(line) = text.lines().nth(line_no) else { return Value::Null };
        let spans = word_spans(line);
        let byte = byte_at(line, character);
        let Some(index) = spans.iter().position(|&(s, e)| byte >= s && byte < e) else { return Value::Null };
        // An identifier in `detailed by [A], [B]` or in `ref [A]` leads to its statement.
        let named = refinement_ids(line)
            .and_then(|ids| ids.into_iter().find(|&(s, e)| byte >= s && byte < e))
            .map(|(s, e)| line[s + 1..e - 1].to_string())
            .or_else(|| line.trim_start().strip_prefix("ref [").and_then(|r| r.strip_suffix(']')).map(str::to_string));
        if let Some(id) = named {
            return Self::statement(state, &id).map_or(Value::Null, |s| self.location_of(state, &SpecRef { id: s.display_id(), file: s.file.clone(), line: s.line, text: String::new() }));
        }
        if line.trim_start().starts_with("use ") && index == 1 {
            let name = &line[spans[index].0..spans[index].1];
            let target = Self::document_at(state, path, line_no).and_then(|d| d.imports.iter().find(|i| i.name == name)).map(|i| i.namespace.clone());
            let doc = target.and_then(|ns| state.project.set.packages.iter().flat_map(|p| &p.documents).find(|d| d.namespace == ns));
            let spec = doc.and_then(|d| d.specs.first());
            return spec.map_or(Value::Null, |s| self.location_of(state, &SpecRef { id: s.display_id(), file: s.file.clone(), line: s.line, text: String::new() }));
        }
        let lex = Self::lexicon_for(state, path, line_no);
        term_at(line, &spans, index, &lex, &state.analysis.vocabulary).and_then(|(_, _, e)| e.defined_at.as_ref().or(e.declared_at.as_ref()).or(e.first_use.as_ref())).map_or(Value::Null, |at| self.location_of(state, at))
    }

    fn completion(&self) -> Value {
        let mut items: Vec<Value> = Vec::new();
        for word in DIRECTIVES.iter().chain(&ANNOTATIONS).chain(&[REFINEMENT, PRIORITY]).chain(&RANKS).chain(&MODAL_WORDS).chain(&FRAME_WORDS) {
            items.push(json!({ "label": word, "kind": 14 }));
        }
        for kind in EXAMPLE_KINDS {
            items.push(json!({ "label": kind, "kind": 12, "detail": "example kind" }));
        }
        if let Some(state) = &self.state {
            for entry in state.analysis.vocabulary.values() {
                if entry.inferred_kinds.contains("action") && entry.inferred_kinds.len() == 1 {
                    continue;
                }
                items.push(json!({ "label": entry.term, "kind": 6, "detail": entry.declared_kind.clone().unwrap_or_else(|| "inferred".to_string()), "documentation": { "kind": "markdown", "value": describe_entry(entry) } }));
            }
        }
        json!(items)
    }

    fn semantic_tokens(&self, path: &Path) -> Value {
        let Some(text) = self.document_text(path) else { return json!({ "data": [] }) };
        let empty = BTreeMap::new();
        // Each namespace block of the file reads with its own lexicon.
        let blocks: Vec<(usize, Lexicon)> = match &self.state {
            Some(state) => Self::documents(state, path).into_iter().map(|(first, d)| (first, state.analysis.lexicon.in_document(d))).collect(),
            None => Vec::new(),
        };
        let vocabulary = self.state.as_ref().map_or(&empty, |s| &s.analysis.vocabulary);
        let fallback = self.state.as_ref().map_or_else(Lexicon::default, |s| s.analysis.lexicon.clone());
        let (mut data, mut last_line, mut last_start) = (Vec::new(), 0, 0);
        for (line_no, line) in text.lines().enumerate() {
            let lex = blocks.iter().rev().find(|(first, _)| *first <= line_no + 1).or(blocks.first()).map_or(&fallback, |(_, l)| l);
            for (start, end, kind, definition) in classify_line(line, lex, vocabulary) {
                let column = utf16_len(&line[..start]);
                let delta_line = line_no - last_line;
                let delta_start = if delta_line == 0 { column - last_start } else { column };
                data.extend([delta_line, delta_start, utf16_len(&line[start..end]), kind, usize::from(definition)]);
                last_line = line_no;
                last_start = column;
            }
        }
        json!({ "data": data })
    }
}

/// The place of the part that a diagnostic names: its message begins with the part in
/// backticks, and the part is sought as whole words from the first line of the statement
/// to the end of its sentence. The result is a 0-based line and UTF-16 columns.
fn named_part(message: &str, text: &str, line: usize) -> Option<(usize, usize, usize)> {
    let part = message.strip_prefix('`')?.split('`').next().filter(|p| !p.is_empty())?;
    let word = |c: char| c.is_alphanumeric() || c == '-' || c == '_';
    for (index, content) in text.lines().enumerate().skip(line.saturating_sub(1)).take(12) {
        let mut from = 0;
        while let Some(found) = content[from..].find(part) {
            let start = from + found;
            let end = start + part.len();
            let before = content[..start].chars().next_back().is_some_and(word);
            let after = content[end..].chars().next().is_some_and(word);
            if !before && !after {
                return Some((index, utf16_len(&content[..start]), utf16_len(&content[..end])));
            }
            from = end;
        }
        if index + 1 > line.saturating_sub(1) && content.trim_end().ends_with('.') {
            break;
        }
    }
    None
}

fn lsp_diagnostic(diagnostic: &Diagnostic, at: Option<&SpecRef>, text: &str, project: &Project) -> Value {
    let line = at.map_or(0, |r| r.line.saturating_sub(1));
    let length = text.lines().nth(line).map_or(1, |l| utf16_len(l).max(1));
    let severity = match diagnostic.severity {
        Severity::Error => 1,
        Severity::Warning => 2,
        Severity::Info => 3,
    };
    let related: Vec<Value> = diagnostic
        .refs
        .iter()
        .skip(1)
        .filter_map(|r| {
            let path = project.files.get(&r.file)?;
            let line = r.line.saturating_sub(1);
            Some(json!({ "location": { "uri": path_to_uri(path), "range": { "start": { "line": line, "character": 0 }, "end": { "line": line, "character": 1 } } }, "message": r.text }))
        })
        .collect();
    json!({ "range": { "start": { "line": line, "character": 0 }, "end": { "line": line, "character": length } }, "severity": severity, "code": diagnostic.code, "source": "trion", "message": diagnostic.message, "relatedInformation": related })
}

fn capabilities() -> Value {
    json!({
        "capabilities": {
            "textDocumentSync": { "openClose": true, "change": 1, "save": true },
            "hoverProvider": true,
            "definitionProvider": true,
            "completionProvider": {},
            "semanticTokensProvider": { "legend": { "tokenTypes": TOKEN_TYPES, "tokenModifiers": TOKEN_MODIFIERS }, "full": true }
        },
        "serverInfo": { "name": "trion", "version": env!("CARGO_PKG_VERSION") }
    })
}

/// Serves until the client sends `exit` or closes the stream.
pub fn serve(input: &mut impl BufRead, output: &mut impl Write) -> io::Result<()> {
    let mut server = Server::default();
    while let Some(message) = read_message(input)? {
        let method = message.get("method").and_then(Value::as_str).unwrap_or("").to_string();
        let params = message.get("params").cloned().unwrap_or(Value::Null);
        let path = params.pointer("/textDocument/uri").and_then(Value::as_str).map(uri_to_path).map(|p| p.canonicalize().unwrap_or(p));
        let position = || (params.pointer("/position/line").and_then(Value::as_u64).unwrap_or(0) as usize, params.pointer("/position/character").and_then(Value::as_u64).unwrap_or(0) as usize);
        let result = match (method.as_str(), &path) {
            ("exit", _) => return Ok(()),
            ("textDocument/didOpen", Some(path)) => {
                server.overlay.insert(path.clone(), params.pointer("/textDocument/text").and_then(Value::as_str).unwrap_or("").to_string());
                server.refresh(path, output)?;
                continue;
            }
            ("textDocument/didChange", Some(path)) => {
                let text = params.pointer("/contentChanges/0/text").and_then(Value::as_str).unwrap_or("").to_string();
                server.overlay.insert(path.clone(), text);
                server.refresh(path, output)?;
                continue;
            }
            ("textDocument/didSave", Some(path)) => {
                server.refresh(path, output)?;
                continue;
            }
            ("textDocument/didClose", Some(path)) => {
                server.overlay.remove(path);
                continue;
            }
            ("initialize", _) => capabilities(),
            ("shutdown", _) => Value::Null,
            ("textDocument/hover", Some(path)) => {
                let (line, character) = position();
                server.hover(path, line, character)
            }
            ("textDocument/definition", Some(path)) => {
                let (line, character) = position();
                server.definition(path, line, character)
            }
            ("textDocument/completion", _) => server.completion(),
            ("textDocument/semanticTokens/full", Some(path)) => server.semantic_tokens(path),
            (_, _) => {
                if let Some(id) = message.get("id") {
                    write_message(output, &json!({ "jsonrpc": "2.0", "id": id, "error": { "code": -32601, "message": format!("method not found: {method}") } }))?;
                }
                continue;
            }
        };
        if let Some(id) = message.get("id") {
            write_message(output, &json!({ "jsonrpc": "2.0", "id": id, "result": result }))?;
        }
    }
    Ok(())
}

/// Serves on standard input and output until the client leaves.
pub fn run() -> ExitCode {
    let stdin = io::stdin();
    let stdout = io::stdout();
    match serve(&mut stdin.lock(), &mut stdout.lock()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: language server failed: {e}");
            ExitCode::from(2)
        }
    }
}

