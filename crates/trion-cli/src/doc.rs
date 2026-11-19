//! `trion doc`: a verified package as one self-contained HTML document.
//!
//! The view follows the source text, so that it reads in the order and the
//! paragraphs its author chose. Each statement carries what the verification
//! knows about it: its resolved terms, its warnings and its sources. A
//! diagram is drawn as a figure beside the controlled English it stands for.

use crate::project::Project;
use crate::convert::Converted;
use crate::figure;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use trion_language::document::{Table, TableCell};
use trion_language::{expand, glossary, occurrences, Diagnostic, Document, GlossaryEntry, Meta, Severity, Spec};
use trion_verification::Analysis;

pub(crate) fn esc(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            other => out.push(other),
        }
    }
    out
}

fn slug(text: &str) -> String {
    let mut out = String::new();
    for c in text.chars() {
        if c.is_ascii_alphanumeric() {
            out.push(c.to_ascii_lowercase());
        } else if !out.ends_with('-') {
            out.push('-');
        }
    }
    out.trim_matches('-').to_string()
}

/// A source line. A multiline string stays with the line that opens it.
struct Line {
    no: usize,
    indent: usize,
    text: String,
    raw: String,
    blank: bool,
}

fn lines_of(src: &str) -> Vec<Line> {
    let mut out: Vec<Line> = Vec::new();
    let mut in_string = false;
    for (index, raw) in src.lines().enumerate() {
        let odd = raw.matches("\"\"\"").count() % 2 == 1;
        if in_string {
            if let Some(last) = out.last_mut() {
                last.raw.push('\n');
                last.raw.push_str(raw);
                last.text.push('\n');
                last.text.push_str(raw);
            }
            in_string ^= odd;
            continue;
        }
        let text = raw.trim();
        out.push(Line { no: index + 1, indent: raw.chars().take_while(|c| c.is_whitespace()).count(), text: text.to_string(), raw: raw.to_string(), blank: text.is_empty() });
        in_string = odd;
    }
    out
}

#[derive(PartialEq)]
enum Kind {
    Comment,
    Package,
    Include,
    Namespace,
    Section,
    Table,
    Meta,
    Note,
    Ref,
    DeclBlock,
    Decl,
    Statement,
}

fn kind_of(text: &str) -> Kind {
    let word = |kw: &str| text.strip_prefix(kw).is_some_and(|rest| rest.starts_with(' '));
    let sentence = text.ends_with('.');
    if text.starts_with("//") {
        Kind::Comment
    } else if word("package") && text.contains(" edition ") {
        Kind::Package
    } else if text.starts_with("include \"") {
        Kind::Include
    } else if word("namespace") && !sentence && !text["namespace ".len()..].trim_end_matches(':').contains(' ') {
        Kind::Namespace
    } else if text.starts_with("section \"") && (text.ends_with('"') || text.ends_with("\":")) {
        Kind::Section
    } else if text.starts_with("table \"") {
        Kind::Table
    } else if (word("use") && !sentence && !text[4..].contains(' ')) || word("cite") || text.starts_with("unsourced \"") || text.starts_with("detailed by [") || text.starts_with("overrides [") || text == "default" || text.strip_prefix("weight ").is_some_and(|n| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit())) {
        Kind::Meta
    } else if text.starts_with("note \"") {
        Kind::Note
    } else if text.starts_with("ref [") {
        Kind::Ref
    } else if ["source", "check", "example", "role"].iter().any(|kw| word(kw) && text.ends_with(':') && !text[kw.len() + 1..text.len() - 1].trim().contains(' ')) {
        Kind::DeclBlock
    } else if ["term", "alias", "bind", "extend", "classify", "predicate", "primitive", "environment", "system"].iter().any(|kw| word(kw)) && !sentence && !text.ends_with(':') {
        Kind::Decl
    } else {
        Kind::Statement
    }
}

/// The byte ranges of the sentences of a paragraph, as the parser splits them.
fn sentence_spans(text: &str) -> Vec<(usize, usize)> {
    let mut spans = Vec::new();
    let (mut in_string, mut in_literal, mut escaped) = (false, false, false);
    let mut start = 0;
    let mut chars = text.char_indices().peekable();
    while let Some((at, c)) = chars.next() {
        if in_string {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_string = false;
            }
            continue;
        }
        if in_literal {
            in_literal = c != '`';
            continue;
        }
        match c {
            '"' => in_string = true,
            '`' => in_literal = text[at + 1..].contains('`'),
            '.' if chars.peek().is_none_or(|(_, next)| next.is_whitespace()) => {
                spans.push((start, at + 1));
                start = at + 1;
            }
            _ => {}
        }
    }
    if !text[start..].trim().is_empty() {
        spans.push((start, text.len()));
    }
    spans.into_iter().map(|(from, to)| (from + text[from..to].len() - text[from..to].trim_start().len(), to)).collect()
}

/// Splits a leading `[ID]` from a statement.
fn take_label(text: &str) -> (Option<&str>, &str) {
    match text.strip_prefix('[').and_then(|rest| rest.split_once(']')) {
        Some((id, rest)) if !id.is_empty() && !id.contains(' ') => (Some(id), rest.trim_start()),
        _ => (None, text),
    }
}

/// What the whole view shares.
struct Shared<'a> {
    project: &'a Project,
    analysis: &'a Analysis,
    /// The examples that demonstrate the conversion, with what each observed.
    demonstrated: &'a [trion_verification::ExampleOutcome],
    diagnostics: Vec<Diagnostic>,
    /// The diagnostics that name a place, by file and line.
    placed: BTreeMap<(String, usize), Vec<usize>>,
    shown: RefCell<BTreeSet<usize>>,
    glossary: BTreeMap<String, GlossaryEntry>,
    /// The anchor of the statement at `file:line`.
    anchors: BTreeMap<String, String>,
    used_terms: RefCell<BTreeSet<String>>,
    figures: Cell<usize>,
    /// The statements that each statement details, by the identifier of the detail.
    details_of: BTreeMap<String, Vec<String>>,
}

fn anchor_of(spec: &Spec) -> String {
    match &spec.id {
        Some(id) => id.clone(),
        None if spec.shares_line => format!("s-{}-{}-{}", slug(&spec.file), spec.line, spec.column),
        None => format!("s-{}-{}", slug(&spec.file), spec.line),
    }
}

impl Shared<'_> {
    fn quote_of(&self, source: &str, quote: Option<&str>) -> String {
        let declaration = self.project.set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.sources).find(|d| d.name == source);
        let Some(declaration) = declaration else { return String::new() };
        match quote.and_then(|q| declaration.quotes.iter().find(|x| x.name == q)) {
            Some(found) => found.text.trim().to_string(),
            None => declaration.title.clone().unwrap_or_default(),
        }
    }

    fn badges(&self, file: &str, line: usize) -> String {
        let mut out = String::new();
        for &index in self.placed.get(&(file.to_string(), line)).into_iter().flatten() {
            let diagnostic = &self.diagnostics[index];
            self.shown.borrow_mut().insert(index);
            let class = if diagnostic.severity == Severity::Warning { "warn" } else { "info" };
            out.push_str(&format!(" <span class=\"badge {class}\" title=\"{}\">{}</span>", esc(&diagnostic.message), esc(&diagnostic.code)));
        }
        out
    }

    /// The marks after a statement: where it comes from and how it relates to other statements.
    fn marks(&self, spec: &Spec) -> String {
        let mut out = String::new();
        let mut cited = Vec::new();
        for meta in &spec.meta {
            match meta {
                Meta::Cite { source, quote } => {
                    let target = quote.as_ref().map_or(source.clone(), |q| format!("{source}#{q}"));
                    cited.push(format!("{target}: {}", self.quote_of(source, quote.as_deref())));
                }
                Meta::Unsourced { reason } => out.push_str(&format!(" <span class=\"mark unsourced\" title=\"{}\">unsourced</span>", esc(reason))),
            }
        }
        // A refinement is shown from both sides.
        let link = |id: &String| format!("<a href=\"#{}\">{}</a>", esc(id), esc(id));
        if !spec.details.is_empty() {
            out.push_str(&format!(" <span class=\"mark refine\">detailed by {}</span>", spec.details.iter().map(link).collect::<Vec<_>>().join(", ")));
        }
        if let Some(abstracts) = spec.id.as_ref().and_then(|id| self.details_of.get(id)) {
            out.push_str(&format!(" <span class=\"mark refine\">details {}</span>", abstracts.iter().map(link).collect::<Vec<_>>().join(", ")));
        }
        // A priority is shown from both sides, with the condition under which it applies.
        if let Some(id) = &spec.id {
            let priorities = &self.analysis.model.priorities;
            let place = |condition: &str| if condition == "⊤" { String::new() } else { format!(" where {condition}") };
            for priority in priorities.iter().filter(|p| &p.to.id == id) {
                out.push_str(&format!(" <span class=\"mark priority\" title=\"{}\">overrides {}</span>", esc(&format!("{} does not apply{}", priority.yields.id, place(&priority.condition))), link(&priority.yields.id)));
            }
            for priority in priorities.iter().filter(|p| &p.yields.id == id) {
                let word = if priority.kind == "default" { "yields as a default to" } else { "overridden by" };
                out.push_str(&format!(" <span class=\"mark priority\" title=\"{}\">{word} {}</span>", esc(&format!("this statement does not apply{}", place(&priority.condition))), link(&priority.to.id)));
            }
        }
        if spec.default {
            out.push_str(" <span class=\"mark priority\" title=\"yields to each more specific statement that contradicts it\">default</span>");
        }
        if let Some(weight) = spec.weight {
            out.push_str(&format!(" <span class=\"mark priority\" title=\"the weight of this recommendation when recommendations cannot all be kept\">weight {weight}</span>"));
        }
        if !cited.is_empty() {
            out.push_str(&format!(" <span class=\"mark cite\" title=\"{}\">&#167;{}</span>", esc(&cited.join("\n\n")), cited.len()));
        }
        out
    }

    /// The text of a statement with each resolved term linked to its definition.
    fn linked(&self, text: &str, keys: &[String]) -> String {
        let lower = text.to_ascii_lowercase();
        // Quoted strings and literals are data.
        let mut data = vec![false; text.len()];
        let mut open: Option<char> = None;
        for (at, c) in text.char_indices() {
            match open {
                Some(q) => {
                    data[at] = true;
                    if c == q {
                        open = None;
                    }
                }
                None if c == '"' || c == '`' => {
                    data[at] = true;
                    open = Some(c);
                }
                None => {}
            }
        }
        let mut candidates: Vec<(&String, String)> = keys
            .iter()
            .filter_map(|key| {
                let entry = self.glossary.get(key)?;
                let local = key.rsplit("::").next().unwrap_or(key).to_ascii_lowercase();
                (entry.definition.is_some() || entry.declared_at.is_some() || entry.occurrences > 1).then_some((key, local))
            })
            .collect();
        candidates.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then(a.0.cmp(b.0)));
        let boundary = |at: usize| at == 0 || at >= lower.len() || !lower.as_bytes()[at].is_ascii_alphanumeric() || !lower.as_bytes()[at - 1].is_ascii_alphanumeric();
        let mut taken: Vec<(usize, usize, &String)> = Vec::new();
        for (key, local) in &candidates {
            if local.is_empty() {
                continue;
            }
            let mut from = 0;
            while let Some(found) = lower[from..].find(local.as_str()) {
                let start = from + found;
                let mut end = start + local.len();
                from = end;
                // A plural names the same term.
                for suffix in ["es", "s"] {
                    if lower[end..].starts_with(suffix) && boundary(end + suffix.len()) {
                        end += suffix.len();
                        break;
                    }
                }
                if !boundary(start) || !boundary(end) || data[start] || taken.iter().any(|(a, b, _)| start < *b && *a < end) {
                    continue;
                }
                taken.push((start, end, key));
            }
        }
        taken.sort();
        let mut out = String::new();
        let mut at = 0;
        for (start, end, key) in taken {
            let entry = &self.glossary[key];
            self.used_terms.borrow_mut().insert(key.clone());
            let (class, title) = match (&entry.definition, &entry.declared_at) {
                (Some(definition), _) => ("defined", definition.clone()),
                (None, Some(place)) => ("defined", format!("declared at {place}")),
                _ => ("derived", format!("derived term ({}); first used at {}", entry.kinds.join(", "), entry.first_use.as_deref().unwrap_or("an unknown place"))),
            };
            let definition = entry.defined_at.as_ref().and_then(|place| self.anchors.get(place));
            let href = definition.cloned().unwrap_or_else(|| format!("g-{}", slug(key)));
            out.push_str(&esc(&text[at..start]));
            out.push_str(&format!("<a class=\"term {class}\" href=\"#{}\" title=\"{}\">{}</a>", esc(&href), esc(&title), esc(&text[start..end])));
            at = end;
        }
        out.push_str(&esc(&text[at..]));
        out
    }
}

/// The view of one file.
struct FileView<'a> {
    shared: &'a Shared<'a>,
    file: &'a str,
    lines: Vec<Line>,
    specs: BTreeMap<usize, VecDeque<(&'a Document, &'a Spec)>>,
    tables: BTreeMap<usize, &'a Table>,
    out: String,
    /// The headings: level, anchor and title.
    toc: Vec<(usize, String, String)>,
    headings: BTreeMap<String, usize>,
}

impl<'a> FileView<'a> {
    fn dedent(&self, header: usize, end: usize) -> usize {
        let indent = self.lines[header].indent;
        (header + 1..end).find(|&j| !self.lines[j].blank && self.lines[j].indent <= indent).unwrap_or(end)
    }

    /// The end of the body that begins at `from`, under a header whose first line is `header`.
    fn body_end(&self, header: usize, from: usize, end: usize) -> usize {
        let indent = self.lines[header].indent;
        (from..end).find(|&j| !self.lines[j].blank && self.lines[j].indent <= indent).unwrap_or(end)
    }

    /// The end of a flat block: the next header of its kind at its indentation.
    fn flat_end(&self, header: usize, end: usize, kind: Kind) -> usize {
        let indent = self.lines[header].indent;
        (header + 1..end).find(|&j| !self.lines[j].blank && (self.lines[j].indent < indent || (self.lines[j].indent == indent && kind_of(&self.lines[j].text) == kind))).unwrap_or(end)
    }

    fn take_spec(&mut self, line: usize) -> Option<(&'a Document, &'a Spec)> {
        self.specs.get_mut(&line)?.pop_front()
    }

    fn heading_anchor(&mut self, title: &str) -> String {
        let base = format!("sec-{}-{}", slug(self.file), slug(title));
        let count = self.headings.entry(base.clone()).or_insert(0);
        *count += 1;
        if *count == 1 { base } else { format!("{base}-{count}") }
    }

    /// One statement: its identifier, its text and what is known about it.
    fn statement(&mut self, label: Option<&str>, text: &str, line: usize, tag: &str) -> String {
        let found = self.take_spec(line);
        let anchor = match (found, label) {
            (Some((_, spec)), _) => anchor_of(spec),
            (None, Some(id)) => id.to_string(),
            (None, None) => format!("s-{}-{line}", slug(self.file)),
        };
        let keys: Vec<String> = match found {
            Some((document, spec)) => {
                let lexicon = self.shared.analysis.lexicon.in_document(document);
                let mut keys: Vec<String> = occurrences(&spec.sentence, &lexicon).into_iter().map(|(key, _)| key).collect();
                keys.sort();
                keys.dedup();
                keys
            }
            None => Vec::new(),
        };
        let mut out = format!("<{tag} class=\"st\" id=\"{}\" data-file=\"{}\" data-line=\"{line}\">", esc(&anchor), esc(self.file));
        if let Some(id) = label {
            out.push_str(&format!("<a class=\"id\" href=\"#{}\">{}</a> ", esc(&anchor), esc(id)));
        }
        out.push_str(&self.shared.linked(text, &keys));
        if let Some((_, spec)) = found {
            out.push_str(&self.shared.marks(spec));
        }
        out.push_str(&self.shared.badges(self.file, line));
        out.push_str(&format!("</{tag}>"));
        out
    }

    fn table(&mut self, table: &Table) {
        self.out.push_str(&format!("<table data-file=\"{}\" data-line=\"{}\"><caption>{}</caption>\n<thead><tr>", esc(self.file), table.line, esc(&table.title)));
        for heading in &table.headings {
            self.out.push_str(&format!("<th scope=\"col\">{}</th>", esc(heading)));
        }
        self.out.push_str("</tr></thead>\n<tbody>\n");
        for row in &table.rows {
            let parent = row.identifier().filter(|id| {
                self.specs.get(&row.line).and_then(|specs| specs.front())
                    .is_some_and(|(_, first)| first.id.as_deref() != Some(id))
            });
            let anchor = parent.map_or_else(String::new, |id| format!(" id=\"{}\"", esc(id)));
            self.out.push_str(&format!("<tr{anchor} data-line=\"{}\">", row.line));
            for cell in &row.cells {
                let body = match cell {
                    TableCell::Text(text) => esc(text),
                    TableCell::Identifier(id) => format!("<a class=\"id\" href=\"#{0}\">{0}</a>", esc(id)),
                    TableCell::Statement(text) => self.statement(None, text, row.line, "span"),
                    TableCell::References(ids) => ids.iter()
                        .map(|id| format!("<a class=\"id\" href=\"#{0}\">{0}</a>", esc(id)))
                        .collect::<Vec<_>>().join(", "),
                };
                self.out.push_str(&format!("<td>{body}</td>"));
            }
            self.out.push_str("</tr>\n");
        }
        self.out.push_str("</tbody></table>\n");
    }

    fn raw_block(&self, from: usize, to: usize) -> String {
        let base = (from..to).filter(|&j| !self.lines[j].blank).map(|j| self.lines[j].indent).min().unwrap_or(0);
        let text: Vec<String> = (from..to)
            .map(|j| {
                let line = &self.lines[j];
                let mut first = true;
                line.raw
                    .split('\n')
                    .map(|part| {
                        let cut = if first { base.min(part.len() - part.trim_start().len()) } else { 0 };
                        first = false;
                        part.chars().skip(cut).collect::<String>()
                    })
                    .collect::<Vec<_>>()
                    .join("\n")
            })
            .collect();
        esc(text.join("\n").trim_end())
    }

    fn block(&mut self, mut i: usize, end: usize, depth: usize) {
        while i < end {
            if self.lines[i].blank {
                i += 1;
                continue;
            }
            let text = self.lines[i].text.clone();
            let no = self.lines[i].no;
            match kind_of(&text) {
                Kind::Package | Kind::Include => i += 1,
                Kind::Comment => {
                    self.out.push_str(&format!("<p class=\"comment\">{}</p>\n", esc(text.trim_start_matches('/').trim())));
                    i += 1;
                }
                Kind::Namespace => {
                    let name = text["namespace ".len()..].trim_end_matches(':').trim().to_string();
                    let body_end = if text.ends_with(':') { self.dedent(i, end) } else { self.flat_end(i, end, Kind::Namespace) };
                    self.out.push_str(&format!("<section class=\"ns\" data-file=\"{}\" data-line=\"{no}\"><div class=\"nsname\">namespace <code>{}</code></div>\n", esc(self.file), esc(&name)));
                    self.block(i + 1, body_end, depth);
                    self.out.push_str("</section>\n");
                    i = body_end;
                }
                Kind::Section => {
                    let colon = text.ends_with(':');
                    let title = text["section \"".len()..].trim_end_matches(':').trim_end_matches('"').replace("\\\"", "\"");
                    let body_end = if colon { self.dedent(i, end) } else { self.flat_end(i, end, Kind::Section) };
                    let anchor = self.heading_anchor(&title);
                    let level = depth.min(6);
                    self.toc.push((depth, anchor.clone(), title.clone()));
                    self.out.push_str(&format!("<section class=\"sec\"><h{level} id=\"{anchor}\" data-file=\"{}\" data-line=\"{no}\">{}</h{level}>\n", esc(self.file), esc(&title)));
                    self.block(i + 1, body_end, depth + 1);
                    self.out.push_str("</section>\n");
                    i = body_end;
                }
                Kind::Table => {
                    if let Some(table) = self.tables.get(&no).copied() {
                        self.table(table);
                    }
                    i = self.dedent(i, end);
                }
                Kind::Meta => {
                    let (word, rest) = text.split_once(' ').unwrap_or((&text, ""));
                    let title = if word == "cite" {
                        let (source, quote) = rest.split_once('#').map_or((rest, None), |(s, q)| (s, Some(q)));
                        self.shared.quote_of(source.trim(), quote.map(str::trim))
                    } else {
                        String::new()
                    };
                    self.out.push_str(&format!("<div class=\"meta\" title=\"{}\" data-file=\"{}\" data-line=\"{no}\"><span class=\"kw\">{}</span> {}{}</div>\n", esc(&title), esc(self.file), esc(word), esc(rest), self.shared.badges(self.file, no)));
                    i += 1;
                }
                Kind::Note => {
                    let body = text["note ".len()..].trim().trim_matches('"').replace("\\\"", "\"").replace("\\n", "\n");
                    self.out.push_str(&format!("<aside class=\"note\" data-file=\"{}\" data-line=\"{no}\">{}</aside>\n", esc(self.file), esc(&body)));
                    i += 1;
                }
                Kind::Ref => {
                    let id = text["ref [".len()..].trim_end_matches(']');
                    self.out.push_str(&format!("<p class=\"ref\">see <a class=\"id\" href=\"#{0}\">{0}</a>{1}</p>\n", esc(id), self.shared.badges(self.file, no)));
                    i += 1;
                }
                Kind::DeclBlock => {
                    let body_end = self.dedent(i, end);
                    let (word, name) = text.trim_end_matches(':').split_once(' ').unwrap_or((&text, ""));
                    let outcome = match word {
                        // A check is a proof obligation of the MMT form: `trioc prove` decides it.
                        "check" => Some(format!("obligation check/{name}")),
                        "example" => self.shared.demonstrated.iter().find(|e| e.file == self.file && e.name == name).map(|e| format!("{}, expected {}", e.observed, e.expected)).or_else(|| Some(format!("obligation example/{name}"))),
                        _ => None,
                    };
                    let state = outcome.map_or(String::new(), |text| format!(" <span class=\"badge ok\">{}</span>", esc(&text)));
                    let mut badges = String::new();
                    for j in i..body_end {
                        badges.push_str(&self.shared.badges(self.file, self.lines[j].no));
                    }
                    self.out.push_str(&format!(
                        "<details class=\"decl\" id=\"{}\" data-file=\"{}\" data-line=\"{no}\"><summary><span class=\"kw\">{}</span> <b>{}</b>{state}{badges}</summary><pre>{}</pre></details>\n",
                        esc(&format!("{word}-{name}")),
                        esc(self.file),
                        esc(word),
                        esc(name),
                        self.raw_block(i + 1, body_end)
                    ));
                    i = body_end;
                }
                Kind::Decl => {
                    self.out.push_str(&format!("<p class=\"decl\" data-file=\"{}\" data-line=\"{no}\"><code>{}</code>{}</p>\n", esc(self.file), esc(&text), self.shared.badges(self.file, no)));
                    i += 1;
                }
                Kind::Statement => i = self.paragraph(i, end, depth),
            }
        }
    }

    /// A paragraph of sentences, with the block that its last sentence may open.
    fn paragraph(&mut self, first: usize, end: usize, depth: usize) -> usize {
        let mut text = String::new();
        let mut starts: Vec<(usize, usize)> = Vec::new();
        let mut i = first;
        let mut header = false;
        loop {
            let line = &self.lines[i];
            if !text.is_empty() {
                text.push(' ');
            }
            starts.push((text.len(), line.no));
            text.push_str(&line.text.replace('\n', " "));
            let last = line.text.chars().last();
            i += 1;
            if last == Some(':') {
                header = true;
                break;
            }
            if i >= end || self.lines[i].blank || self.lines[i].indent < self.lines[first].indent {
                break;
            }
            if matches!(last, Some('.' | ';')) && kind_of(&self.lines[i].text) != Kind::Statement {
                break;
            }
        }
        let first_no = self.lines[first].no;
        let line_at = |offset: usize| starts.iter().rev().find(|(from, _)| *from <= offset).map_or(first_no, |(_, no)| *no);
        let spans = sentence_spans(&text);
        let mut sentences = Vec::new();
        let mut head: Option<(Option<String>, String, usize)> = None;
        for (index, (from, to)) in spans.iter().enumerate() {
            let (label, body) = take_label(&text[*from..*to]);
            let line = line_at(to - body.len());
            if header && index + 1 == spans.len() {
                head = Some((label.map(str::to_string), body.to_string(), line));
            } else {
                sentences.push(self.statement(label, body, line, "span"));
            }
        }
        if !sentences.is_empty() {
            self.out.push_str(&format!("<p class=\"para\">{}</p>\n", sentences.join(" ")));
        }
        let Some((label, head, line)) = head else { return i };
        let body_end = self.body_end(first, i, end);
        let label = label.as_deref();
        if head == "concept:" {
            self.concept(label, line, i, body_end);
        } else if head.contains("follow this flow") {
            self.flow(label, &head, line, i, body_end);
        } else if head.contains("following actions") {
            let ordered = head.contains("in order");
            let steps = self.specs.get(&line).and_then(|specs| specs.front()).and_then(|(_, spec)| expand::flow_steps(spec));
            let statement = self.statement(label, &head, line, "div");
            self.out.push_str(&format!("<div class=\"compose\">{statement}\n"));
            let items = self.items(i, body_end, ordered);
            self.out.push_str(&items);
            // An ordered list of actions is also shown as the flow that restates it.
            if let Some(steps) = steps {
                let mut graph = figure::Graph::default();
                let mut before = graph.node("", figure::Shape::Start);
                for (index, action) in steps.iter().enumerate() {
                    let step = graph.node(&format!("s{}", index + 1), figure::Shape::Step);
                    graph.describe(step, action);
                    graph.edge(before, step, "");
                    before = step;
                }
                let finish = graph.node(" ", figure::Shape::Finish);
                graph.edge(before, finish, "");
                let n = self.figure_id();
                self.out.push_str(&format!("<details class=\"view\"><summary>Flow view of this list</summary><figure class=\"diagram flow generated\" data-file=\"{}\" data-line=\"{line}\">{}<figcaption>Generated flow view: it restates the list above</figcaption></figure></details>\n", esc(self.file), graph.svg(n, "generated flow view")));
            }
            self.out.push_str("</div>\n");
        } else {
            self.out.push_str(&format!("<div class=\"scope\" data-file=\"{}\" data-line=\"{line}\"><div class=\"scope-head\">{}{}</div>\n", esc(self.file), esc(&head), self.shared.badges(self.file, line)));
            self.block(i, body_end, depth);
            self.out.push_str("</div>\n");
        }
        body_end
    }

    /// The statements of a block, each from its first line to its terminator.
    fn entries(&self, mut i: usize, end: usize) -> Vec<(usize, usize, String)> {
        let mut out = Vec::new();
        while i < end {
            if self.lines[i].blank || kind_of(&self.lines[i].text) == Kind::Comment {
                i += 1;
                continue;
            }
            let first = i;
            let mut text = self.lines[i].text.clone();
            i += 1;
            let wraps = |text: &str| text.starts_with("step ") || text.starts_with('[') || !["start ", "finish ", "when ", "otherwise "].iter().any(|kw| text.starts_with(kw)) && !text.contains("->");
            while i < end && !self.lines[i].blank && !matches!(text.chars().last(), Some(';' | ':')) && wraps(&text) && self.lines[i].indent >= self.lines[first].indent {
                text.push(' ');
                text.push_str(&self.lines[i].text);
                i += 1;
            }
            out.push((first, i, text));
        }
        out
    }

    fn items(&mut self, from: usize, end: usize, ordered: bool) -> String {
        let tag = if ordered { "ol" } else { "ul" };
        let mut out = format!("<{tag} class=\"acts\">\n");
        let entries = self.entries(from, end);
        let mut skip_to = from;
        for (first, next, text) in entries {
            if first < skip_to {
                continue;
            }
            let (label, body) = take_label(&text);
            let id = label.map_or(String::new(), |id| format!("<a class=\"id\" id=\"{0}\" href=\"#{0}\">{0}</a> ", esc(id)));
            let no = self.lines[first].no;
            if body.ends_with(':') {
                let body_end = self.body_end(first, next, end);
                let nested = self.items(next, body_end, body.contains("in order"));
                out.push_str(&format!("<li data-file=\"{}\" data-line=\"{no}\">{id}<span class=\"op\">{}</span>\n{nested}</li>\n", esc(self.file), esc(body)));
                skip_to = body_end;
            } else {
                out.push_str(&format!("<li data-file=\"{}\" data-line=\"{no}\">{id}{}{}</li>\n", esc(self.file), esc(body), self.shared.badges(self.file, no)));
            }
        }
        out.push_str(&format!("</{tag}>\n"));
        out
    }

    fn figure_id(&self) -> usize {
        let n = self.shared.figures.get() + 1;
        self.shared.figures.set(n);
        n
    }

    /// A concept block: the graph of its edges and the sentences they stand for.
    fn concept(&mut self, label: Option<&str>, line: usize, from: usize, end: usize) {
        let mut graph = figure::Graph::default();
        let mut sentences = Vec::new();
        for (first, _, text) in self.entries(from, end) {
            let no = self.lines[first].no;
            let (edge_label, body) = take_label(&text);
            let pieces: Vec<&str> = body.trim_end_matches(';').split("->").map(str::trim).collect();
            if let [source, relation, target] = pieces.as_slice() {
                let (cardinality, target) = figure::cardinality(target);
                let a = graph.node(&figure::singular(source.strip_prefix("each ").unwrap_or(source)), figure::Shape::Box);
                let b = graph.node(&figure::singular(&target), figure::Shape::Box);
                graph.edge(a, b, &format!("{relation} {cardinality}"));
            }
            let sentence = self.specs.get(&no).and_then(|specs| specs.front()).map(|(_, spec)| expand::expand(spec));
            let sentence = sentence.unwrap_or_else(|| body.to_string());
            sentences.push(self.statement(edge_label, &sentence, no, "li"));
        }
        let n = self.figure_id();
        let caption = label.map_or(String::new(), |id| format!("<a class=\"id\" id=\"{0}\" href=\"#{0}\">{0}</a> ", esc(id)));
        self.out.push_str(&format!(
            "<figure class=\"diagram concept\" data-file=\"{}\" data-line=\"{line}\">{}<figcaption>{caption}Concept diagram{}</figcaption>\n<details open><summary>Controlled English of this diagram</summary><ul class=\"expansion\">\n{}\n</ul></details></figure>\n",
            esc(self.file),
            graph.svg(n, "concept diagram"),
            self.shared.badges(self.file, line),
            sentences.join("\n")
        ));
    }

    /// A flow block: its flowchart and the controlled English it stands for.
    fn flow(&mut self, label: Option<&str>, head: &str, line: usize, from: usize, end: usize) {
        let found = self.specs.get(&line).and_then(|specs| specs.front()).copied();
        let mut graph = figure::Graph::default();
        let start = graph.node("", figure::Shape::Start);
        let mut finish: Option<usize> = None;
        let entries = self.entries(from, end);
        // Steps first: an edge may name a step that is declared after it.
        for (_, _, text) in &entries {
            let (_, body) = take_label(text);
            if let Some((name, action)) = body.strip_prefix("step ").and_then(|rest| rest.split_once(':')) {
                let index = graph.node(name.trim(), figure::Shape::Step);
                graph.describe(index, action.trim().trim_end_matches(';'));
            }
        }
        let mut choice: Option<(usize, usize)> = None;
        for (first, _, text) in &entries {
            let (_, body) = take_label(text);
            let indent = self.lines[*first].indent;
            if choice.is_some_and(|(_, at)| indent <= at) {
                choice = None;
            }
            if body.starts_with("step ") {
                continue;
            }
            if let Some(name) = body.strip_prefix("start ") {
                let to = graph.node(name.trim(), figure::Shape::Step);
                graph.edge(start, to, "");
            } else if let Some(name) = body.strip_prefix("finish ") {
                let from = graph.node(name.trim(), figure::Shape::Step);
                let to = *finish.get_or_insert_with(|| graph.node(" ", figure::Shape::Finish));
                graph.edge(from, to, "");
            } else if let Some(after) = body.strip_prefix("choose after ") {
                let step = graph.node(after.trim_end_matches(':').trim(), figure::Shape::Step);
                let diamond = graph.node(&format!("after {}", after.trim_end_matches(':').trim()), figure::Shape::Choice);
                graph.edge(step, diamond, "");
                choice = Some((diamond, indent));
            } else if let Some((left, right)) = body.rsplit_once("->") {
                let to = graph.node(right.trim().trim_end_matches(';'), figure::Shape::Step);
                match choice {
                    Some((diamond, _)) => graph.edge(diamond, to, left.trim().strip_prefix("when ").unwrap_or(left.trim())),
                    None => {
                        let from = graph.node(left.trim(), figure::Shape::Step);
                        graph.edge(from, to, "");
                    }
                }
            }
        }
        let n = self.figure_id();
        let statement = self.statement(label, head, line, "div");
        let expansion = found.map_or(String::new(), |(_, spec)| expand::expand(spec));
        self.out.push_str(&format!(
            "<figure class=\"diagram flow\" data-file=\"{}\" data-line=\"{line}\">{statement}\n{}<figcaption>Flow diagram</figcaption>\n<details open><summary>Controlled English of this diagram</summary><pre class=\"expansion\">{}</pre></details>\n<details><summary>Authored notation</summary><pre>{}</pre></details></figure>\n",
            esc(self.file),
            graph.svg(n, "flow diagram"),
            esc(&expansion),
            self.raw_block(from, end)
        ));
    }
}

const STYLE: &str = r#"
:root{--bg:#ffffff;--fg:#1f2328;--muted:#656d76;--line:#d0d7de;--soft:#f6f8fa;--accent:#0969da;--ok:#1a7f37;--warn:#9a6700;--node:#eef4fb;--scope:#f3f0ff;--scope-line:#8250df}
@media (prefers-color-scheme: dark){:root{--bg:#1e1f22;--fg:#dfe1e5;--muted:#9aa0a6;--line:#43454a;--soft:#2b2d30;--accent:#6cb6ff;--ok:#57ab5a;--warn:#c69026;--node:#2d3b4d;--scope:#2a2740;--scope-line:#b083f0}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);font:16px/1.65 -apple-system,BlinkMacSystemFont,"Segoe UI",Helvetica,Arial,sans-serif}
main{max-width:54rem;margin:0 auto;padding:1.5rem 1rem 4rem}
h1{font-size:1.9rem;margin:.2rem 0}h2{font-size:1.45rem;margin:2.2rem 0 .6rem;padding-bottom:.25rem;border-bottom:1px solid var(--line)}
h3{font-size:1.2rem;margin:1.8rem 0 .5rem}h4,h5,h6{font-size:1.05rem;margin:1.4rem 0 .4rem}
a{color:var(--accent);text-decoration:none}a:hover{text-decoration:underline}
code,pre{font:13px/1.5 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace}
pre{background:var(--soft);border:1px solid var(--line);border-radius:6px;padding:.6rem .8rem;overflow-x:auto;white-space:pre-wrap}
.edition,.path,.comment,.meta,.nsname,.ref{color:var(--muted);font-size:.85rem}
.status{border:1px solid var(--line);border-left:4px solid var(--ok);border-radius:6px;padding:.6rem .9rem;margin:1rem 0;background:var(--soft)}
.status ul{margin:.3rem 0;padding-left:1.2rem}
nav.toc{border:1px solid var(--line);border-radius:6px;padding:.6rem .9rem;margin:1rem 0}
nav.toc ul{list-style:none;margin:0;padding-left:1rem}nav.toc>ul{padding-left:0}
table{border-collapse:collapse;width:100%;margin:1rem 0}
caption{text-align:left;font-weight:600;margin-bottom:.35rem}
th,td{border:1px solid var(--line);padding:.4rem .55rem;text-align:left;vertical-align:top}
.file{margin-top:2.5rem;border-top:2px solid var(--line)}
.ns{margin:.4rem 0}.kw{color:var(--muted);font-style:italic}
p.para{margin:.7rem 0}
.st{scroll-margin-top:1rem}.st:target{background:color-mix(in srgb,var(--accent) 18%,transparent);border-radius:3px}
a.id{font:600 11px/1 ui-monospace,SFMono-Regular,Menlo,monospace;color:var(--muted);border:1px solid var(--line);border-radius:4px;padding:1px 4px;vertical-align:middle;white-space:nowrap}
a.term{color:inherit;text-decoration:none}
a.term.defined{border-bottom:1px dotted var(--accent)}
a.term.derived:hover,a.term.defined:hover{color:var(--accent);border-bottom:1px solid var(--accent)}
.mark,.badge{font:11px/1 ui-monospace,SFMono-Regular,Menlo,monospace;border-radius:8px;padding:1px 5px;white-space:nowrap;vertical-align:middle;cursor:help}
.mark{color:var(--muted)}.mark.unsourced{color:var(--warn)}
.badge{color:#fff;background:var(--muted)}.badge.warn{background:var(--warn)}.badge.ok{background:var(--ok)}
aside.note{border-left:3px solid var(--line);color:var(--muted);padding:.1rem .8rem;margin:.7rem 0;font-size:.92rem;white-space:pre-wrap}
.scope{border:1px solid var(--scope-line);border-radius:8px;background:var(--scope);padding:.2rem .9rem .4rem;margin:.9rem 0}
.scope-head{font-weight:600;color:var(--scope-line);margin:.35rem 0}
.compose{margin:.7rem 0}.acts{margin:.3rem 0}.op{font-style:italic;color:var(--muted)}
details.decl{margin:.6rem 0}details>summary{cursor:pointer;color:var(--muted);font-size:.88rem}
p.decl{margin:.3rem 0}
figure.diagram{border:1px solid var(--line);border-radius:8px;padding:.8rem;margin:1rem 0;overflow-x:auto}
figure.diagram svg{display:block;margin:.4rem auto;max-width:100%;height:auto;color:var(--fg)}
figcaption{color:var(--muted);font-size:.85rem;text-align:center;margin-bottom:.4rem}
svg .shape{fill:var(--node);stroke:var(--fg);stroke-width:1.2}svg .dot{fill:var(--fg)}svg .ring{fill:none;stroke:var(--fg);stroke-width:1.2}
svg .wire{fill:none;stroke:var(--fg);stroke-width:1.2}svg text{fill:var(--fg);font:12px -apple-system,BlinkMacSystemFont,"Segoe UI",Helvetica,Arial,sans-serif}
svg text.name{font-weight:600}svg text.edge{font-size:11px;paint-order:stroke;stroke:var(--bg);stroke-width:4px;stroke-linejoin:round}
ul.expansion{margin:.3rem 0}
dl.glossary dt{font-weight:600;margin-top:.7rem;scroll-margin-top:1rem}dl.glossary dt:target{color:var(--accent)}
dl.glossary dd{margin:0 0 0 1rem;color:var(--muted);font-size:.92rem}dl.glossary small{font-weight:400;color:var(--muted)}
.mark.priority{border:1px solid var(--line)}
.mark.refine{color:var(--muted)}
"#;

/// Renders the package, or one of its files, as one HTML document.
pub(crate) fn render(project: &Project, converted: &Converted, only: Option<&str>) -> Result<String, String> {
    let analysis = &converted.analysis;
    let documents: Vec<&Document> = project.set.packages.iter().filter(|p| p.is_root).flat_map(|p| &p.documents).collect();
    let mut files: Vec<&str> = Vec::new();
    for document in &documents {
        if !files.contains(&document.file.as_str()) {
            files.push(&document.file);
        }
    }
    if let Some(wanted) = only {
        let wanted = wanted.trim_start_matches("./");
        files.retain(|file| *file == wanted || file.ends_with(&format!("/{wanted}")) || wanted.ends_with(&format!("/{file}")));
        if files.is_empty() {
            return Err(format!("no file of package `{}` is `{wanted}`", project.manifest.package.name));
        }
    }

    let diagnostics: Vec<Diagnostic> = converted.all().cloned().collect();
    let source_report = &converted.sources;
    let mut placed: BTreeMap<(String, usize), Vec<usize>> = BTreeMap::new();
    for (index, diagnostic) in diagnostics.iter().enumerate() {
        for reference in &diagnostic.refs {
            let at = placed.entry((reference.file.clone(), reference.line)).or_default();
            if !at.contains(&index) {
                at.push(index);
            }
        }
    }
    let glossary: BTreeMap<String, GlossaryEntry> = glossary(&analysis.vocabulary).into_iter().map(|e| (e.term.clone(), e)).collect();
    let mut anchors = BTreeMap::new();
    for spec in documents.iter().filter(|d| files.contains(&d.file.as_str())).flat_map(|d| &d.specs) {
        anchors.entry(format!("{}:{}", spec.file, spec.line)).or_insert_with(|| anchor_of(spec));
    }
    let mut details_of: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for spec in project.root_specs() {
        if let Some(id) = &spec.id {
            for detail in &spec.details {
                details_of.entry(detail.clone()).or_default().push(id.clone());
            }
        }
    }
    let shared = Shared { project, analysis: &analysis, demonstrated: &converted.demonstrated, diagnostics, placed, shown: RefCell::new(BTreeSet::new()), glossary, anchors, used_terms: RefCell::new(BTreeSet::new()), figures: Cell::new(0), details_of };

    let mut body = String::new();
    let mut toc = String::new();
    let mut statements = 0;
    for file in &files {
        let path = project.files.get(*file).cloned().unwrap_or_else(|| project.root.join(file));
        let text = fs::read_to_string(&path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        let mut specs: BTreeMap<usize, VecDeque<(&Document, &Spec)>> = BTreeMap::new();
        let mut tables = BTreeMap::new();
        for document in documents.iter().filter(|d| d.file == *file) {
            for spec in &document.specs {
                specs.entry(spec.line).or_default().push_back((document, spec));
                statements += 1;
            }
            tables.extend(document.tables.iter().map(|table| (table.line, table)));
        }
        let lines = lines_of(&text);
        let count = lines.len();
        let mut view = FileView { shared: &shared, file, lines, specs, tables, out: String::new(), toc: Vec::new(), headings: BTreeMap::new() };
        view.block(0, count, 3);
        let anchor = format!("file-{}", slug(file));
        body.push_str(&format!("<article class=\"file\" id=\"{anchor}\"><div class=\"path\">{}</div>\n{}</article>\n", esc(file), view.out));
        toc.push_str(&format!("<li><a href=\"#{anchor}\"><code>{}</code></a>", esc(file)));
        let mut level = 2;
        for (depth, anchor, title) in &view.toc {
            while level < *depth {
                toc.push_str("<ul>");
                level += 1;
            }
            while level > *depth {
                toc.push_str("</ul>");
                level -= 1;
            }
            toc.push_str(&format!("<li><a href=\"#{anchor}\">{}</a></li>", esc(title)));
        }
        while level > 2 {
            toc.push_str("</ul>");
            level -= 1;
        }
        toc.push_str("</li>\n");
    }

    // The package line of the entry file names the edition.
    let entry = project.root.join(project.manifest.package.entry.as_deref().unwrap_or("trion.trion"));
    let edition = fs::read_to_string(entry).ok().and_then(|text| {
        let line = text.lines().find(|l| l.starts_with("package ") && l.contains(" edition "))?;
        Some(line.split_once(" edition ")?.1.trim().trim_matches('"').to_string())
    });

    // The package conforms to the language: what is left to say of it is a
    // warning. Nothing in the document is proved: the proof obligations are
    // listed with the bound that each is about.
    let warnings = shared.diagnostics.iter().filter(|d| d.severity == Severity::Warning).count();
    let stated = &converted.obligations;
    let mut status = format!("<section class=\"status\" id=\"status\"><strong>converted</strong>: {statements} statements shown; the package conforms to the language with {warnings} warnings, and nothing here is proved<ul>\n");
    for obligation in &stated.obligations {
        status.push_str(&format!("<li>proof obligation <code>{}</code> ({}): {}; not proved here: <code>trioc prove</code> proves it from the MMT form</li>\n", esc(&obligation.name), esc(&obligation.property), esc(&obligation.proposition)));
    }
    if !converted.control.system.is_empty() || !converted.control.environment.is_empty() {
        let names = |set: &std::collections::BTreeSet<String>| if set.is_empty() { "none".to_string() } else { set.iter().map(|a| esc(a)).collect::<Vec<_>>().join(", ") };
        status.push_str(&format!("<li>system: {}; environment: {}</li>\n", names(&converted.control.system), names(&converted.control.environment)));
    }
    for declared in &converted.declared {
        status.push_str(&format!("<li>declared, not checked: {}</li>\n", esc(declared)));
    }
    if let Some(individuals) = &analysis.model.individuals {
        status.push_str(&format!("<li>individuals: semantic version {}; domains of {} individuals of each declared type</li>\n", esc(individuals.version), individuals.scope));
        status.push_str("<li><details><summary>readings over individuals</summary><dl>\n");
        for meaning in &individuals.meanings {
            status.push_str(&format!("<dt>[{}] {}</dt><dd>{}</dd>\n", esc(&meaning.statement), esc(&meaning.source), meaning.lines().iter().map(|line| esc(line)).collect::<Vec<_>>().join("<br>")));
        }
        status.push_str("</dl></details></li>\n");
    }
    for source in &source_report.sources {
        status.push_str(&format!("<li>source {}: {:.2}% cited</li>\n", esc(&source.id), source.percent));
    }
    status.push_str("</ul>");
    let unplaced: Vec<&Diagnostic> = shared.diagnostics.iter().enumerate().filter(|(index, _)| !shared.shown.borrow().contains(index)).map(|(_, d)| d).collect();
    if !unplaced.is_empty() {
        status.push_str(&format!("<details><summary>{} diagnostics outside the statements shown</summary><ul>\n", unplaced.len()));
        for diagnostic in unplaced {
            let class = if diagnostic.severity == Severity::Warning { "warn" } else { "info" };
            let place = diagnostic.refs.first().map_or(String::new(), |r| format!(" <code>{}:{}</code>", esc(&r.file), r.line));
            status.push_str(&format!("<li><span class=\"badge {class}\">{}</span> {}{place}</li>\n", esc(&diagnostic.code), esc(&diagnostic.message)));
        }
        status.push_str("</ul></details>");
    }
    status.push_str("</section>\n");

    // The relations that were written as sentences, drawn as one concept view for each file.
    let mut views = String::new();
    let mut by_file: BTreeMap<String, Vec<expand::ConceptEdge>> = BTreeMap::new();
    for spec in project.root_specs().filter(|s| s.expansion.is_none() && only.is_none_or(|wanted| s.file == wanted || s.file.ends_with(wanted) || wanted.ends_with(&s.file))) {
        if let Some(edge) = expand::concept_edge(spec) {
            by_file.entry(spec.file.clone()).or_default().push(edge);
        }
    }
    for (file, edges) in &by_file {
        let mut graph = figure::Graph::default();
        for edge in edges {
            let (cardinality, target) = figure::cardinality(&edge.to);
            let a = graph.node(&figure::singular(edge.from.strip_prefix("each ").unwrap_or(&edge.from)), figure::Shape::Box);
            let b = graph.node(&figure::singular(&target), figure::Shape::Box);
            graph.edge(a, b, &format!("{} {cardinality}", edge.relation));
        }
        let n = shared.figures.get() + 1;
        shared.figures.set(n);
        views.push_str(&format!(
            "<figure class=\"diagram concept generated\" data-file=\"{}\" data-line=\"{}\">{}<figcaption>Generated concept view of the relations stated in {}</figcaption>\n<details><summary>Diagram notation of this view</summary><pre>{}</pre></details></figure>\n",
            esc(file),
            edges.first().map_or(0, |e| e.line),
            graph.svg(n, "generated concept view"),
            esc(file),
            esc(&expand::concept_notation(None, edges))
        ));
    }
    if !views.is_empty() {
        views = format!("<section id=\"views\"><h2>Generated diagram views</h2>\n{views}</section>\n");
    }

    // A primitive is accepted without a definition: its meaning is the statements about it.
    let primitives: BTreeSet<String> = project.set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| d.primitives.iter().map(|p| p.name.to_lowercase())).collect();
    // The statements that relate concepts: inclusions, exclusions and the like, which the model reads as axioms.
    let axioms: BTreeSet<&str> = analysis.model.constraints.iter().filter(|c| c.kind.is_vocabulary()).flat_map(|c| &c.refs).map(|r| r.id.as_str()).collect();
    let relating: Vec<&Spec> = project.root_specs().filter(|s| !matches!(s.sentence.core, trion_language::syntax::ast::Core::Definition { .. }) && axioms.contains(s.display_id().as_str())).collect();
    // A primitive is listed although no definition links to it.
    for key in shared.glossary.keys().filter(|key| primitives.contains(&key.rsplit("::").next().unwrap_or(key).to_lowercase())) {
        shared.used_terms.borrow_mut().insert(key.clone());
    }
    let mut terms = String::from("<section id=\"glossary\"><h2>Glossary</h2>\n<dl class=\"glossary\">\n");
    for key in shared.used_terms.borrow().iter() {
        let entry = &shared.glossary[key];
        let kinds = if entry.kinds.is_empty() { String::new() } else { format!(": {}", entry.kinds.join(", ")) };
        terms.push_str(&format!("<dt id=\"g-{}\">{} <small>{}{}</small></dt>\n<dd>", slug(key), esc(key.rsplit("::").next().unwrap_or(key)), if entry.definition.is_some() { "defined" } else if primitives.contains(&key.rsplit("::").next().unwrap_or(key).to_lowercase()) { "primitive" } else if entry.declared_at.is_some() { "declared" } else { "derived" }, esc(&kinds)));
        if let Some(definition) = &entry.definition {
            terms.push_str(&esc(definition));
            terms.push(' ');
        }
        let place = entry.defined_at.as_ref().or(entry.declared_at.as_ref()).or(entry.first_use.as_ref());
        if let Some(place) = place {
            let word = if entry.defined_at.is_some() { "defined at" } else if entry.declared_at.is_some() { "declared at" } else { "first used at" };
            match shared.anchors.get(place) {
                Some(anchor) => terms.push_str(&format!("{word} <a href=\"#{}\"><code>{}</code></a>; ", esc(anchor), esc(place))),
                None => terms.push_str(&format!("{word} <code>{}</code>; ", esc(place))),
            }
        }
        if !entry.namespace.is_empty() {
            terms.push_str(&format!("namespace <code>{}</code>; ", esc(&entry.namespace)));
        }
        let related: Vec<String> = relating
            .iter()
            .filter(|s| entry.occurrences_at.iter().any(|at| *at == format!("{}:{}", s.file, s.line)))
            .map(|s| match shared.anchors.get(&format!("{}:{}", s.file, s.line)) {
                Some(anchor) => format!("<a href=\"#{}\">{}</a>", esc(anchor), esc(&s.sentence.source)),
                None => esc(&s.sentence.source),
            })
            .collect();
        if !related.is_empty() {
            terms.push_str(&format!("related by: {}; ", related.join(" ")));
        }
        terms.push_str(&format!("{} occurrences</dd>\n", entry.occurrences));
    }
    terms.push_str("</dl></section>\n");

    let name = &project.manifest.package.name;
    let title = match only {
        Some(_) if files.len() == 1 => format!("{name}: {}", files[0]),
        _ => name.clone(),
    };
    Ok(format!(
        "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>{}</title>\n<style>{STYLE}</style>\n</head>\n<body>\n<main>\n<header><h1>{}</h1>\n<div class=\"edition\">{}</div></header>\n{status}<nav class=\"toc\"><strong>Contents</strong><ul>\n{toc}<li><a href=\"#glossary\">Glossary</a></li></ul></nav>\n{body}{views}{terms}</main>\n</body>\n</html>\n",
        esc(&title),
        esc(&title),
        edition.map_or(String::new(), |e| format!("edition {}", esc(&e))),
    ))
}
