//! The `.trion` source format: a file is a package declaration, includes and
//! namespace blocks. Blocks open with `:` and close with `end`; delimiters
//! decide the structure and indentation only helps the reader.
//!
//! The English inside a statement is read by [`crate::syntax`]. This layer
//! keeps what a sentence cannot carry: which namespace owns a name, which
//! conditions a block shares, and where a citation applies.

use crate::diagnostic::{Diagnostic, SpecRef};
use crate::syntax::ast::*;
use crate::syntax::parse::{parse, ParseError};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

mod table;
pub use table::{Table, TableCell, TableRow};

/// A provenance or review annotation that applies to a statement.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Meta {
    /// `cite SOURCE` or `cite SOURCE#QUOTE`
    Cite { source: String, quote: Option<String> },
    /// `unsourced "reason"`: no source states this, for the reason given.
    Unsourced { reason: String },
}

/// Where one element of a diagram or a composition was written.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Element {
    /// `node`, `label`, `edge`, `step`, `start`, `finish`, `guard` or `otherwise`.
    pub kind: String,
    /// The node, the label, the step, or `from -> to`.
    pub name: String,
    pub id: Option<String>,
    pub line: usize,
    /// The element as written.
    pub text: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Spec {
    /// The stable identifier. Without one, the position identifies the statement.
    pub id: Option<String>,
    pub sentence: Sentence,
    pub meta: Vec<Meta>,
    pub file: String,
    pub line: usize,
    /// The titles of the enclosing sections, outermost first.
    pub sections: Vec<String>,
    /// Stable identifiers of the identified items of a composition or diagram.
    pub parts: Vec<String>,
    /// The expansion of a diagram or a shared context, when it has one.
    pub expansion: Option<String>,
    /// `true` for the `otherwise` branch: the frames are denied.
    pub otherwise: bool,
    /// The source extent: the column of the first character and the line of the last.
    pub column: usize,
    pub end_line: usize,
    /// `true` when an earlier sentence of the paragraph begins on the same line.
    pub shares_line: bool,
    /// The heads of the enclosing explicit scopes, outermost first.
    pub scopes: Vec<String>,
    /// The line of each of those heads: two blocks with one head are two
    /// scopes. An assumption sentence in a block is distributed to the
    /// guarantee sentences of that block only.
    pub scope_lines: Vec<usize>,
    /// The elements of the diagram that this statement was written as.
    pub elements: Vec<Element>,
    /// The declared diagram kind of a statement written as an element of that kind.
    pub diagram: Option<String>,
    /// The statements that detail this one: `detailed by [ID], [ID]`.
    pub details: Vec<String>,
    /// The statements that this one takes priority over: `overrides [ID], [ID]`.
    pub overrides: Vec<String>,
    /// `default`: the statement yields to each more specific statement that contradicts it.
    pub default: bool,
    /// `weight N`: how much a recommendation counts when recommendations conflict.
    pub weight: Option<u32>,
    /// The sentence with composite vocabulary that this statement is one
    /// part of, as it was written, and the number of the part, from one.
    /// The sentence of the statement is the simple sentence that the part
    /// abbreviates: every statement holds a simple sentence.
    pub abbreviates: Option<(String, usize)>,
}

impl Spec {
    /// The stable identifier, or the position of a statement without one.
    /// A part of a sentence with composite vocabulary is named after the
    /// sentence and its number: `ID/2`.
    pub fn display_id(&self) -> String {
        let part = |base: String| match &self.abbreviates {
            Some((_, number)) => format!("{base}/{number}"),
            None => base,
        };
        match &self.id {
            Some(id) => id.clone(),
            None if self.shares_line => part(format!("{}:{}:{}", self.file, self.line, self.column)),
            None => part(format!("{}:{}", self.file, self.line)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct VocabDecl {
    pub term: String,
    pub kind: String,
    pub file: String,
    pub line: usize,
}

/// `predicate overlap(interval, interval)`: an uninterpreted predicate. The
/// declaration supplies a signature and an identity, and no axiom.
/// `primitive NAME`, or `primitive NAME, NAME, …` for several: a term that
/// the author accepts without a definition. Its meaning is the statements
/// about it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PrimitiveDecl {
    pub name: String,
    pub file: String,
    pub line: usize,
}

/// `environment NAME` or `system NAME`: who controls what the term does.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ControlDecl {
    pub name: String,
    /// `environment` or `system`.
    pub by: String,
    pub file: String,
    pub line: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PredicateDecl {
    pub name: String,
    pub signature: Vec<String>,
    pub file: String,
    pub line: usize,
}

/// A claim that the sentence grammar agrees with a revision of another
/// grammar for the sentence forms that it names.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CompatibilityClaim {
    pub name: String,
    /// The source that identifies the other grammar.
    pub source: String,
    pub revision: String,
    /// The sentence forms that the claim covers.
    pub forms: Vec<String>,
    pub file: String,
    pub line: usize,
}

/// The sentence forms that a compatibility claim may name.
const SENTENCE_FORMS: [&str; 15] = ["Definition", "Description", "Ubiquitous", "Optional-feature", "State-driven", "Event-driven", "Unwanted-behaviour", "Complex", "Must", "Recommendation", "Permission", "Prohibition", "Temporal-opener", "Exception", "Purpose"];

/// A declared diagram kind: how an element is written, what its parts are,
/// the controlled English that an element means, and why that keeps the meaning.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DiagramKind {
    pub name: String,
    /// The element grammar: literal text around `$name` placeholders.
    pub element: String,
    /// The typing rules: the term kind of each placeholder.
    pub types: Vec<(String, String)>,
    /// The controlled English sentence that one element expands to.
    pub expansion: String,
    /// The meaning-preservation contract.
    pub preserves: String,
    pub file: String,
    pub line: usize,
}

/// The `$name` placeholders of a template, in order.
fn placeholders(template: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = template;
    while let Some(at) = rest.find('$') {
        let name: String = rest[at + 1..].chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
        rest = &rest[at + 1 + name.len()..];
        if !name.is_empty() {
            out.push(name);
        }
    }
    out
}

/// Reads an element against the element grammar of its kind.
fn match_element(pattern: &str, text: &str) -> Option<Vec<(String, String)>> {
    let mut found = Vec::new();
    let mut pattern = pattern.trim();
    let mut text = text.trim();
    loop {
        match pattern.find('$') {
            None => return (pattern.trim() == text.trim()).then_some(found),
            Some(at) => {
                text = text.strip_prefix(pattern[..at].trim())?.trim_start();
                let name: String = pattern[at + 1..].chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
                pattern = pattern[at + 1 + name.len()..].trim_start();
                let literal = pattern.split('$').next().unwrap_or("").trim();
                let end = if literal.is_empty() { if pattern.is_empty() { text.len() } else { return None } } else { text.find(literal)? };
                let value = text[..end].trim();
                if value.is_empty() {
                    return None;
                }
                found.push((name, value.to_string()));
                text = &text[end..];
            }
        }
    }
}

fn parse_predicate(rest: &str) -> Option<(String, Vec<String>)> {
    let (name, arguments) = rest.trim().strip_suffix(')')?.split_once('(')?;
    let word = |w: &str| !w.is_empty() && w.chars().all(|c| c.is_ascii_alphanumeric() || c == '-' || c == ' ');
    let signature: Vec<String> = arguments.split(',').map(|a| a.trim().to_string()).collect();
    (word(name.trim()) && !name.trim().contains(' ') && signature.iter().all(|a| word(a))).then(|| (name.trim().to_string(), signature))
}

/// `use a.b`: makes the term domain of a namespace available in a block.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Import {
    pub name: String,
    pub namespace: String,
    pub file: String,
    pub line: usize,
}

/// `extend X with A, B.`
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Extension {
    pub attr: String,
    pub values: Vec<String>,
    pub file: String,
    pub line: usize,
    pub text: String,
}

/// `classify sentences as X.`
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Classification {
    pub attr: String,
    pub file: String,
    pub line: usize,
    pub text: String,
}

/// `bind TERM as ROLE.`
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Binding {
    pub term: String,
    pub role: String,
    pub file: String,
    pub line: usize,
    pub text: String,
}

/// `alias NAME = TERM`: a member of its namespace, like any other name.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Alias {
    pub term: String,
    pub canonical: String,
    pub file: String,
    pub line: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FormRule {
    pub id: String,
    pub pattern: Sentence,
    pub variable: String,
    pub regex: String,
    pub negated: bool,
    pub applies_when: Option<String>,
    pub file: String,
    pub line: usize,
    pub text: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RequiredRule {
    pub id: String,
    pub pattern: Sentence,
    pub file: String,
    pub line: usize,
    pub text: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Role {
    pub name: String,
    pub activations: Vec<Sentence>,
    pub forms: Vec<FormRule>,
    pub required: Vec<RequiredRule>,
    pub file: String,
    pub line: usize,
}

/// `source NAME:` with its title, locator and quotes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Default)]
pub struct SourceDecl {
    pub name: String,
    pub title: Option<String>,
    pub locator: Option<String>,
    pub revision: Option<String>,
    pub select: Vec<String>,
    /// `requirement` or `citation`.
    pub kind: Option<String>,
    /// A local copy of the source; the copy makes coverage measurable.
    pub path: Option<String>,
    pub sha256: Option<String>,
    pub retrieved: Option<String>,
    pub minimum: Option<String>,
    pub quotes: Vec<Quote>,
    pub file: String,
    pub line: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Quote {
    pub name: String,
    pub text: String,
    pub line: usize,
}

/// `check NAME:`: an obligation to prove a relation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Check {
    pub name: String,
    pub relation: String,
    pub left: Vec<String>,
    pub right: Vec<String>,
    /// `true` when the block states no question that this edition decides:
    /// a field is missing or unknown, or the relation is not `equivalent`.
    /// The block is reported where it is read, and nothing is proved of it.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub malformed: bool,
    pub file: String,
    pub line: usize,
}

/// A check with an isolated propositional input, read into a checked Core problem.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PropositionalCheck {
    pub name: String,
    pub input: trion_cnl::Accepted,
    pub file: String,
    pub line: usize,
}

/// `example NAME:`: an isolated input with an expected outcome.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Example {
    pub name: String,
    pub kind: String,
    pub form: Option<String>,
    pub input: Option<String>,
    pub base: Vec<String>,
    pub candidate: Vec<String>,
    pub expect: String,
    pub file: String,
    pub line: usize,
}

/// `scenario NAME:`: one concrete behaviour with the judgement that the
/// author expects of it. The individuals of a scenario are named by
/// variables; what it does not state does not exist, does not hold and does
/// not happen.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Scenario {
    pub name: String,
    /// Each individual with the noun of its type, in the order of the
    /// declarations: `given a user U1, a room R1`.
    pub individuals: Vec<(String, String)>,
    /// The facts of the domain, each a sentence: `given U1 is a member of R1.`
    pub facts: Vec<(usize, String)>,
    /// What holds or happens at a time in milliseconds: `at 0 ms: U1 posts M1 to R1.`
    pub at: Vec<(usize, i64, String)>,
    /// `allowed`, `forbidden`, or `undefined` for a behaviour in which a
    /// share that a statement bounds has no value.
    pub expect: String,
    /// `true` when a field of the block was not read: the block states no
    /// behaviour, and nothing is judged of it.
    pub malformed: bool,
    pub file: String,
    pub line: usize,
}

/// One namespace block.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Default)]
pub struct Document {
    pub namespace: String,
    pub file: String,
    pub extensions: Vec<Extension>,
    pub classifications: Vec<Classification>,
    pub imports: Vec<Import>,
    pub vocabulary: Vec<VocabDecl>,
    pub predicates: Vec<PredicateDecl>,
    pub primitives: Vec<PrimitiveDecl>,
    /// `measure NAME`: the population whose shares the statements may bound,
    /// as in `for at least 99.9 percent of requests`.
    pub measures: Vec<PrimitiveDecl>,
    /// `individuals NAME, NAME`: the types whose individuals the statements
    /// tell apart. A statement about such a type speaks about each
    /// individual of the type, and one noun names one individual throughout
    /// the statement. Each name is a primitive term as well.
    pub individuals: Vec<PrimitiveDecl>,
    pub controls: Vec<ControlDecl>,
    pub diagram_kinds: Vec<DiagramKind>,
    pub compatibility: Vec<CompatibilityClaim>,
    pub aliases: Vec<Alias>,
    pub roles: Vec<Role>,
    pub bindings: Vec<Binding>,
    pub specs: Vec<Spec>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub tables: Vec<Table>,
    pub sources: Vec<SourceDecl>,
    pub checks: Vec<Check>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub propositional_checks: Vec<PropositionalCheck>,
    pub examples: Vec<Example>,
    pub scenarios: Vec<Scenario>,
    /// Identifiers displayed by `ref`, with their lines.
    pub references: Vec<(String, usize)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PackageDecl {
    pub name: String,
    pub edition: String,
    pub line: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Include {
    pub path: String,
    pub line: usize,
}

/// One parsed source file.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Default)]
pub struct ParsedFile {
    pub package: Option<PackageDecl>,
    pub includes: Vec<Include>,
    pub documents: Vec<Document>,
}

/// Which terms the statements of a set may use.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum VocabularyMode {
    /// Declared terms and terms inferred from the specification set are usable.
    #[default]
    Inferred,
    /// Only declared terms are usable.
    Declared,
}

/// One package of a set: its name and its namespace blocks.
#[derive(Debug, Clone, Default)]
pub struct Package {
    pub name: String,
    pub is_root: bool,
    pub documents: Vec<Document>,
}

impl Package {
    /// Every identifier that the package declares: its statements and the
    /// items inside them.
    pub fn identifiers(&self) -> BTreeSet<String> {
        self.documents.iter().flat_map(|d| &d.specs).flat_map(|s| s.id.iter().chain(s.parts.iter().filter(|p| p.as_str() != "concept-edge"))).cloned().chain(self.documents.iter().flat_map(|d| &d.references).filter_map(|(id, _)| id.strip_prefix("concept:").map(str::to_string))).collect()
    }
}

/// A specification set: the root package and the packages that it depends
/// on. Its formal meaning is the conjunction of the contracts of its statements.
#[derive(Debug, Clone, Default)]
pub struct SpecSet {
    pub packages: Vec<Package>,
    pub vocabulary_mode: VocabularyMode,
}

/// Parses exactly one sentence.
pub fn parse_sentence(text: &str) -> Result<Sentence, String> {
    single_sentence(text).map_err(|e| e.to_string())
}

fn single_sentence(text: &str) -> Result<Sentence, ParseError> {
    let spec = parse(text)?;
    let mut sentences = spec.sentences;
    match (sentences.pop(), sentences.is_empty()) {
        (Some(only), true) => Ok(only),
        _ => Err(ParseError::Empty),
    }
}

/// A line of source with comments gone and multiline strings folded into
/// ordinary escaped strings.
struct Line {
    no: usize,
    indent: usize,
    text: String,
}

fn escape(text: &str) -> String {
    text.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n")
}

fn logical_lines(src: &str) -> Vec<Line> {
    let chars: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let (mut i, mut no, mut start) = (0, 1, 1);
    let mut cur = String::new();
    let flush = |cur: &mut String, start: usize, out: &mut Vec<Line>| {
        let indent = cur.chars().take_while(|c| c.is_whitespace()).count();
        let text = cur.trim().to_string();
        if !text.is_empty() {
            out.push(Line { no: start, indent, text });
        }
        cur.clear();
    };
    let at = |i: usize, s: &str| s.chars().enumerate().all(|(k, c)| chars.get(i + k) == Some(&c));
    while i < chars.len() {
        let c = chars[i];
        if at(i, "\"\"\"") {
            let body_start = i + 3;
            let mut j = body_start;
            while j < chars.len() && !at(j, "\"\"\"") {
                j += 1;
            }
            let body: String = chars[body_start..j.min(chars.len())].iter().collect();
            no += body.matches('\n').count();
            let body = body.strip_prefix('\n').unwrap_or(&body);
            let body = body.strip_suffix('\n').unwrap_or(body);
            cur.push('"');
            cur.push_str(&escape(body));
            cur.push('"');
            i = (j + 3).min(chars.len());
            continue;
        }
        if c == '"' {
            cur.push(c);
            i += 1;
            while i < chars.len() && chars[i] != '"' && chars[i] != '\n' {
                if chars[i] == '\\' && i + 1 < chars.len() && chars[i + 1] != '\n' {
                    cur.push(chars[i]);
                    i += 1;
                }
                cur.push(chars[i]);
                i += 1;
            }
            if chars.get(i) == Some(&'"') {
                cur.push('"');
                i += 1;
            }
            continue;
        }
        if c == '`' {
            let close = (i + 1..chars.len()).take_while(|&k| chars[k] != '\n').find(|&k| chars[k] == '`');
            if let Some(close) = close {
                cur.extend(&chars[i..=close]);
                i = close + 1;
                continue;
            }
        }
        if at(i, "//") {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        if c == '\n' {
            flush(&mut cur, start, &mut out);
            no += 1;
            start = no;
            i += 1;
            continue;
        }
        if cur.trim().is_empty() {
            start = no;
        }
        cur.push(c);
        i += 1;
    }
    flush(&mut cur, start, &mut out);
    out
}

/// Reads a quoted string at the start of the text, returning it and the rest.
fn quoted(text: &str) -> Option<(String, &str)> {
    let body = text.trim_start().strip_prefix('"')?;
    let mut out = String::new();
    let mut chars = body.char_indices();
    while let Some((at, c)) = chars.next() {
        match c {
            '"' => return Some((out, &body[at + 1..])),
            '\\' => match chars.next() {
                Some((_, 'n')) => out.push('\n'),
                Some((_, other)) => out.push(other),
                None => return None,
            },
            other => out.push(other),
        }
    }
    None
}

fn whole_string(text: &str) -> Option<String> {
    let (value, rest) = quoted(text)?;
    rest.trim().is_empty().then_some(value)
}

fn is_stable_id(id: &str) -> bool {
    let (head, tail) = id.split_once('/').map_or((id, None), |(h, t)| (h, Some(t)));
    let mut chars = head.chars();
    chars.next().is_some_and(|c| c.is_ascii_uppercase()) && chars.all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '-') && tail.is_none_or(is_component)
}

fn is_component(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(|c| c.is_ascii_lowercase()) && chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
}

fn is_metadata_name(name: &str) -> bool {
    !name.contains('/') && is_stable_id(name)
}

fn is_dotted(name: &str) -> bool {
    !name.is_empty() && name.split('.').all(is_component)
}

fn keyword<'a>(line: &'a str, kw: &str) -> Option<&'a str> {
    let rest = line.strip_prefix(kw)?;
    rest.starts_with(char::is_whitespace).then(|| rest.trim())
}

/// Lists the namespaces a file names in `use` declarations, without parsing
/// its sentences.
pub fn scan_imports(src: &str) -> Vec<String> {
    logical_lines(src).iter().filter_map(|l| keyword(&l.text, "use")).filter(|rest| !rest.contains(char::is_whitespace)).map(str::to_string).collect()
}

/// The bracketed references of a field: `[A], [B]`.
fn bracket_list(text: &str) -> Option<Vec<String>> {
    text.split(',').map(|part| part.trim().strip_prefix('[')?.strip_suffix(']').filter(|id| is_stable_id(id)).map(str::to_string)).collect()
}

/// The sentence terminator of a line, outside strings and literals.
fn last_significant(text: &str) -> Option<char> {
    let (mut in_string, mut in_literal) = (false, false);
    let mut escaped = false;
    let mut last = None;
    for c in text.chars() {
        if in_string {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_string = false;
            }
            last = None;
            continue;
        }
        if in_literal {
            in_literal = c != '`';
            last = None;
            continue;
        }
        match c {
            '"' => {
                in_string = true;
                last = None;
            }
            '`' => {
                in_literal = text.matches('`').count() % 2 == 0;
                last = None;
            }
            _ if c.is_whitespace() => {}
            other => last = Some(other),
        }
    }
    last
}

/// Double quotes in a sentence name literals, so they read as one word.
fn literals_as_backticks(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(at) = rest.find('"') {
        out.push_str(&rest[..at]);
        match quoted(&rest[at..]) {
            Some((value, tail)) => {
                out.push('`');
                out.push_str(&value);
                out.push('`');
                rest = tail;
            }
            None => {
                rest = &rest[at..];
                break;
            }
        }
    }
    out.push_str(rest);
    out
}

/// The uppercase variables that are bound at a point of a specification.
#[derive(Debug, Clone, Default)]
struct Vars {
    bound: BTreeMap<String, String>,
    /// Variables bound in an alternative that has since closed.
    closed: BTreeSet<String>,
    /// `true` inside an item of a composition: the text is a response.
    in_response: bool,
    /// What makes the bindings of this statement its own: its file and line.
    tag: String,
}

/// The mark of an object that a response introduces. `create a report R`
/// names one report of that activation, not every report: the mark keeps
/// it apart from the bindings of other statements, and its type stands after it.
pub(crate) const BINDING_MARK: char = '#';

/// The text with each bound object written as its variable again: `create a
/// report R` and `retain R`. A generated view written this way reads back to
/// the statement that it restates.
pub(crate) fn with_variables(text: &str) -> String {
    let words: Vec<&str> = text.split(' ').collect();
    let mut out: Vec<String> = Vec::new();
    let mut i = 0;
    while i < words.len() {
        let word = words[i];
        let mark = word.strip_prefix("`#").and_then(|rest| rest.strip_suffix('`'));
        let parsed = mark.and_then(|m| {
            let (name, rest) = m.split_once('@')?;
            let size: usize = rest.rsplit_once('/')?.1.parse().ok()?;
            Some((name.to_string(), size))
        });
        let Some((name, size)) = parsed else {
            out.push(word.to_string());
            i += 1;
            continue;
        };
        let noun: Vec<&str> = words[i + 1..].iter().take(size).copied().collect();
        let last = noun.last().copied().unwrap_or("");
        let bare = last.trim_end_matches([',', ';', '.', ':']);
        let tail = &last[bare.len()..];
        if out.last().is_some_and(|w| w.eq_ignore_ascii_case("the")) {
            // A later mention is the variable alone.
            out.pop();
            out.push(format!("{name}{tail}"));
        } else {
            out.extend(noun[..noun.len().saturating_sub(1)].iter().map(|w| w.to_string()));
            out.push(bare.to_string());
            out.push(format!("{name}{tail}"));
        }
        i += 1 + size;
    }
    out.join(" ")
}

/// The text without the marks of bound objects, as an author reads it.
/// `true` when a text holds the mark of a bound variable, as `without_binding_marks` removes it.
pub(crate) fn has_binding_mark(text: &str) -> bool {
    text.match_indices("`#").any(|(at, _)| text[at + 2..].split('`').next().is_some_and(|mark| mark.contains('@')))
}

pub(crate) fn without_binding_marks(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(at) = rest.find("`#") {
        out.push_str(&rest[..at]);
        match rest[at + 1..].find('`') {
            Some(end) => rest = rest[at + 1 + end + 1..].trim_start_matches(' '),
            None => {
                rest = &rest[at..];
                break;
            }
        }
    }
    out.push_str(rest);
    out
}

fn is_variable(word: &str) -> bool {
    let mut chars = word.chars();
    chars.next().is_some_and(|c| c.is_ascii_uppercase()) && chars.all(|c| c.is_ascii_digit())
}

const BINDER_DETS: [&str; 4] = ["a", "an", "each", "every"];
const BINDER_STOPS: [&str; 27] = ["shall", "must", "should", "may", "is", "are", "has", "have", "of", "to", "from", "for", "in", "on", "at", "by", "with", "and", "or", "then", "when", "while", "if", "where", "that", "which", "the"];
const ORDINALS: [&str; 5] = ["second", "third", "fourth", "fifth", "sixth"];

impl Vars {
    /// Replaces variables by the noun phrase they name, so that two statements
    /// about the same type read alike whatever letter each one chose.
    fn apply(&mut self, text: &str) -> Result<String, String> {
        let mut out: Vec<String> = Vec::new();
        let mut in_literal = false;
        let tokens: Vec<&str> = text.split_whitespace().collect();
        for (index, raw) in tokens.iter().copied().enumerate() {
            let opens = raw.starts_with('`');
            let closes = raw.ends_with('`') || raw.trim_end_matches([',', ';', '.', ':']).ends_with('`');
            if in_literal || (opens && !closes) || (opens && closes && raw.len() > 1) {
                in_literal = (in_literal || opens) && !closes;
                out.push(raw.to_string());
                continue;
            }
            let core = raw.trim_end_matches([',', ';', '.', ':']);
            let tail = &raw[core.len()..];
            if !is_variable(core) {
                out.push(raw.to_string());
                continue;
            }
            // A variable named `A` shares its spelling with the article: before
            // a noun it is the article, before a verb or at the end it is the variable.
            if core == "A" && tail.is_empty() && index == 0 && self.bound.contains_key(core) && article_before(tokens.get(index + 1).copied()) {
                out.push(raw.to_string());
                continue;
            }
            if let Some(noun) = self.bound.get(core) {
                out.push(format!("the {noun}{tail}"));
                continue;
            }
            if let Some((at, noun)) = binder_at(&out) {
                // `a report R` after the modal word, or in an item of a
                // composition, introduces one object of this activation.
                let indefinite = ["a", "an"].contains(&out[at].to_ascii_lowercase().as_str());
                let after_modal = out[..at].iter().any(|w| ["shall", "must", "should", "may"].contains(&w.as_str()));
                if indefinite && (self.in_response || after_modal) && !self.tag.is_empty() {
                    let mark = format!("`{BINDING_MARK}{core}@{}/{}`", self.tag, noun.split_whitespace().count());
                    out.insert(at + 1, mark.clone());
                    self.bound.insert(core.to_string(), format!("{mark} {noun}"));
                    if let Some(last) = out.last_mut() {
                        last.push_str(tail);
                    }
                    continue;
                }
                let used = self.bound.values().filter(|v| v.ends_with(&noun)).count();
                let noun = if used == 0 {
                    noun
                } else {
                    let ordinal = ORDINALS.get(used - 1).copied().unwrap_or("other");
                    out.insert(at + 1, ordinal.to_string());
                    format!("{ordinal} {noun}")
                };
                self.bound.insert(core.to_string(), noun);
                if let Some(last) = out.last_mut() {
                    last.push_str(tail);
                }
                continue;
            }
            if self.closed.contains(core) {
                return Err(format!("`{core}` was bound in another alternative and is local to it"));
            }
            out.push(raw.to_string());
        }
        Ok(out.join(" "))
    }

    fn close_alternative(&mut self, branch: &Vars) {
        for name in branch.bound.keys().filter(|name| !self.bound.contains_key(*name)) {
            self.closed.insert(name.clone());
        }
        self.closed.extend(branch.closed.iter().cloned());
    }
}

/// The population of a proportion in a sentence: `requests` in `for 99.9
/// percent of requests`.
fn proportion_population(sentence: &Sentence) -> Option<String> {
    let text = sentence.render();
    let lower = text.to_lowercase();
    let at = lower.find(" percent of ")?;
    let rest = &text[at + " percent of ".len()..];
    let words: Vec<&str> = rest.split_whitespace().take_while(|w| !["and", "or", "within", "for", "unless", "when", "while", "if"].contains(&w.to_lowercase().as_str())).collect();
    let name = words.join(" ");
    let name = name.trim_end_matches(['.', ',', ';']);
    let name = name.strip_prefix("the ").or_else(|| name.strip_prefix("all ")).unwrap_or(name);
    (!name.is_empty()).then(|| name.to_string())
}

/// A variable that stands where a noun phrase is expected and that no binder
/// replaced. A capital letter after a copula or inside a name is a value, and
/// those places hold no noun phrase.
fn unbound_variable(sentence: &Sentence) -> Option<String> {
    let tree = format!("{sentence:?}");
    const OPEN: &str = "Np { det: None, modifiers: [], head: \"";
    const CLOSE: &str = "\", of: None, relative: None, of_also: [], of_conj: None }";
    let mut rest = tree.as_str();
    while let Some(at) = rest.find(OPEN) {
        rest = &rest[at + OPEN.len()..];
        if let Some(end) = rest.find('"') {
            if is_variable(&rest[..end]) && rest[end..].starts_with(CLOSE) {
                return Some(rest[..end].to_string());
            }
        }
    }
    // `is part of the name of D` keeps its words.
    const OF: &str = "\"of\", \"";
    let mut rest = tree.as_str();
    while let Some(at) = rest.find(OF) {
        rest = &rest[at + OF.len()..];
        let name = rest.split('"').next().unwrap_or("");
        if is_variable(name) {
            return Some(name.to_string());
        }
    }
    None
}

/// `true` when the word after `A` is a noun that the article introduces.
fn article_before(next: Option<&str>) -> bool {
    const NOT_NOUNS: [&str; 34] = ["shall", "must", "should", "may", "is", "are", "has", "have", "means", "and", "or", "of", "to", "from", "for", "in", "on", "at", "by", "with", "as", "that", "which", "who", "whose", "when", "while", "unless", "until", "before", "after", "within", "into", "not"];
    let Some(next) = next else { return false };
    let word = next.trim_end_matches([',', ';', '.', ':']);
    let verbal = word.ends_with('s') && !word.ends_with("ss") && !word.ends_with("us") && !word.ends_with("is");
    word.chars().next().is_some_and(|c| c.is_ascii_lowercase()) && !NOT_NOUNS.contains(&word) && !verbal
}

impl Vars {
    /// Binds the variable of a `For each <noun phrase> X` head. The whole
    /// noun phrase is the type, with its `of`, `from` and `to` phrases:
    /// `For each adverb of time A`. Returns `false` when the head has another shape.
    fn bind_head(&mut self, head: &str) -> Result<bool, String> {
        let words: Vec<&str> = head.split_whitespace().collect();
        if words.len() < 4 {
            return Ok(false);
        }
        // One new variable stands in the head, after its noun or at the end.
        let fresh: Vec<usize> = (3..words.len()).filter(|&i| is_variable(words[i]) && !self.bound.contains_key(words[i])).collect();
        let [at] = fresh.as_slice() else { return Ok(false) };
        let phrase: Vec<&str> = words[2..].iter().enumerate().filter(|(i, _)| i + 2 != *at).map(|(_, w)| *w).collect();
        let noun = self.apply(&phrase.join(" "))?;
        let used = self.bound.values().filter(|v| v.ends_with(&noun)).count();
        let noun = if used == 0 { noun } else { format!("{} {noun}", ORDINALS.get(used - 1).copied().unwrap_or("other")) };
        self.bound.insert(words[*at].to_string(), noun);
        Ok(true)
    }
}

/// When the last words are `a <noun words>`, the index of the determiner and the noun.
fn binder_at(words: &[String]) -> Option<(usize, String)> {
    for at in (0..words.len()).rev() {
        let word = words[at].as_str();
        if word.ends_with(',') {
            return None;
        }
        let lower = word.to_ascii_lowercase();
        if BINDER_DETS.contains(&lower.as_str()) {
            return (at + 1 < words.len()).then(|| (at, words[at + 1..].join(" ")));
        }
        if BINDER_STOPS.contains(&lower.as_str()) || word.starts_with('`') {
            return None;
        }
    }
    None
}

/// The frames shared by the blocks around a statement.
#[derive(Debug, Clone, Default)]
struct Context {
    sections: Vec<String>,
    frames: Frames,
    vars: Vars,
    shared: bool,
    head_text: Vec<String>,
    head_lines: Vec<usize>,
}

const LIST_PHRASES: [(&str, ListKind); 4] = [
    ("perform all of the following actions", ListKind::All),
    ("perform one or more of the following actions", ListKind::Some),
    ("perform exactly one of the following actions", ListKind::One),
    ("perform the following actions in order", ListKind::Sequence),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ListKind {
    All,
    Some,
    One,
    Sequence,
}

fn list_phrase(text: &str) -> Option<(usize, ListKind, usize)> {
    LIST_PHRASES.iter().find_map(|(phrase, kind)| text.find(phrase).map(|at| (at, *kind, phrase.len())))
}

const FLOW_PHRASE: &str = "follow this flow";

struct Parser<'a> {
    lines: Vec<Line>,
    at: usize,
    file: &'a str,
    diags: Vec<Diagnostic>,
    /// The blocks that are open, outermost first.
    blocks: Vec<Block>,
    /// The indentation of the first line of the statement being read.
    stmt_indent: usize,
    closer: Line,
    /// Annotations written inside a composition or a diagram, for its statement.
    block_meta: Vec<Meta>,
    /// The refinement written inside a composition or a diagram, for its statement.
    block_details: Vec<String>,
    /// The priority lines written inside a composition or a diagram.
    block_rank: Rank,
    /// The elements of the diagram being read, for its statement.
    block_elements: Vec<Element>,
    /// The diagram kinds that the file has declared so far.
    kinds: Vec<DiagramKind>,
    /// The kind of the diagram being read.
    block_kind: Option<String>,
    /// The extent of the sentence being read.
    column: usize,
    end_line: usize,
    shares_line: bool,
}

/// The byte ranges of the sentences of a paragraph. A sentence ends with a
/// period that white space or the end of the paragraph follows; a final range
/// may instead end with the `:` of a block header.
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

/// How a statement ranks against the statements that conflict with it.
#[derive(Debug, Clone, Default)]
struct Rank {
    overrides: Vec<String>,
    default: bool,
    weight: Option<u32>,
}

impl Rank {
    fn merge(&mut self, other: Rank) {
        self.overrides.extend(other.overrides);
        self.default |= other.default;
        self.weight = other.weight.or(self.weight);
    }
}

/// What closes a block. A block with a colon holds the lines that are indented
/// more than its header. A flat namespace or section has no colon and runs to
/// the next header of its kind.
#[derive(Debug, Clone, Copy)]
enum Block {
    Indent(usize),
    FlatNamespace(usize),
    FlatSection(usize),
}

impl Block {
    fn closes_before(self, next: Option<&Line>) -> bool {
        let Some(next) = next else { return true };
        match self {
            Block::Indent(header) => next.indent <= header,
            Block::FlatNamespace(header) => next.indent < header || (next.indent == header && keyword(&next.text, "namespace").is_some()),
            Block::FlatSection(header) => next.indent < header || (next.indent == header && keyword(&next.text, "section").is_some()),
        }
    }
}

/// The line that the parser reads where a block closes. No source line can spell it.
const END: &str = "\u{1}end";

enum BlockEnd {
    Closed,
    EndOfFile,
}

impl<'a> Parser<'a> {
    fn error(&mut self, code: &str, message: impl Into<String>, line: usize, text: &str) {
        let at = SpecRef { id: format!("{}:{line}", self.file), file: self.file.to_string(), line, text: text.to_string() };
        self.diags.push(Diagnostic::error(code, message, vec![at]));
    }

    fn closing(&self) -> bool {
        let next = self.lines.get(self.at);
        self.blocks.iter().any(|block| block.closes_before(next))
    }

    /// Opens a block under the statement being read.
    fn open(&mut self) {
        self.blocks.push(Block::Indent(self.stmt_indent));
    }

    fn peek(&self) -> Option<&Line> {
        if self.closing() {
            return Some(&self.closer);
        }
        self.lines.get(self.at)
    }

    fn next_text(&mut self) -> Option<(usize, usize, String)> {
        if self.closing() {
            self.blocks.pop();
            let no = self.lines.get(self.at.wrapping_sub(1)).map_or(0, |l| l.no);
            return Some((no, 0, END.to_string()));
        }
        let line = self.lines.get(self.at)?;
        let item = (line.no, line.indent, line.text.clone());
        self.at += 1;
        Some(item)
    }

    /// Inside a composition or a diagram: reads an annotation of its statement,
    /// and rejects a written `end`. Returns `true` when the line is consumed.
    fn block_line(&mut self, text: &str, line: usize) -> bool {
        if text == "end" || text == "end;" {
            self.error("parse-block", "a block closes where its indentation ends: `end` is not written", line, text);
            return true;
        }
        if text.starts_with("cite ") || text.starts_with("unsourced ") {
            if let Some(meta) = self.annotation(text, line) {
                self.block_meta.push(meta);
            }
            return true;
        }
        if let Some(rest) = keyword(text, "detailed") {
            let details = self.details(rest, line, text);
            self.block_details.extend(details);
            return true;
        }
        if let Some(rank) = self.rank(text, line) {
            self.block_rank.merge(rank);
            return true;
        }
        false
    }

    /// `overrides [ID], [ID]`, `default` or `weight N`: how a statement ranks
    /// against the statements that conflict with it.
    fn rank(&mut self, text: &str, line: usize) -> Option<Rank> {
        if text == "default" {
            return Some(Rank { default: true, ..Rank::default() });
        }
        if let Some(rest) = keyword(text, "overrides").filter(|rest| rest.starts_with('[') || !rest.contains(char::is_whitespace)) {
            return Some(match bracket_list(rest).filter(|ids| !ids.is_empty()) {
                Some(overrides) => Rank { overrides, ..Rank::default() },
                None => {
                    self.error("parse-priority", "write `overrides [ID], [ID]`", line, text);
                    Rank::default()
                }
            });
        }
        if let Some(rest) = keyword(text, "weight").filter(|rest| rest.chars().all(|c| c.is_ascii_digit() || c == '-')) {
            return Some(match rest.trim().parse::<u32>().ok().filter(|n| *n > 0) {
                Some(weight) => Rank { weight: Some(weight), ..Rank::default() },
                None => {
                    self.error("parse-priority", "write `weight N` with a whole number above zero", line, text);
                    Rank::default()
                }
            });
        }
        None
    }

    fn element(&mut self, kind: &str, name: &str, id: Option<String>, line: usize, text: &str) {
        self.block_elements.push(Element { kind: kind.to_string(), name: name.trim().to_string(), id, line, text: text.trim().to_string() });
    }

    /// `detailed by [ID], [ID]`: the statements that say what a statement means in detail.
    fn details(&mut self, rest: &str, line: usize, text: &str) -> Vec<String> {
        match keyword(rest, "by").and_then(bracket_list).filter(|ids| !ids.is_empty()) {
            Some(ids) => ids,
            None => {
                self.error("parse-refinement", "write `detailed by [ID], [ID]`", line, text);
                Vec::new()
            }
        }
    }

    /// What is unique to the bindings of the statement at a line of this file.
    fn binding_tag(&self, id: Option<&str>, line: usize) -> String {
        // An identified statement keeps its bindings wherever it is written.
        if let Some(id) = id {
            return id.to_string();
        }
        let stem = self.file.rsplit('/').next().unwrap_or(self.file).trim_end_matches(".trion");
        let stem: String = stem.chars().filter(|c| c.is_ascii_alphanumeric() || *c == '-').collect();
        format!("{stem}:{line}")
    }

    /// Reports and skips a block whose header could not be read.
    fn skip_block(&mut self) {
        self.open();
        while let Some((_, _, text)) = self.next_text() {
            if text == END {
                return;
            }
        }
    }

    /// Joins the lines of one sentence up to its terminator.
    fn gather(&mut self, first: String) -> String {
        self.gather_located(first, 0, 0).0
    }

    /// Joins the lines of a paragraph up to a line that ends a sentence, and
    /// returns where each line begins: its offset in the text, its number and
    /// its indentation.
    fn gather_located(&mut self, first: String, line: usize, indent: usize) -> (String, Vec<(usize, usize, usize)>) {
        let mut text = first;
        let mut starts = vec![(0, line, indent)];
        while !matches!(last_significant(&text), Some('.' | ':' | ';')) {
            match self.peek() {
                Some(next) if next.text != END => {
                    text.push(' ');
                    starts.push((text.len(), next.no, next.indent));
                    text.push_str(&next.text);
                    self.at += 1;
                }
                _ => break,
            }
        }
        (text, starts)
    }

    fn sentence_error(&mut self, error: &ParseError, line: usize, text: &str) {
        if text.chars().any(|c| c.is_alphabetic() && !c.is_ascii()) && !text.contains('`') {
            self.error("NOT_CONTROLLED_ENGLISH", "a normative sentence is written in the controlled English grammar", line, text);
        } else if matches!(error, ParseError::UnresolvedPronoun { .. }) {
            self.error("UNRESOLVED_REFERENCE", error.to_string(), line, text);
        } else if matches!(error, ParseError::AmbiguousPronoun { .. }) {
            self.error("AMBIGUOUS_REFERENCE", error.to_string(), line, text);
        } else if matches!(error, ParseError::UnsupportedProportion) {
            self.error("UNSUPPORTED_SEMANTICS", error.to_string(), line, text);
        } else if matches!(error, ParseError::MissingPivot) {
            self.error("MISSING_PREDICATE", error.to_string(), line, text);
        } else if matches!(error, ParseError::DeniedConjunction) {
            self.error("composite-not-distributive", error.to_string(), line, text);
        } else if matches!(error, ParseError::UngroupedResponseOperators) {
            self.error("UNGROUPED_RESPONSE_OPERATORS", error.to_string(), line, text);
        } else {
            self.error("parse-sentence", error.to_string(), line, text);
        }
    }

    fn parse_english(&mut self, text: &str, line: usize, authored: &str) -> Option<Sentence> {
        match single_sentence(text) {
            Ok(mut sentence) => {
                sentence.source = String::new();
                if let Some(name) = unbound_variable(&sentence) {
                    self.error("UNBOUND_VARIABLE", format!("`{name}` is not bound here: `a <type> {name}` binds it within its sentence or composition, and `For each <type> {name}:` binds it within a block"), line, authored);
                    return None;
                }
                sentence.source = authored.to_string();
                Some(sentence)
            }
            Err(error) => {
                self.sentence_error(&error, line, authored);
                None
            }
        }
    }

    fn head_frames(&mut self, head: &str, vars: &mut Vars, line: usize) -> Option<Frames> {
        let literal = literals_as_backticks(head);
        let replaced = match vars.apply(&literal) {
            Ok(text) => text,
            Err(message) => {
                self.error("UNRESOLVED_REFERENCE", message, line, head);
                return None;
            }
        };
        let completion = if replaced.ends_with("then") { " the x shall y." } else { ", the x shall y." };
        let sentence = self.parse_english(&format!("{replaced}{completion}"), line, head)?;
        Some(sentence.frames)
    }

    fn merge_frames(&mut self, target: &mut Frames, extra: &Frames, line: usize, text: &str) {
        let mut scopes = extra.scopes.clone();
        scopes.append(&mut target.scopes);
        target.scopes = scopes;
        let mut states = extra.states.clone();
        states.append(&mut target.states);
        target.states = states;
        match (&target.trigger, &extra.trigger) {
            (Some(_), Some(_)) => self.error("context-second-trigger", "a response inherits at most one event or unwanted trigger", line, text),
            (None, Some(trigger)) => target.trigger = Some(trigger.clone()),
            _ => {}
        }
    }

    fn check_id(&mut self, id: &str, line: usize, text: &str) {
        if !is_stable_id(id) {
            self.error("parse-spec-id", "a stable identifier is an uppercase letter, then uppercase letters, digits or hyphens, with an optional slash and a lowercase component", line, text);
        }
    }

    /// Splits a leading `[ID]` from a line.
    fn take_id(&mut self, text: String, line: usize) -> (Option<String>, String) {
        let Some(rest) = text.strip_prefix('[') else { return (None, text) };
        let Some((id, body)) = rest.split_once(']') else {
            self.error("parse-spec-id", "an identifier is closed with `]`", line, &text);
            return (None, String::new());
        };
        let id = id.to_string();
        self.check_id(&id, line, &text);
        (Some(id), body.trim().to_string())
    }

    fn statement_after_id(&mut self, body: String) -> Option<(usize, usize, String)> {
        if body.is_empty() {
            self.next_text()
        } else {
            Some((0, 0, body))
        }
    }

    fn push_spec(&mut self, doc: &mut Document, ctx: &Context, id: Option<String>, mut sentence: Sentence, line: usize, parts: Vec<String>, expansion: Option<String>, otherwise: bool) {
        let authored = sentence.source.clone();
        if ctx.shared {
            if matches!(sentence.core, Core::Definition { .. }) {
                self.error("definition-in-context", "a definition is declared outside every shared context", line, &sentence.source);
                return;
            }
            let frames = ctx.frames.clone();
            let source = sentence.source.clone();
            self.merge_frames(&mut sentence.frames, &frames, line, &source);
        }
        // A share of a population is a quantity only when the population is a declared measure.
        if let Some(population) = proportion_population(&sentence) {
            if !doc.measures.iter().any(|m| m.name.eq_ignore_ascii_case(&population)) {
                self.error("UNSUPPORTED_SEMANTICS", format!("a proportion of `{population}` has no formal reading without a measure: declare `measure {population}` before the statement, and the share becomes a quantity between 0 and 100 percent"), line, &sentence.source);
                return;
            }
        }
        // Composite vocabulary abbreviates several sentences: each becomes a
        // statement of its own, and no statement holds composite vocabulary.
        let simple = match crate::syntax::composite::expand(&sentence) {
            Ok(simple) => simple,
            Err(refused) => {
                self.error("composite-not-distributive", refused.reason, line, &sentence.source);
                return;
            }
        };
        let end_line = self.end_line.max(line);
        let meta = std::mem::take(&mut self.block_meta);
        let elements = std::mem::take(&mut self.block_elements);
        let diagram = self.block_kind.clone();
        let details = std::mem::take(&mut self.block_details);
        let rank = std::mem::take(&mut self.block_rank);
        let composite = simple.len() > 1;
        if let (true, Some(id)) = (composite, &id) {
            // The identifier of the sentence is the parent of the identifier of each part.
            doc.references.push((format!("concept:{id}"), line));
        }
        for (number, sentence) in simple.into_iter().enumerate() {
            let abbreviates = composite.then(|| (authored.clone(), number + 1));
            let id = match (&id, composite) {
                (Some(id), true) => Some(format!("{id}/{}", number + 1)),
                (id, _) => id.clone(),
            };
            doc.specs.push(Spec { overrides: rank.overrides.clone(), default: rank.default, weight: rank.weight, details: details.clone(), elements: elements.clone(), diagram: diagram.clone(), id, sentence, meta: meta.clone(), file: self.file.to_string(), line, sections: ctx.sections.clone(), parts: parts.clone(), expansion: expansion.clone(), otherwise, column: self.column, end_line, shares_line: self.shares_line, scopes: ctx.head_text.clone(), scope_lines: ctx.head_lines.clone(), abbreviates });
        }
    }

    /// A statement that ends with `.`, including `If C, then A; otherwise, B.`
    fn plain_statement(&mut self, doc: &mut Document, ctx: &Context, id: Option<String>, text: &str, line: usize) {
        let authored = text.split_whitespace().collect::<Vec<_>>().join(" ");
        let mut vars = ctx.vars.clone();
        vars.tag = self.binding_tag(id.as_deref(), line);
        let mut literal = literals_as_backticks(&authored);
        // `For each request R, the API shall log R.` is the block form on one line:
        // the frame binds its variable for this sentence and adds no condition.
        if let Some((head, rest)) = literal.strip_prefix("For each ").and_then(|after| after.split_once(", ")).map(|(head, rest)| (head.to_string(), rest.to_string())) {
            if !head.contains('`') {
                if let Err(message) = vars.bind_head(&format!("For each {head}")) {
                    self.error("UNRESOLVED_REFERENCE", message, line, &authored);
                    return;
                }
                let mut first = rest.chars();
                literal = first.next().map(|c| c.to_uppercase().chain(first).collect()).unwrap_or_default();
            }
        }
        let replaced = match vars.apply(&literal) {
            Ok(text) => text,
            Err(message) => {
                self.error("UNRESOLVED_REFERENCE", message, line, &authored);
                return;
            }
        };
        if let Some((first, second)) = replaced.split_once("; otherwise, ") {
            self.otherwise_statement(doc, ctx, id, first, second, line, &authored);
            return;
        }
        if replaced.contains(';') {
            self.error("parse-sentence", "`;` ends an item of an action list", line, &authored);
            return;
        }
        if let Some(sentence) = self.parse_english(&replaced, line, &authored) {
            self.push_spec(doc, ctx, id, sentence, line, vec![], None, false);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn otherwise_statement(&mut self, doc: &mut Document, ctx: &Context, id: Option<String>, first: &str, second: &str, line: usize, authored: &str) {
        let Some(sentence) = self.parse_english(&format!("{first}."), line, authored) else { return };
        if sentence.frames.trigger.is_none() {
            self.error("parse-sentence", "`otherwise` follows a condition opened by `If` or `When`", line, authored);
            return;
        }
        let tail = second.trim_end_matches('.');
        let Some(mut branch) = self.parse_english(&format!("{tail}."), line, authored) else { return };
        branch.frames = sentence.frames.clone();
        let branch_id = id.as_ref().map(|i| format!("{i}/otherwise"));
        self.push_spec(doc, ctx, id, sentence, line, vec![], None, false);
        self.push_spec(doc, ctx, branch_id, branch, line, vec![], None, true);
    }

    fn head_sentence(&mut self, head: &str, vars: &mut Vars, line: usize, authored: &str) -> Option<Sentence> {
        let replaced = match vars.apply(&literals_as_backticks(head)) {
            Ok(text) => text,
            Err(message) => {
                self.error("UNRESOLVED_REFERENCE", message, line, authored);
                return None;
            }
        };
        self.parse_english(&replaced, line, authored)
    }

    /// Reads the verb phrase of an item.
    fn item_vp(&mut self, text: &str, vars: &mut Vars, leaves: &mut Vec<Vp>, line: usize) -> Option<CompNode> {
        vars.in_response = true;
        let literal = literals_as_backticks(text);
        let replaced = match vars.apply(&literal) {
            Ok(text) => text,
            Err(message) => {
                self.error("UNRESOLVED_REFERENCE", message, line, text);
                return None;
            }
        };
        let sentence = self.parse_english(&format!("The x shall {replaced}."), line, text)?;
        let Core::Deontic { vp, .. } = sentence.core else { return None };
        let exception = sentence.exception;
        let mut leaf = |vp: Vp, exception: Option<Clause>| {
            leaves.push(vp);
            CompNode::Leaf { index: leaves.len() - 1, exception }
        };
        Some(match vp {
            VpGroup::Single(vp) => leaf(vp, exception),
            VpGroup::Alternatives { items } => CompNode::Some { items: items.into_iter().map(|v| leaf(v, exception.clone())).collect() },
            VpGroup::All { items, .. } => CompNode::All { items: items.into_iter().map(|v| leaf(v, exception.clone())).collect() },
            VpGroup::Composite(_) => return None,
        })
    }

    /// Reads action-list items up to `end`.
    fn list_items(&mut self, kind: ListKind, parent_id: Option<&str>, vars: &mut Vars, leaves: &mut Vec<Vp>, parts: &mut Vec<String>) -> Vec<CompNode> {
        let mut items = Vec::new();
        self.open();
        while let Some((line, indent, text)) = self.next_text() {
            if text == END {
                return items;
            }
            self.stmt_indent = indent;
            if self.block_line(&text, line) {
                continue;
            }
            let (id, body) = self.take_id(text, line);
            let Some((line, _, body)) = self.statement_after_id(body).map(|(l, i, b)| (if l == 0 { line } else { l }, i, b)) else { break };
            let body = self.gather(body);
            if let Some(id) = &id {
                if !parent_id.is_some_and(|p| id.starts_with(&format!("{p}/"))) {
                    // An item outside a named parent keeps its own identifier.
                    if parent_id.is_some() {
                        self.error("parse-spec-id", format!("the item `{id}` is named under its parent"), line, &body);
                    }
                }
                parts.push(id.clone());
            }
            // One branch cannot see what another introduces.
            let mut branch = vars.clone();
            let scope: &mut Vars = if kind == ListKind::Sequence { vars } else { &mut branch };
            let node = if last_significant(&body) == Some(':') {
                let phrase = body.trim_end_matches(':').trim();
                match LIST_PHRASES.iter().find(|(p, _)| *p == phrase) {
                    Some((_, nested)) => {
                        let nested_items = self.list_items(*nested, parent_id, scope, leaves, parts);
                        Some(list_node(*nested, nested_items))
                    }
                    None => {
                        self.error("parse-composition", "a nested item begins with one of the four `perform` phrases", line, &body);
                        self.skip_block();
                        None
                    }
                }
            } else if last_significant(&body) == Some(';') {
                self.item_vp(body.trim_end_matches(';').trim(), scope, leaves, line)
            } else {
                self.error("parse-composition", "an action item ends with `;`", line, &body);
                None
            };
            if kind != ListKind::Sequence {
                vars.close_alternative(&branch);
            }
            items.extend(node);
        }
        self.error("parse-block", "an action list is closed with `end`", self.lines.last().map_or(0, |l| l.no), "");
        items
    }

    fn action_list(&mut self, doc: &mut Document, ctx: &Context, id: Option<String>, text: &str, line: usize, at: usize, kind: ListKind, phrase_len: usize) {
        let authored = text.split_whitespace().collect::<Vec<_>>().join(" ");
        let tail = text[at + phrase_len..].trim_end_matches(':').trim();
        let head = format!("{}perform the listed actions{tail}.", &text[..at]);
        let mut vars = ctx.vars.clone();
        vars.tag = self.binding_tag(id.as_deref(), line);
        let Some(mut sentence) = self.head_sentence(&head, &mut vars, line, &authored) else {
            self.skip_block();
            return;
        };
        let mut leaves = Vec::new();
        let mut parts = Vec::new();
        let items = self.list_items(kind, id.as_deref(), &mut vars, &mut leaves, &mut parts);
        if items.is_empty() {
            self.error("parse-composition", "an action list holds at least one item", line, &authored);
            return;
        }
        let composition = Composition { root: list_node(kind, items), leaves };
        if let Core::Deontic { vp, .. } = &mut sentence.core {
            *vp = VpGroup::Composite(Box::new(composition));
        }
        self.end_line = self.lines.get(self.at.wrapping_sub(1)).map_or(line, |l| l.no);
        self.push_spec(doc, ctx, id, sentence, line, parts, None, false);
    }

    fn flow(&mut self, doc: &mut Document, ctx: &Context, id: Option<String>, text: &str, line: usize, at: usize) {
        let authored = text.split_whitespace().collect::<Vec<_>>().join(" ");
        let head = format!("{}perform the listed actions.", &text[..at]);
        let mut vars = ctx.vars.clone();
        vars.tag = self.binding_tag(id.as_deref(), line);
        let Some(mut sentence) = self.head_sentence(&head, &mut vars, line, &authored) else {
            self.skip_block();
            return;
        };
        if sentence.frames.trigger.is_none() && ctx.frames.trigger.is_none() {
            self.error("parse-flow", "a flow responds to a trigger: open the head with `When` or `If`, or place the flow in a context that has one", line, &authored);
        }
        let mut leaves = Vec::new();
        let mut parts = Vec::new();
        let mut flow = Flow { steps: vec![], start: String::new(), finish: vec![], edges: vec![], choices: vec![] };
        let mut starts: Vec<String> = Vec::new();
        self.open();
        while let Some((no, indent, raw)) = self.next_text() {
            if raw == END {
                break;
            }
            self.stmt_indent = indent;
            if self.block_line(&raw, no) {
                continue;
            }
            let (step_id, raw) = self.take_id(raw, no);
            if let Some(rest) = keyword(&raw, "step") {
                let body = self.gather(rest.to_string());
                let Some((name, action)) = body.split_once(':') else {
                    self.error("parse-flow", "write `step <name>: <action>;`", no, &raw);
                    continue;
                };
                if !is_component(name.trim()) {
                    self.error("parse-flow", "a step name is a lowercase component name", no, &raw);
                }
                if flow.steps.iter().any(|s: &FlowStep| s.name == name.trim()) {
                    self.error("FLOW_BAD_REFERENCE", format!("the step `{}` is declared twice", name.trim()), no, &raw);
                    continue;
                }
                if last_significant(action) != Some(';') {
                    self.error("parse-flow", "a step ends with `;`", no, &raw);
                    continue;
                }
                self.element("step", name.trim(), step_id.clone(), no, &format!("step {}", body.trim()));
                if let Some(step_id) = step_id {
                    parts.push(step_id);
                }
                if let Some(node) = self.item_vp(action.trim().trim_end_matches(';').trim(), &mut vars, &mut leaves, no) {
                    flow.steps.push(FlowStep { name: name.trim().to_string(), node });
                }
            } else if let Some(rest) = keyword(&raw, "start") {
                self.element("start", rest, None, no, &raw);
                starts.push(rest.to_string());
            } else if let Some(rest) = keyword(&raw, "finish") {
                self.element("finish", rest, None, no, &raw);
                flow.finish.push(rest.to_string());
            } else if let Some(rest) = keyword(&raw, "choose after") {
                let Some(after) = rest.strip_suffix(':') else {
                    self.error("parse-flow", "write `choose after <step>:`", no, &raw);
                    continue;
                };
                let choice = self.choice(after.trim(), &mut vars);
                flow.choices.push(choice);
            } else if let Some((from, to)) = raw.split_once("->") {
                self.element("edge", &format!("{} -> {}", from.trim(), to.trim()), None, no, &raw);
                flow.edges.push((from.trim().to_string(), to.trim().to_string()));
            } else {
                self.error("parse-flow", "a flow holds steps, one start, edges, choices and finishes", no, &raw);
            }
        }
        if starts.len() != 1 {
            self.error("FLOW_START", "a flow has exactly one start", line, &authored);
        }
        flow.start = starts.into_iter().next().unwrap_or_default();
        if let Some(message) = flow_problem(&flow) {
            let code = if message.starts_with("cycle") { "UNSUPPORTED_FLOW_CYCLE" } else { "FLOW_BAD_REFERENCE" };
            self.error(code, message, line, &authored);
        }
        let composition = Composition { root: CompNode::Flow(Box::new(flow)), leaves };
        if let Core::Deontic { vp, .. } = &mut sentence.core {
            *vp = VpGroup::Composite(Box::new(composition));
        }
        self.end_line = self.lines.get(self.at.wrapping_sub(1)).map_or(line, |l| l.no);
        self.push_spec(doc, ctx, id, sentence, line, parts, None, false);
    }

    fn choice(&mut self, after: &str, vars: &mut Vars) -> FlowChoice {
        let mut choice = FlowChoice { after: after.to_string(), arms: vec![], otherwise: None };
        self.open();
        while let Some((no, _, raw)) = self.next_text() {
            if raw == END {
                break;
            }
            if let Some(rest) = keyword(&raw, "when") {
                let Some((condition, target)) = rest.rsplit_once("->") else {
                    self.error("parse-flow", "write `when <condition> -> <step>`", no, &raw);
                    continue;
                };
                let mut guard_vars = vars.clone();
                if let Some(frames) = self.head_frames(&format!("When {}", condition.trim()), &mut guard_vars, no) {
                    if let Some(trigger) = frames.trigger {
                        self.element("guard", &format!("{after} -> {}", target.trim()), None, no, &raw);
                        choice.arms.push((trigger.clause, target.trim().to_string()));
                    }
                }
            } else if let Some(target) = raw.strip_prefix("otherwise").and_then(|r| r.trim().strip_prefix("->")) {
                self.element("otherwise", &format!("{after} -> {}", target.trim()), None, no, &raw);
                choice.otherwise = Some(target.trim().to_string());
            } else {
                self.error("parse-flow", "a choice holds `when ... -> ...` and `otherwise -> ...`", no, &raw);
            }
        }
        choice
    }

    fn concept(&mut self, doc: &mut Document, ctx: &Context, id: Option<String>, line: usize) {
        let mut lowered = Vec::new();
        self.open();
        while let Some((no, _, raw)) = self.next_text() {
            if raw == END {
                break;
            }
            if self.block_line(&raw, no) {
                continue;
            }
            let (edge_id, body) = self.take_id(raw, no);
            let Some(edge) = body.strip_suffix(';') else {
                self.error("parse-concept", "a concept edge ends with `;`", no, &body);
                continue;
            };
            let pieces: Vec<&str> = edge.split("->").map(str::trim).collect();
            let [from, relation, to] = pieces.as_slice() else {
                self.error("parse-concept", "write `each <type> -> <relation> -> <cardinality> <type>;`", no, &body);
                continue;
            };
            if !from.starts_with("each ") {
                self.error("parse-concept", "a concept edge begins with `each`", no, &body);
                continue;
            }
            let mut chars = from.chars();
            let upper: String = chars.next().map(|c| c.to_ascii_uppercase()).into_iter().chain(chars).collect();
            let text = format!("{upper} {relation} {to}.");
            lowered.push(text.clone());
            let display = edge_id.or_else(|| id.as_ref().map(|i| format!("{i}/{}", lowered.len())));
            if let Some(sentence) = self.parse_english(&text, no, &text) {
                let source = from.strip_prefix("each ").unwrap_or(from);
                self.element("node", source, None, no, from);
                self.element("label", relation, None, no, relation);
                self.element("node", to, None, no, to);
                self.element("edge", &format!("{source} -> {to}"), display.clone(), no, &body);
                self.push_spec(doc, ctx, display, sentence, no, vec![], Some(text), false);
            }
        }
        // The diagram as a whole is the conjunction of its edges: its identifier
        // is the parent of every generated statement.
        if let Some(id) = id {
            doc.references.push((format!("concept:{id}"), line));
        }
    }

    /// `compatibility NAME:` names the source, its revision and the covered forms.
    fn compatibility_block(&mut self, doc: &mut Document, name: &str, line: usize, header: &str) {
        let mut claim = CompatibilityClaim { name: name.to_string(), source: String::new(), revision: String::new(), forms: vec![], file: self.file.to_string(), line };
        for (no, raw) in self.fields() {
            if let Some(source) = keyword(&raw, "source").filter(|s| is_metadata_name(s.trim())) {
                claim.source = source.trim().to_string();
            } else if let Some(revision) = keyword(&raw, "revision").and_then(whole_string) {
                claim.revision = revision;
            } else if let Some(form) = keyword(&raw, "form").map(str::trim).filter(|f| SENTENCE_FORMS.contains(f)) {
                claim.forms.push(form.to_string());
            } else {
                self.error("parse-compatibility", format!("a compatibility claim holds `source NAME`, `revision \"...\"` and `form` lines with one of {}", SENTENCE_FORMS.join(", ")), no, &raw);
            }
        }
        if claim.source.is_empty() || claim.revision.trim().is_empty() || claim.forms.is_empty() {
            self.error("parse-compatibility", "a compatibility claim identifies its source, the revision of that source, and the sentence forms that it covers", line, header);
            return;
        }
        doc.compatibility.push(claim);
    }

    /// `diagram kind NAME:` declares the element grammar, the typing rules,
    /// the expansion and the meaning-preservation contract of a kind.
    fn diagram_kind(&mut self, doc: &mut Document, name: &str, line: usize, header: &str) {
        let mut kind = DiagramKind { name: name.to_string(), element: String::new(), types: vec![], expansion: String::new(), preserves: String::new(), file: self.file.to_string(), line };
        let mut seen = Vec::new();
        for (no, raw) in self.fields() {
            let field = ["element", "types", "expansion", "preserves"].into_iter().find_map(|f| Some((f, whole_string(keyword(&raw, f)?)?)));
            let Some((field, value)) = field else {
                self.error("parse-diagram-kind", "a diagram kind holds `element`, `types`, `expansion` and `preserves`, each with a quoted string", no, &raw);
                continue;
            };
            seen.push(field);
            match field {
                "element" => kind.element = value,
                "expansion" => kind.expansion = value,
                "preserves" => kind.preserves = value,
                _ => {
                    for part in value.split(',') {
                        match part.split_once(':').map(|(n, k)| (n.trim().trim_start_matches('$').to_string(), k.trim().to_string())) {
                            Some((n, k)) if ["entity", "object", "attribute", "value", "action"].contains(&k.as_str()) => kind.types.push((n, k)),
                            _ => self.error("parse-diagram-kind", "a typing rule is `$name: entity|object|attribute|value|action`", no, &raw),
                        }
                    }
                }
            }
        }
        let parts = placeholders(&kind.element);
        let complete = ["element", "types", "expansion", "preserves"].iter().all(|f| seen.contains(f)) && !kind.preserves.trim().is_empty();
        let typed = !parts.is_empty() && parts.iter().all(|p| kind.types.iter().any(|(n, _)| n == p));
        let bound = placeholders(&kind.expansion).iter().all(|p| parts.contains(p));
        if !is_component(name) || !complete || !typed || !bound {
            self.error("parse-diagram-kind", "a diagram kind declares its element grammar, a type for each placeholder, an expansion over those placeholders, and its meaning-preservation contract", line, header);
            return;
        }
        if self.kinds.iter().any(|k| k.name == kind.name) || ["concept", "flow", "kind"].contains(&name) {
            self.error("parse-diagram-kind", format!("the diagram kind `{name}` is already declared"), line, header);
            return;
        }
        doc.diagram_kinds.push(kind.clone());
        self.kinds.push(kind);
    }

    /// A diagram of a declared kind: each element is the sentence that the
    /// expansion of the kind gives it, read by the same parser as English.
    fn declared_diagram(&mut self, doc: &mut Document, ctx: &Context, id: Option<String>, kind: &DiagramKind, line: usize) {
        let mut count = 0;
        self.open();
        while let Some((no, _, raw)) = self.next_text() {
            if raw == END {
                break;
            }
            if self.block_line(&raw, no) {
                continue;
            }
            let (element_id, body) = self.take_id(raw, no);
            let Some(bound) = match_element(&kind.element, &body) else {
                self.error("parse-diagram", format!("an element of the diagram kind `{}` is written `{}`", kind.name, kind.element), no, &body);
                continue;
            };
            let mut text = kind.expansion.clone();
            let mut names: Vec<&(String, String)> = bound.iter().collect();
            names.sort_by_key(|(name, _)| std::cmp::Reverse(name.len()));
            for (name, value) in names {
                text = text.replace(&format!("${name}"), value);
            }
            let mut chars = text.chars();
            let text: String = chars.next().map(|c| c.to_ascii_uppercase()).into_iter().chain(chars).collect();
            count += 1;
            let display = element_id.or_else(|| id.as_ref().map(|i| format!("{i}/{count}")));
            if let Some(sentence) = self.parse_english(&literals_as_backticks(&text), no, &text) {
                for (name, value) in &bound {
                    let declared = kind.types.iter().find(|(n, _)| n == name).map(|(_, k)| k.clone()).unwrap_or_default();
                    self.element("node", value, None, no, &format!("${name}: {declared}"));
                    doc.vocabulary.push(VocabDecl { term: value.clone(), kind: declared, file: self.file.to_string(), line: no });
                }
                self.element("edge", &body, display.clone(), no, &body);
                self.block_kind = Some(kind.name.clone());
                self.push_spec(doc, ctx, display, sentence, no, vec![], Some(text), false);
                self.block_kind = None;
            }
        }
        if let Some(id) = id {
            doc.references.push((format!("concept:{id}"), line));
        }
    }

    fn fields(&mut self) -> Vec<(usize, String)> {
        self.block_lines().into_iter().map(|(line, _, text)| (line, text)).collect()
    }

    fn block_lines(&mut self) -> Vec<(usize, usize, String)> {
        let mut out = Vec::new();
        self.open();
        while let Some((line, indent, text)) = self.next_text() {
            if text == END {
                break;
            }
            out.push((line, indent, text));
        }
        out
    }

    fn check_block(&mut self, doc: &mut Document, name: &str, line: usize) {
        let fields = self.fields();
        if fields.iter().any(|(_, raw)| keyword(raw, "grammar").is_some() || keyword(raw, "input").is_some()) {
            self.propositional_check(doc, name, line, fields);
            return;
        }
        let mut check = Check { name: name.to_string(), relation: String::new(), left: vec![], right: vec![], malformed: false, file: self.file.to_string(), line };
        let mut using = false;
        for (no, raw) in fields {
            if let Some(rest) = keyword(&raw, "relation") {
                check.relation = rest.to_string();
            } else if let Some(rest) = keyword(&raw, "left") {
                check.left = self.references(rest, no);
            } else if let Some(rest) = keyword(&raw, "right") {
                check.right = self.references(rest, no);
            } else if raw == "using definitions" {
                using = true;
            } else {
                check.malformed = true;
                self.error("parse-check", "a check holds relation, left, right and using fields", no, &raw);
            }
        }
        if check.relation != "equivalent" {
            check.malformed = true;
            self.error("parse-check", "this edition accepts `equivalent` as the relation of a check", line, name);
        }
        if check.left.is_empty() || check.right.is_empty() || !using {
            check.malformed = true;
            self.error("parse-check", "a check holds relation, left, right and using fields", line, name);
        }
        doc.checks.push(check);
    }

    fn propositional_check(&mut self, doc: &mut Document, name: &str, line: usize, fields: Vec<(usize, String)>) {
        let mut grammar = None;
        let mut input = None;
        for (no, raw) in fields {
            if let Some(version) = keyword(&raw, "grammar").and_then(whole_string).filter(|_| grammar.is_none()) {
                grammar = Some(version);
            } else if let Some(source) = keyword(&raw, "input").and_then(whole_string).filter(|_| input.is_none()) {
                input = Some((no, source));
            } else {
                self.error("parse-check", "a propositional check holds one quoted grammar and one quoted input", no, &raw);
                return;
            }
        }
        let (Some(grammar), Some((input_line, source))) = (grammar, input) else {
            self.error("parse-check", "a propositional check requires a grammar version and an input", line, name);
            return;
        };
        let input = match trion_cnl::formalize_version(&source, Some(&grammar)) {
            Ok(accepted) => accepted,
            Err(rejected) => {
                use trion_cnl::Rejected::*;
                let (status, diagnostic) = match rejected {
                    Ambiguous(diagnostic) => ("ambiguous", diagnostic),
                    Unsupported(diagnostic) => ("unsupported", diagnostic),
                    Invalid(diagnostic) => ("invalid", diagnostic),
                };
                let message = format!("{status} propositional input [{}]: {} (input bytes {}..{})", diagnostic.rule, diagnostic.reason, diagnostic.span.start, diagnostic.span.end);
                self.error("parse-check", &message, if diagnostic.rule == "CNL-VERSION" { line } else { input_line }, name);
                return;
            }
        };
        doc.propositional_checks.push(PropositionalCheck { name: name.to_string(), input, file: self.file.to_string(), line });
    }

    fn references(&mut self, text: &str, line: usize) -> Vec<String> {
        match bracket_list(text) {
            Some(list) => list,
            None => {
                self.error("parse-reference", "write bracketed references separated by commas", line, text);
                vec![]
            }
        }
    }

    fn example_block(&mut self, doc: &mut Document, name: &str, line: usize) {
        let mut example = Example { name: name.to_string(), kind: String::new(), form: None, input: None, base: vec![], candidate: vec![], expect: String::new(), file: self.file.to_string(), line };
        let mut expects = 0;
        let mut lines = 0;
        for (no, raw) in self.fields() {
            if let Some(rest) = keyword(&raw, "kind") {
                example.kind = rest.to_string();
            } else if let Some(rest) = keyword(&raw, "form") {
                example.form = Some(rest.to_string());
            } else if let Some(rest) = keyword(&raw, "input") {
                match whole_string(rest) {
                    Some(value) => example.input = Some(value),
                    None => self.error("parse-example", "an input is a quoted string", no, &raw),
                }
            } else if let Some(rest) = keyword(&raw, "base") {
                example.base = self.references(rest, no);
            } else if let Some(rest) = keyword(&raw, "candidate") {
                example.candidate = self.references(rest, no);
            } else if let Some(rest) = keyword(&raw, "expect") {
                // A reading example states its entry line by line: each
                // `expect` field holds one quoted line of the entry.
                match whole_string(rest) {
                    Some(line) if !example.expect.is_empty() => {
                        example.expect.push('\n');
                        example.expect.push_str(&line);
                        lines += 1;
                    }
                    Some(line) if rest.trim_start().starts_with('"') => {
                        example.expect = line;
                        lines += 1;
                    }
                    _ => example.expect = rest.to_string(),
                }
                expects += 1;
            } else if raw != "using definitions" {
                self.error("parse-example", "this field does not belong to an example", no, &raw);
            }
        }
        let reading = example.kind == "reading";
        if reading && (expects == 0 || lines != expects) {
            self.error("parse-example", "a reading example holds one or more expect fields, each with one quoted line of the expected entry", line, name);
        }
        if !reading && expects != 1 {
            self.error("parse-example", "an example holds exactly one expect field", line, name);
        }
        if !["syntax", "comparison", "consistency", "reading"].contains(&example.kind.as_str()) {
            self.error("parse-example", "the kinds are syntax, comparison, consistency and reading", line, name);
        }
        doc.examples.push(example);
    }

    fn scenario_block(&mut self, doc: &mut Document, name: &str, line: usize) {
        let mut scenario = Scenario { name: name.to_string(), individuals: Vec::new(), facts: Vec::new(), at: Vec::new(), expect: String::new(), malformed: false, file: self.file.to_string(), line };
        let mut expects = 0;
        for (no, raw) in self.fields() {
            if let Some(rest) = keyword(&raw, "given") {
                if last_significant(rest) == Some('.') {
                    scenario.facts.push((no, rest.to_string()));
                    continue;
                }
                // `given a user U1, a room R1`: each individual with its type.
                for item in rest.split(',').map(str::trim) {
                    let words: Vec<&str> = item.split_whitespace().collect();
                    match words.as_slice() {
                        [article, noun @ .., variable] if ["a", "an"].contains(article) && !noun.is_empty() && is_variable(variable) && !scenario.individuals.iter().any(|(known, _)| known == variable) => scenario.individuals.push((variable.to_string(), noun.join(" "))),
                        _ => {
                            scenario.malformed = true;
                            self.error("parse-scenario", "an individual of a scenario is declared once with its type and a variable, as in `given a user U1, a room R1`", no, &raw)
                        }
                    }
                }
            } else if let Some(rest) = keyword(&raw, "at") {
                let parsed = rest.split_once(':').and_then(|(time, clause)| {
                    let (number, unit) = time.trim().split_once(char::is_whitespace)?;
                    let factor = match unit.trim() {
                        "ms" | "millisecond" | "milliseconds" => 1,
                        "s" | "second" | "seconds" => 1000,
                        "minute" | "minutes" => 60_000,
                        _ => return None,
                    };
                    let clause = clause.trim();
                    (last_significant(clause) == Some('.')).then_some(())?;
                    Some((number.parse::<i64>().ok()?.checked_mul(factor)?, clause.to_string()))
                });
                match parsed {
                    Some((time, clause)) => scenario.at.push((no, time, clause)),
                    None => {
                        scenario.malformed = true;
                        self.error("parse-scenario", "a moment of a scenario is written as `at <whole number> <ms|seconds|minutes>: <clause>.`", no, &raw)
                    }
                }
            } else if let Some(rest) = keyword(&raw, "expect") {
                scenario.expect = rest.to_string();
                expects += 1;
            } else {
                scenario.malformed = true;
                self.error("parse-scenario", "a scenario holds `given`, `at` and `expect` fields", no, &raw);
            }
        }
        if expects != 1 || !["allowed", "forbidden", "undefined"].contains(&scenario.expect.as_str()) {
            self.error("parse-scenario", "a scenario holds exactly one `expect allowed`, `expect forbidden` or `expect undefined`", line, name);
            scenario.expect.clear();
            scenario.malformed = true;
        }
        doc.scenarios.push(scenario);
    }

    fn source_block(&mut self, doc: &mut Document, name: &str, line: usize) {
        let mut source = SourceDecl { name: name.to_string(), file: self.file.to_string(), line, ..Default::default() };
        let mut seen: Vec<String> = Vec::new();
        for (no, raw) in self.fields() {
            let (field, rest) = raw.split_once(char::is_whitespace).unwrap_or((raw.as_str(), ""));
            let rest = rest.trim();
            // A quoted field is a string; a missing quote is an error, not a silent drop.
            let mut string = |rest: &str| {
                let value = whole_string(rest);
                if value.is_none() {
                    self.error("parse-source", format!("the `{field}` field is a quoted string"), no, &raw);
                }
                value
            };
            let single = ["title", "locator", "revision", "kind", "path", "sha256", "retrieved", "minimum"];
            if single.contains(&field) {
                if seen.iter().any(|f| f == field) {
                    self.error("parse-source", format!("a source has one `{field}` field"), no, &raw);
                    continue;
                }
                seen.push(field.to_string());
            }
            match field {
                "title" => source.title = string(rest),
                "locator" => source.locator = string(rest),
                "revision" => source.revision = string(rest),
                "select" => source.select.extend(string(rest)),
                "kind" => source.kind = Some(rest.to_string()),
                "path" => source.path = string(rest),
                "sha256" => source.sha256 = string(rest),
                "retrieved" => source.retrieved = string(rest),
                "minimum" => source.minimum = Some(rest.to_string()),
                "quote" => {
                    let Some((quote_name, value)) = rest.split_once(char::is_whitespace) else {
                        self.error("parse-source", "write `quote NAME \"text\"`", no, &raw);
                        continue;
                    };
                    match whole_string(value) {
                        Some(text) if is_metadata_name(quote_name) => source.quotes.push(Quote { name: quote_name.to_string(), text, line: no }),
                        _ => self.error("parse-source", "write `quote NAME \"text\"`", no, &raw),
                    }
                }
                _ => self.error("parse-source", "a source holds title, locator, revision, select, kind, path, sha256, retrieved, minimum and quote fields", no, &raw),
            }
        }
        if source.title.is_none() || source.locator.is_none() {
            self.error("parse-source", format!("the source {name} has exactly one title and exactly one locator"), line, name);
        }
        doc.sources.push(source);
    }

    fn role_block(&mut self, doc: &mut Document, name: &str, line: usize) {
        let mut role = Role { name: name.to_string(), activations: vec![], forms: vec![], required: vec![], file: self.file.to_string(), line };
        for (no, raw) in self.fields() {
            self.role_line(&mut role, &raw, no);
        }
        doc.roles.push(role);
    }

    fn sentence(&mut self, text: &str, line: usize) -> Option<Sentence> {
        self.parse_english(text, line, text)
    }

    fn role_line(&mut self, role: &mut Role, trimmed: &str, line: usize) {
        if let Some(rest) = trimmed.strip_prefix("activate:") {
            if let Some(s) = self.sentence(rest.trim(), line) {
                role.activations.push(s);
            }
            return;
        }
        let (rest, is_form) = if let Some(r) = keyword(trimmed, "form") {
            (r, true)
        } else if let Some(r) = keyword(trimmed, "required") {
            (r, false)
        } else {
            self.error("parse-role-line", "a role body holds only `activate:`, `form` and `required` lines", line, trimmed);
            return;
        };
        let Some((id, body)) = rest.split_once(':') else {
            self.error("parse-role-line", "write `form <ID>: ...` or `required <ID>: ...`", line, trimmed);
            return;
        };
        let id = id.trim().to_string();
        let file = self.file.to_string();
        if !is_form {
            if let Some(pattern) = self.sentence(body.trim(), line) {
                role.required.push(RequiredRule { id, pattern, file, line, text: trimmed.to_string() });
            }
            return;
        }
        let Some(form) = parse_form_body(body) else {
            self.error("parse-form-rule", "write `form <ID>: <sentence>. where $<variable> matches /<regex>/ [when $<variable> matches /<regex>/]`", line, trimmed);
            return;
        };
        for candidate in std::iter::once(&form.regex).chain(form.applies_when.iter()) {
            if let Err(e) = regex::Regex::new(candidate) {
                self.error("parse-form-regex", format!("invalid regular expression: {e}"), line, trimmed);
                return;
            }
        }
        if let Some(pattern) = self.sentence(form.pattern.trim(), line) {
            role.forms.push(FormRule { id, pattern, variable: form.variable, regex: form.regex, negated: form.negated, applies_when: form.applies_when, file, line, text: trimmed.to_string() });
        }
    }

    fn annotation(&mut self, text: &str, line: usize) -> Option<Meta> {
        if let Some(rest) = keyword(text, "cite") {
            let (source, quote) = rest.split_once('#').map_or((rest, None), |(s, q)| (s, Some(q.to_string())));
            if !is_metadata_name(source) || quote.as_deref().is_some_and(|q| !is_metadata_name(q)) {
                self.error("parse-citation", "write `cite SOURCE` or `cite SOURCE#QUOTE`", line, text);
                return None;
            }
            return Some(Meta::Cite { source: source.to_string(), quote });
        }
        let reason = whole_string(keyword(text, "unsourced")?);
        if reason.is_none() {
            self.error("parse-citation", "write `unsourced \"reason\"`", line, text);
        }
        reason.map(|reason| Meta::Unsourced { reason })
    }

    /// The body shared by a namespace, a section and a context.
    fn body(&mut self, doc: &mut Document, ctx: &Context, in_namespace: bool) -> BlockEnd {
        let first_spec = doc.specs.len();
        let mut block_meta: Vec<Meta> = Vec::new();
        let mut last_rule: Option<(Option<usize>, usize)> = None;
        let result = loop {
            let Some((line, indent, text)) = self.next_text() else { break BlockEnd::EndOfFile };
            if text == END {
                break BlockEnd::Closed;
            }
            if text.starts_with("cite ") || text.starts_with("unsourced ") {
                let Some(meta) = self.annotation(&text, line) else { continue };
                // An annotation indented under a statement belongs to it.
                match last_rule {
                    Some((Some(spec), rule_indent)) if indent > rule_indent && spec < doc.specs.len() => doc.specs[spec].meta.push(meta),
                    // Under a malformed statement, the annotation has no owner.
                    Some((None, rule_indent)) if indent > rule_indent => {}
                    _ => block_meta.push(meta),
                }
                continue;
            }
            if let Some(rest) = keyword(&text, "detailed").filter(|rest| keyword(rest, "by").is_some()) {
                let details = self.details(rest, line, &text);
                // A refinement belongs to the statement it is indented under.
                match last_rule {
                    Some((Some(spec), rule_indent)) if indent > rule_indent && spec < doc.specs.len() => doc.specs[spec].details.extend(details),
                    _ => self.error("parse-refinement", "`detailed by` is indented under the statement that it details", line, &text),
                }
                continue;
            }
            if let Some(rank) = self.rank(&text, line) {
                // A priority line belongs to the statement it is indented under.
                match last_rule {
                    Some((Some(spec), rule_indent)) if indent > rule_indent && spec < doc.specs.len() => {
                        let owner = &mut doc.specs[spec];
                        owner.overrides.extend(rank.overrides);
                        owner.default |= rank.default;
                        owner.weight = rank.weight.or(owner.weight);
                    }
                    _ => self.error("parse-priority", "a priority line is indented under the statement that it ranks", line, &text),
                }
                continue;
            }
            let before = doc.specs.len();
            self.statement(doc, ctx, line, indent, text, in_namespace);
            last_rule = Some(((doc.specs.len() > before).then_some(before), indent));
        };
        for spec in &mut doc.specs[first_spec..] {
            for meta in &block_meta {
                if !spec.meta.contains(meta) {
                    spec.meta.push(meta.clone());
                }
            }
        }
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn statement(&mut self, doc: &mut Document, ctx: &Context, line: usize, _indent: usize, text: String, in_namespace: bool) {
        let file = self.file.to_string();
        self.stmt_indent = _indent;
        self.block_meta.clear();
        self.block_details.clear();
        self.block_rank = Rank::default();
        self.block_elements.clear();
        if text == "end" {
            self.error("parse-block", "a block closes where its indentation ends: `end` is not written", line, &text);
            return;
        }
        if let Some(name) = keyword(&text, "use").filter(|r| is_dotted(r)) {
            if !in_namespace {
                self.error("parse-placement", "a use declaration occurs directly within a namespace block", line, &text);
            }
            doc.imports.push(Import { name: name.to_string(), namespace: name.to_string(), file, line });
            return;
        }
        if let Some(rest) = keyword(&text, "note") {
            if whole_string(rest).is_none() {
                self.error("parse-note", "a note is a quoted string", line, &text);
            }
            return;
        }
        if let Some(rest) = keyword(&text, "ref") {
            match rest.strip_prefix('[').and_then(|r| r.strip_suffix(']')) {
                Some(id) if is_stable_id(id) => doc.references.push((id.to_string(), line)),
                _ => self.error("parse-reference", "write `ref [ID]`", line, &text),
            }
            return;
        }
        if let Some(rest) = keyword(&text, "section") {
            match quoted(rest).filter(|(_, tail)| [":", ""].contains(&tail.trim())) {
                Some((title, tail)) => {
                    let mut inner = ctx.clone();
                    // Sections of the flat form follow one another and do not nest.
                    if tail.trim().is_empty() {
                        self.blocks.push(Block::FlatSection(_indent));
                    } else {
                        self.open();
                    }
                    inner.sections.push(title);
                    self.body(doc, &inner, false);
                }
                None => self.error("parse-block", "write `section \"title\"` or `section \"title\":`", line, &text),
            }
            return;
        }
        if let Some(rest) = keyword(&text, "table").filter(|rest| rest.starts_with('"')) {
            self.table(doc, ctx, line, rest);
            return;
        }
        if let Some(name) = keyword(&text, "compatibility").and_then(|r| r.strip_suffix(':')).map(str::trim).filter(|n| is_metadata_name(n)) {
            self.compatibility_block(doc, name, line, &text);
            return;
        }
        for (kw, placement) in [("source", in_namespace), ("check", !ctx.shared), ("example", !ctx.shared), ("scenario", !ctx.shared)] {
            let Some(name) = keyword(&text, kw).and_then(|r| r.strip_suffix(':')).map(str::trim) else { continue };
            if name.contains(char::is_whitespace) {
                continue;
            }
            if !is_metadata_name(name) {
                self.error("parse-name", format!("a {kw} name uses the stable identifier form"), line, &text);
            }
            if !placement {
                self.error("parse-placement", format!("a {kw} declaration does not belong in this block"), line, &text);
            }
            match kw {
                "source" => self.source_block(doc, name, line),
                "check" => self.check_block(doc, name, line),
                "scenario" => self.scenario_block(doc, name, line),
                _ => self.example_block(doc, name, line),
            }
            return;
        }
        if ctx.shared && ["term", "alias", "bind", "extend", "classify", "role", "predicate", "primitive"].iter().any(|kw| keyword(&text, kw).is_some()) && last_significant(&text) != Some('.') {
            self.error("parse-placement", "a shared context holds statements, action lists, diagrams, contexts, sections, citations, notes and references", line, &text);
            if last_significant(&text) == Some(':') {
                self.skip_block();
            }
            return;
        }
        if let Some(name) = keyword(&text, "role").and_then(|r| r.strip_suffix(':')) {
            self.role_block(doc, name.trim(), line);
            return;
        }
        if let Some((name, signature)) = keyword(&text, "predicate").and_then(parse_predicate) {
            doc.predicates.push(PredicateDecl { name, signature, file, line });
            return;
        }
        for by in ["environment", "system"] {
            if let Some(name) = keyword(&text, by).map(str::trim).filter(|n| !n.is_empty() && last_significant(n) != Some('.') && !n.contains(':')) {
                if ctx.shared {
                    self.error("parse-placement", "a shared context holds statements, action lists, diagrams, contexts, sections, citations, notes and references", line, &text);
                } else {
                    // `system A, B` declares each listed actor, as `primitive A, B` declares each term.
                    doc.controls.extend(name.split(',').map(str::trim).filter(|actor| !actor.is_empty()).map(|actor| ControlDecl { name: actor.to_string(), by: by.to_string(), file: file.clone(), line }));
                }
                return;
            }
        }
        if let Some(name) = keyword(&text, "measure").map(str::trim).filter(|n| !n.is_empty() && last_significant(n) != Some('.') && !n.contains(':') && n.split_whitespace().count() <= 4) {
            doc.measures.push(PrimitiveDecl { name: name.to_string(), file, line });
            return;
        }
        if let Some(name) = keyword(&text, "individuals").map(str::trim).filter(|n| !n.is_empty() && last_significant(n) != Some('.') && !n.contains(':')) {
            // `individuals A, B` declares each listed type, and each is a primitive term.
            for term in name.split(',').map(str::trim).filter(|term| !term.is_empty()) {
                doc.individuals.push(PrimitiveDecl { name: term.to_string(), file: file.clone(), line });
                doc.primitives.push(PrimitiveDecl { name: term.to_string(), file: file.clone(), line });
            }
            return;
        }
        if let Some(name) = keyword(&text, "primitive").map(str::trim).filter(|n| !n.is_empty() && last_significant(n) != Some('.') && !n.contains(':')) {
            // `primitive A, B, C` declares each listed term.
            doc.primitives.extend(name.split(',').map(str::trim).filter(|term| !term.is_empty()).map(|term| PrimitiveDecl { name: term.to_string(), file: file.clone(), line }));
            return;
        }
        if let Some(rest) = keyword(&text, "term") {
            if let Some((term, kind)) = rest.split_once(':').filter(|(_, k)| !k.trim().is_empty() && !k.trim().contains(' ')) {
                doc.vocabulary.push(VocabDecl { term: term.trim().to_string(), kind: kind.trim().to_string(), file, line });
                return;
            }
        }
        if let Some((term, canonical)) = keyword(&text, "alias").and_then(|r| r.split_once(" = ")) {
            doc.aliases.push(Alias { term: term.trim().to_string(), canonical: canonical.trim().to_string(), file, line });
            return;
        }
        if let Some((term, role)) = keyword(&text, "bind").and_then(parse_binding) {
            doc.bindings.push(Binding { term, role, file, line, text: text.clone() });
            return;
        }
        if let Some((attr, values)) = keyword(&text, "extend").and_then(parse_extension) {
            doc.extensions.push(Extension { attr, values, file, line, text: text.clone() });
            return;
        }
        if let Some(attr) = keyword(&text, "classify").and_then(parse_classification) {
            doc.classifications.push(Classification { attr, file, line, text: text.clone() });
            return;
        }
        if text.starts_with("namespace ") || text.starts_with("include ") || text.starts_with("package ") {
            self.error("parse-placement", "this declaration occurs only at the file level", line, &text);
            if text.ends_with(':') {
                self.skip_block();
            }
            return;
        }

        let written = text.chars().count();
        let (id, body) = self.take_id(text, line);
        let own_line = !body.is_empty();
        // An identifier on the line of its sentence moves the first column.
        let after_id = written - body.chars().count();
        let Some((body_line, body_indent, body)) = self.statement_after_id(body) else { return };
        let (line, indent) = if own_line { (line, _indent + after_id) } else { (body_line, body_indent) };
        self.column = indent + 1;
        self.end_line = line;
        self.shares_line = false;
        if body == "concept:" {
            self.concept(doc, ctx, id, line);
            return;
        }
        if let Some(name) = keyword(&body, "diagram kind").and_then(|r| r.strip_suffix(':')) {
            self.diagram_kind(doc, name.trim(), line, &body);
            return;
        }
        if let Some(kind) = keyword(&body, "diagram").and_then(|r| r.strip_suffix(':')) {
            if let Some(declared) = self.kinds.iter().find(|k| k.name == kind.trim()).cloned() {
                self.declared_diagram(doc, ctx, id, &declared, line);
                return;
            }
            self.error("UNSUPPORTED_DIAGRAM_KIND", format!("the diagram kind `{kind}` has no declared interpretation"), line, &body);
            self.skip_block();
            return;
        }
        let (paragraph, starts) = self.gather_located(body, line, indent);
        if paragraph.chars().any(|c| c.is_alphabetic() && !c.is_ascii()) && !paragraph.contains('"') && !paragraph.contains('`') {
            self.error("NOT_CONTROLLED_ENGLISH", "a normative sentence is written in the controlled English grammar", line, &paragraph);
            return;
        }
        // A paragraph holds complete sentences. An identifier names the first one only.
        let locate = |offset: usize| {
            let (from, no, indent) = starts.iter().rev().find(|(from, _, _)| *from <= offset).copied().unwrap_or((0, line, indent));
            (no, indent + 1 + paragraph[from..offset].chars().count())
        };
        let mut id = id;
        let mut last_start = 0;
        for (from, to) in sentence_spans(&paragraph) {
            let sentence = &paragraph[from..to];
            let (line, column) = locate(from);
            self.shares_line = last_start == line;
            last_start = line;
            self.column = column;
            self.end_line = locate(to.saturating_sub(1)).0;
            match last_significant(sentence) {
                Some(':') => self.block_statement(doc, ctx, id.take(), sentence, line),
                Some('.') => self.plain_statement(doc, ctx, id.take(), sentence, line),
                _ => self.error("parse-sentence", "a sentence ends with a period", line, sentence),
            }
        }
    }

    fn block_statement(&mut self, doc: &mut Document, ctx: &Context, id: Option<String>, sentence: &str, line: usize) {
        let collapsed = sentence.split_whitespace().collect::<Vec<_>>().join(" ");
        if let Some((at, kind, len)) = list_phrase(&collapsed) {
            self.action_list(doc, ctx, id, &collapsed, line, at, kind, len);
            return;
        }
        if let Some(at) = collapsed.find(FLOW_PHRASE) {
            self.flow(doc, ctx, id, &collapsed, line, at);
            return;
        }
        let head = collapsed.trim_end_matches(':').trim();
        let opens_context = ["For each ", "Where ", "While ", "When ", "If ", "After ", "Once ", "Upon ", "Before ", "During ", "Until ", "On "].iter().any(|k| head.starts_with(k));
        if !opens_context || id.is_some() {
            self.error("parse-block", "this block header is not a section, a context, an action list, a flow or a declaration", line, &collapsed);
            self.skip_block();
            return;
        }
        let mut inner = ctx.clone();
        inner.shared = true;
        if head.starts_with("For each ") {
            let before = inner.vars.bound.len();
            let bound = match inner.vars.bind_head(head) {
                Ok(true) => Ok(()),
                Ok(false) => inner.vars.apply(head).map(|_| ()),
                Err(message) => Err(message),
            };
            match bound {
                Ok(()) if inner.vars.bound.len() == before => self.error("parse-block", "`For each` binds a typed variable, as in `For each request R:`", line, head),
                Ok(()) => {}
                Err(message) => self.error("UNRESOLVED_REFERENCE", message, line, head),
            }
        } else {
            let mut vars = inner.vars.clone();
            vars.tag = self.binding_tag(id.as_deref(), line);
            let Some(frames) = self.head_frames(head, &mut vars, line) else {
                self.skip_block();
                return;
            };
            inner.vars = vars;
            let mut merged = inner.frames.clone();
            self.merge_frames(&mut merged, &frames, line, head);
            inner.frames = merged;
        }
        inner.head_text.push(head.to_string());
        inner.head_lines.push(line);
        self.open();
        if self.closing() {
            self.error("parse-block", "a block holds the lines that are indented more than its header: this one holds none", line, head);
        }
        self.body(doc, &inner, false);
    }

    fn file(&mut self, parsed: &mut ParsedFile) {
        while let Some((line, indent, text)) = self.next_text() {
            self.stmt_indent = indent;
            if let Some(rest) = keyword(&text, "package") {
                self.package(parsed, rest, line, &text);
            } else if let Some(rest) = keyword(&text, "include") {
                match whole_string(rest) {
                    Some(path) => parsed.includes.push(Include { path, line }),
                    None => self.error("parse-include", "write `include \"path\"`", line, &text),
                }
            } else if let Some(name) = keyword(&text, "namespace").map(|r| r.strip_suffix(':').unwrap_or(r).trim()).filter(|n| is_dotted(n)) {
                let mut doc = Document { namespace: name.to_string(), file: self.file.to_string(), ..Default::default() };
                // Without a colon the namespace runs to the next namespace line.
                if text.ends_with(':') {
                    self.open();
                } else {
                    self.blocks.push(Block::FlatNamespace(indent));
                }
                self.body(&mut doc, &Context::default(), true);
                parsed.documents.push(doc);
            } else {
                self.error("parse-placement", "a file holds a package declaration, includes and namespace blocks", line, &text);
                if last_significant(&text) == Some(':') {
                    self.skip_block();
                }
            }
        }
    }

    fn package(&mut self, parsed: &mut ParsedFile, rest: &str, line: usize, text: &str) {
        let decl = rest.split_once(" edition ").and_then(|(name, edition)| Some((name.trim(), whole_string(edition)?)));
        match decl {
            Some((name, edition)) if is_dotted(name) && parsed.package.is_none() => parsed.package = Some(PackageDecl { name: name.to_string(), edition, line }),
            _ => self.error("parse-package", "write one `package NAME edition \"EDITION\"` declaration", line, text),
        }
    }
}

fn list_node(kind: ListKind, items: Vec<CompNode>) -> CompNode {
    match kind {
        ListKind::All => CompNode::All { items },
        ListKind::Some => CompNode::Some { items },
        ListKind::One => CompNode::One { items },
        ListKind::Sequence => CompNode::Sequence { items },
    }
}

/// The first structural problem of a flow.
fn flow_problem(flow: &Flow) -> Option<String> {
    let names: BTreeSet<&str> = flow.steps.iter().map(|s| s.name.as_str()).collect();
    let known = |name: &str| names.contains(name);
    let mut successors: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (from, to) in &flow.edges {
        successors.entry(from).or_default().push(to);
    }
    for choice in &flow.choices {
        let targets = choice.arms.iter().map(|(_, t)| t).chain(choice.otherwise.iter());
        successors.entry(&choice.after).or_default().extend(targets.map(String::as_str));
    }
    for name in successors.iter().flat_map(|(from, to)| std::iter::once(*from).chain(to.iter().copied())).chain(std::iter::once(flow.start.as_str())).chain(flow.finish.iter().map(String::as_str)) {
        if !known(name) {
            return Some(format!("the step `{name}` is not declared in this flow"));
        }
    }
    if flow.finish.is_empty() {
        return Some("a flow has at least one finish step".to_string());
    }
    for step in &flow.steps {
        let name = step.name.as_str();
        let edges = flow.edges.iter().filter(|(from, _)| from == name).count();
        let choices = flow.choices.iter().filter(|c| c.after == name).count();
        let finishing = flow.finish.iter().any(|f| f == name);
        match (finishing, edges, choices) {
            (true, 0, 0) | (false, 1, 0) | (false, 0, 1) => {}
            (true, _, _) => return Some(format!("the finish step `{name}` has a successor")),
            _ => return Some(format!("the step `{name}` needs exactly one successor or one choice")),
        }
    }
    // Depth-first over the successors: a back edge is a cycle.
    fn visit<'a>(node: &'a str, successors: &BTreeMap<&'a str, Vec<&'a str>>, path: &mut Vec<&'a str>, seen: &mut BTreeSet<&'a str>) -> Option<String> {
        if path.contains(&node) {
            return Some(format!("cycle through `{node}`: this flow kind has no loop semantics"));
        }
        if !seen.insert(node) {
            return None;
        }
        path.push(node);
        for next in successors.get(node).into_iter().flatten() {
            if let Some(found) = visit(next, successors, path, seen) {
                return Some(found);
            }
        }
        path.pop();
        None
    }
    let mut seen = BTreeSet::new();
    if let Some(found) = visit(&flow.start, &successors, &mut Vec::new(), &mut seen) {
        return Some(found);
    }
    names.iter().find(|n| !seen.contains(*n)).map(|n| format!("the step `{n}` is not reachable from the start"))
}

fn parse_extension(rest: &str) -> Option<(String, Vec<String>)> {
    let (attr, values) = rest.strip_suffix('.').unwrap_or(rest).split_once(" with ")?;
    let values: Vec<String> = values.split(',').map(|v| v.trim().trim_start_matches("and ").to_string()).filter(|v| !v.is_empty()).collect();
    (!values.is_empty()).then(|| (attr.trim().to_string(), values))
}

fn parse_classification(rest: &str) -> Option<String> {
    let attr = rest.strip_suffix('.').unwrap_or(rest).strip_prefix("sentences as ")?;
    (!attr.trim().is_empty()).then(|| attr.trim().to_string())
}

fn parse_binding(rest: &str) -> Option<(String, String)> {
    let body = rest.strip_suffix('.').unwrap_or(rest).trim();
    let (term, role) = body.rsplit_once(" as ")?;
    let role = role.trim();
    (role.contains('.') && !role.contains(char::is_whitespace)).then(|| (term.trim().to_string(), role.to_string()))
}

struct FormBody {
    pattern: String,
    variable: String,
    regex: String,
    negated: bool,
    applies_when: Option<String>,
}

fn slashed(text: &str) -> Option<(String, &str)> {
    let body = text.trim().strip_prefix('/')?;
    let end = body.find("/ when $").or_else(|| body.rfind('/'))?;
    Some((body[..end].to_string(), body[end + 1..].trim()))
}

fn parse_form_body(body: &str) -> Option<FormBody> {
    let (pattern, constraint) = body.split_once(" where $")?;
    let (variable, tail, negated) = match constraint.split_once(" does not match ") {
        Some((v, t)) => (v, t, true),
        None => {
            let (v, t) = constraint.split_once(" matches ")?;
            (v, t, false)
        }
    };
    let (regex, rest) = slashed(tail)?;
    let applies_when = if rest.is_empty() {
        None
    } else {
        let guard = rest.strip_prefix("when $")?.strip_prefix(variable.trim())?.trim().strip_prefix("matches ")?;
        Some(slashed(guard)?.0)
    };
    Some(FormBody { pattern: pattern.trim().to_string(), variable: format!("${}", variable.trim()), regex, negated, applies_when })
}

/// Parses one file. Errors become diagnostics and parsing continues.
pub fn parse_document(src: &str, file: &str) -> (ParsedFile, Vec<Diagnostic>) {
    let mut parser = Parser { lines: logical_lines(src), at: 0, file, diags: Vec::new(), blocks: Vec::new(), stmt_indent: 0, closer: Line { no: 0, indent: 0, text: END.to_string() }, block_meta: Vec::new(), block_details: Vec::new(), block_rank: Rank::default(), block_elements: Vec::new(), kinds: Vec::new(), block_kind: None, column: 1, end_line: 0, shares_line: false };
    let mut parsed = ParsedFile::default();
    parser.file(&mut parsed);
    (parsed, parser.diags)
}

/// Parses one statement or response composition outside any file.
pub fn parse_statement(src: &str) -> (Document, Vec<Diagnostic>) {
    let wrapped = format!("namespace statement\n{src}\n");
    let (mut parsed, diags) = parse_document(&wrapped, "<statement>");
    (parsed.documents.pop().unwrap_or_default(), diags)
}
