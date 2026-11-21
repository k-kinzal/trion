//! Requirement traceability: quotations from a source document, and how much
//! of that document the specifications account for.

use crate::project::{LoadedSource, Project};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::fs;
use trion_language::document::SourceDecl;
use trion_language::{Diagnostic, Meta, Spec, SpecRef};

#[derive(Debug, Clone, Serialize)]
pub struct UnitCoverage {
    pub index: usize,
    pub text: String,
    pub total: usize,
    pub covered: usize,
    pub uncovered: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct SourceCoverage {
    pub id: String,
    pub kind: String,
    pub path: String,
    pub total: usize,
    pub covered: usize,
    pub percent: f64,
    pub units: Vec<UnitCoverage>,
}

#[derive(Debug, Clone, Serialize)]
pub struct UnsourcedSpec {
    pub id: String,
    pub text: String,
    /// Why the statement has no source, when it says so.
    pub reason: Option<String>,
}

#[derive(Debug, Clone, Serialize, Default)]
pub struct SourceReport {
    pub sources: Vec<SourceCoverage>,
    pub unsourced: Vec<UnsourcedSpec>,
    pub diagnostics: Vec<Diagnostic>,
}

fn spec_ref(spec: &Spec) -> SpecRef {
    SpecRef { id: spec.display_id(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() }
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes).iter().map(|b| format!("{b:02x}")).collect()
}

/// Splits a source into units: sentences of Japanese or English text, or lines.
fn unit_bounds(chars: &[char]) -> Vec<(usize, usize)> {
    let mut bounds = Vec::new();
    let mut start = 0;
    for (i, c) in chars.iter().enumerate() {
        if matches!(c, '。' | '\n') {
            bounds.push((start, i + 1));
            start = i + 1;
        }
    }
    if start < chars.len() {
        bounds.push((start, chars.len()));
    }
    bounds.retain(|&(s, e)| chars[s..e].iter().any(|c| !c.is_whitespace()));
    bounds
}

/// Finds every position of `quote` in `chars`.
fn occurrences(chars: &[char], quote: &[char]) -> Vec<usize> {
    if quote.is_empty() || quote.len() > chars.len() {
        return Vec::new();
    }
    (0..=chars.len() - quote.len()).filter(|&i| chars[i..i + quote.len()] == *quote).collect()
}

/// Whether a quote occupies whole sentences of its source: a fragment of a
/// sentence does not stand as a requirement.
fn whole_sentences(chars: &[char], at: usize, length: usize) -> bool {
    let ends_sentence = |c: char| matches!(c, '。' | '．' | '！' | '？' | '.' | '!' | '?' | '\n');
    let opens = at == 0 || (0..at).rev().find(|&i| !matches!(chars[i], ' ' | '\t' | '　')).is_none_or(|i| ends_sentence(chars[i]));
    let last = chars[at..at + length].iter().rev().find(|c| !c.is_whitespace()).copied();
    let closes = last.is_some_and(ends_sentence) || at + length == chars.len() || chars[at + length..].iter().find(|c| !matches!(c, ' ' | '\t' | '　')).is_none_or(|c| *c == '\n');
    opens && closes
}

fn at_declaration(decl: &SourceDecl) -> SpecRef {
    SpecRef { id: decl.name.clone(), file: decl.file.clone(), line: decl.line, text: format!("source {}", decl.name) }
}

/// The quotes of a source that some statement cites.
fn cited_quotes(source: &str, specs: &[&Spec]) -> BTreeSet<String> {
    specs.iter().flat_map(|spec| &spec.meta).filter_map(|meta| match meta {
        Meta::Cite { source: cited, quote: Some(quote) } if cited == source => Some(quote.clone()),
        _ => None,
    }).collect()
}

fn check_source(loaded: &LoadedSource, specs: &[&Spec], diags: &mut Vec<Diagnostic>) -> Option<SourceCoverage> {
    let source = &loaded.decl;
    let relative = source.path.as_deref()?;
    let at = at_declaration(source);
    let path = loaded.dir.join(relative);
    let bytes = match fs::read(&path) {
        Ok(b) => b,
        Err(e) => {
            diags.push(Diagnostic::error("source-unreadable", format!("cannot read source {}: {e}", path.display()), vec![at]));
            return None;
        }
    };
    let actual = sha256_hex(&bytes);
    if source.sha256.as_deref() != Some(actual.as_str()) {
        diags.push(Diagnostic::error("source-changed", format!("source {relative} changed: expected sha256 {}, found {actual}", source.sha256.as_deref().unwrap_or("nothing")), vec![at.clone()]));
    }
    let text = String::from_utf8_lossy(&bytes);
    let chars: Vec<char> = text.chars().collect();
    let mut covered = vec![false; chars.len()];
    let used = cited_quotes(&source.name, specs);

    for quote in &source.quotes {
        let here = SpecRef { id: format!("{}#{}", source.name, quote.name), file: source.file.clone(), line: quote.line, text: quote.text.clone() };
        let needle: Vec<char> = quote.text.chars().collect();
        match occurrences(&chars, &needle).as_slice() {
            [] => diags.push(Diagnostic::error("source-quote-not-found", format!("the quote is not in source {}: \"{}\"", source.name, quote.text), vec![here])),
            [position] => {
                if !whole_sentences(&chars, *position, needle.len()) {
                    diags.push(Diagnostic::error("source-quote-partial", format!("this quote of {} cuts a sentence: quote the whole sentence", source.name), vec![here.clone()]));
                }
                if used.contains(&quote.name) {
                    covered[*position..*position + needle.len()].iter_mut().for_each(|c| *c = true);
                } else {
                    diags.push(Diagnostic::warning("source-quote-unused", format!("no statement cites the quote {}#{}", source.name, quote.name), vec![here]));
                }
            }
            many => diags.push(Diagnostic::error("source-quote-ambiguous", format!("the quote appears {} times in source {}; quote more of it", many.len(), source.name), vec![here])),
        }
    }

    let counted = |range: std::ops::Range<usize>, only_covered: bool| range.filter(|&i| !chars[i].is_whitespace() && (!only_covered || covered[i])).count();
    let units: Vec<UnitCoverage> = unit_bounds(&chars)
        .into_iter()
        .enumerate()
        .map(|(index, (s, e))| UnitCoverage {
            index: index + 1,
            text: chars[s..e].iter().collect::<String>().trim().to_string(),
            total: counted(s..e, false),
            covered: counted(s..e, true),
            uncovered: (s..e).filter(|&i| !covered[i] && !chars[i].is_whitespace()).map(|i| chars[i]).collect(),
        })
        .collect();
    let total: usize = units.iter().map(|u| u.total).sum();
    let done: usize = units.iter().map(|u| u.covered).sum();
    let percent = if total == 0 { 100.0 } else { done as f64 * 100.0 / total as f64 };
    Some(SourceCoverage { id: source.name.clone(), kind: source.kind.clone().unwrap_or_else(|| "requirement".to_string()), path: relative.to_string(), total, covered: done, percent, units })
}

/// Validates the annotations and measures coverage.
pub fn check(project: &Project) -> SourceReport {
    let mut report = SourceReport::default();
    // A compatibility claim is about one revision of a declared source.
    let declared: Vec<&SourceDecl> = project.set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.sources).collect();
    for claim in project.set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.compatibility) {
        let at = SpecRef { id: claim.name.clone(), file: claim.file.clone(), line: claim.line, text: format!("compatibility {}", claim.name) };
        match declared.iter().find(|s| s.name == claim.source) {
            None => report.diagnostics.push(Diagnostic::error("compatibility-source-unknown", format!("the compatibility claim {} names the source `{}`, which is not declared", claim.name, claim.source), vec![at])),
            Some(source) if source.revision.as_deref() != Some(claim.revision.as_str()) => report.diagnostics.push(Diagnostic::error(
                "compatibility-revision",
                format!("the compatibility claim {} is about revision `{}`, and source {} is at revision `{}`", claim.name, claim.revision, claim.source, source.revision.as_deref().unwrap_or("none")),
                vec![at],
            )),
            Some(_) => {}
        }
    }
    for loaded in &project.sources {
        if !matches!(loaded.decl.kind.as_deref(), None | Some("requirement" | "citation")) {
            report.diagnostics.push(Diagnostic::error("source-kind-unknown", format!("source {} has kind `{}`; a source is a requirement or a citation", loaded.decl.name, loaded.decl.kind.as_deref().unwrap_or_default()), vec![at_declaration(&loaded.decl)]));
        }
    }
    let specs: Vec<&Spec> = project.root_specs().collect();
    let cited: Vec<&Spec> = project.all_specs().collect();

    // A statement that cites nothing has no source: that is a warning, with
    // the reason when the statement gives one.
    for spec in &specs {
        let has_cite = spec.meta.iter().any(|m| matches!(m, Meta::Cite { .. }));
        if has_cite {
            continue;
        }
        let reason = spec.meta.iter().find_map(|m| if let Meta::Unsourced { reason } = m { Some(reason.clone()) } else { None });
        let message = match &reason {
            Some(reason) => format!("this statement names no source: {reason}"),
            None => "this statement names no source: cite one, or state why it has none with `unsourced`".to_string(),
        };
        report.diagnostics.push(Diagnostic::warning("unsourced", message, vec![spec_ref(spec)]));
        report.unsourced.push(UnsourcedSpec { id: spec.display_id(), text: spec.sentence.source.clone(), reason });
    }

    for loaded in &project.sources {
        let source = &loaded.decl;
        // A reference keeps the dependency's own evidence without adding its
        // sentences to the contracts of this project.
        let catalogue = project.set.packages.iter().find(|package| package.documents.iter().any(|doc| {
            doc.sources.iter().any(|origin| origin.file == source.file && origin.line == source.line)
        }));
        let evidence: Vec<&Spec> = cited.iter().copied().chain(
            catalogue.into_iter().flat_map(|package| &package.documents).flat_map(|doc| &doc.symbol_sources)
        ).collect();
        if let Some(coverage) = check_source(loaded, &evidence, &mut report.diagnostics) {
            let minimum = source.minimum.as_deref().and_then(|m| m.parse::<f64>().ok()).unwrap_or(100.0);
            if coverage.percent < minimum {
                report.diagnostics.push(Diagnostic::error("source-coverage-below-minimum", format!("source {} is {:.2}% covered; the minimum is {minimum:.2}%", coverage.id, coverage.percent), vec![at_declaration(source)]));
            }
            report.sources.push(coverage);
        }
    }
    report
}
