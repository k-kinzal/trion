#![allow(dead_code)]

use trion_language::{parse_document, Document, Package, SpecSet, VocabularyMode};
use trion_verification::{analyze, Analysis, Options};

/// Wraps the statements of a test in a namespace block named after the package,
/// unless the text already holds one. A first `package NAME` line names it.
pub fn wrap(package: &str, src: &str) -> String {
    if src.lines().map(str::trim_start).find(|l| !l.is_empty() && !l.starts_with("//")).is_some_and(|l| l.starts_with("namespace ")) {
        return src.to_string();
    }
    let body = match src.split_once('\n') {
        Some((first, rest)) if first.trim().strip_prefix("package ").is_some_and(|n| !n.contains(' ')) => rest,
        _ => src,
    };
    format!("namespace {package}\n{body}\n")
}

/// The namespace of a root package's own document is the package itself, and
/// the analysis reads it unqualified, as the loader does.
fn normalize(doc: &mut Document, package: &str, is_root: bool) {
    if is_root {
        if doc.namespace == package {
            doc.namespace = String::new();
        } else if let Some(rest) = doc.namespace.strip_prefix(&format!("{package}.")) {
            doc.namespace = rest.to_string();
        }
    }
}

/// Parses a package of one file and returns its namespace documents.
pub fn documents(package: &str, is_root: bool, src: &str) -> Vec<Document> {
    let (parsed, diags) = parse_document(&wrap(package, src), &format!("{package}.trion"));
    assert!(diags.is_empty(), "unexpected parse diagnostics: {diags:?}");
    parsed
        .documents
        .into_iter()
        .map(|mut doc| {
            normalize(&mut doc, package, is_root);
            doc
        })
        .collect()
}

/// Builds a one-package specification set from source text.
pub fn set(src: &str) -> SpecSet {
    set_of(&[("main", true, src)], VocabularyMode::Inferred)
}

pub fn set_of(packages: &[(&str, bool, &str)], mode: VocabularyMode) -> SpecSet {
    let packages = packages.iter().map(|(name, is_root, src)| Package { name: name.to_string(), is_root: *is_root, documents: documents(name, *is_root, src) }).collect();
    SpecSet { packages, vocabulary_mode: mode }
}

pub fn run(src: &str) -> Analysis {
    analyze(&set(src), &Options::default())
}

pub fn codes(analysis: &Analysis) -> Vec<String> {
    analysis.diagnostics.iter().map(|d| d.code.clone()).collect()
}

pub fn run_codes(src: &str) -> Vec<String> {
    codes(&run(src))
}

/// The codes of the parts that have no formal reading.
#[allow(dead_code)]
pub fn unread_codes(src: &str) -> Vec<String> {
    run(src).silence.opaque.iter().map(|d| d.code.to_string()).collect()
}

/// The source sentences each contradiction-like diagnostic refers to.
pub fn cores(analysis: &Analysis, code: &str) -> Vec<Vec<String>> {
    analysis
        .diagnostics
        .iter()
        .filter(|d| d.code == code)
        .map(|d| {
            let mut texts: Vec<String> = d.refs.iter().map(|r| r.text.clone()).collect();
            texts.sort();
            texts
        })
        .collect()
}
