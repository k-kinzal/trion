#![allow(dead_code)]

use trion_language::{parse_document, Document, Package, SpecSet, VocabularyMode};
use trion_language::{Diagnostic, SpecRef};
use trion_verification::{analyze, proof_obligations, Analysis, ObligationVerdict, Options};

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
    proved(&set(src), &Options::default())
}

/// The analysis of a set with the finding of each proof obligation that is
/// not proved, as `trion` and `trioc prove` report them together: each
/// obligation is decided as `trioc` decides it ([`trion_verification::ProofObligations::decide`]).
pub fn proved(set: &SpecSet, options: &Options) -> Analysis {
    let mut analysis = analyze(set, options);
    let stated = proof_obligations(set, &analysis, options.bounds.trace_length);
    analysis.diagnostics.extend(stated.findings.iter().cloned());
    let inst = stated.instance(options.bounds.decisions);
    let at = |id: &str| -> SpecRef {
        analysis.model.constraints.iter().flat_map(|c| &c.refs).find(|r| r.id == id).cloned().unwrap_or(SpecRef { id: id.to_string(), file: String::new(), line: 0, text: String::new() })
    };
    let mut found = Vec::new();
    for obligation in &stated.obligations {
        let decision = stated.decide(&inst, obligation);
        let refs: Vec<SpecRef> = obligation.statements.iter().map(|id| at(id)).collect();
        let named = |c: &trion_verification::Counterexample| -> Vec<SpecRef> { c.statements.iter().map(|id| at(id)).collect() };
        let why = decision.reason.clone().unwrap_or_default();
        match decision.verdict {
            ObligationVerdict::Proved => {}
            ObligationVerdict::Unproved => found.push(Diagnostic::error("obligation-unproved", format!("the obligation {} is neither proved nor refuted: {why}", obligation.name), Vec::new())),
            ObligationVerdict::Refuted => match obligation.property.as_str() {
                // A form that a bound role requires, which the statements do not have.
                "consistency" if !decision.counterexamples.is_empty() => found.extend(decision.counterexamples.iter().map(|c| {
                    let shaped = c.statements.iter().any(|id| analysis.model.constraints.iter().any(|k| matches!(k.kind, trion_language::ConstraintKind::Binding | trion_language::ConstraintKind::Form) && k.refs.first().is_some_and(|r| &r.id == id)));
                    if shaped {
                        Diagnostic::error("shape-violation", format!("these statements do not have the form that their role requires, where {}", c.facts.join(", ")), named(c))
                    } else {
                        Diagnostic::error("contradiction", format!("these statements cannot all be kept where {}", c.facts.join(", ")), named(c))
                    }
                })),
                "consistency" => found.push(Diagnostic::error("contradiction", why, refs)),
                "compatibility" => found.push(Diagnostic::error("incompatible", why, decision.counterexamples.first().map_or(refs, named))),
                "correctness" => found.push(Diagnostic::error("detail-not-refining", why, refs)),
                "completeness" => found.push(Diagnostic::error("detail-incomplete", why, refs)),
                "realizability" => found.push(Diagnostic::error("unrealizable", obligation.proposition.clone(), refs)),
                "recommendation" => found.push(Diagnostic::error("recommendation-violation", why, decision.counterexamples.first().map_or(refs, named))),
                "choice" if obligation.name.contains("/exclusive/") => found.push(Diagnostic::error("OVERLAPPING_FLOW_GUARDS", obligation.proposition.clone(), refs)),
                "choice" => found.push(Diagnostic::error("INCOMPLETE_FLOW_CHOICE", obligation.proposition.clone(), refs)),
                "check" => found.push(Diagnostic::error("check-refuted", why, refs)),
                "example" => found.push(Diagnostic::error("example-failed", obligation.proposition.clone(), refs)),
                "scenario" => found.push(Diagnostic::error("scenario-failed", obligation.proposition.clone(), refs)),
                other => panic!("the property `{other}` is not stated"),
            },
        }
    }
    analysis.diagnostics.extend(found);
    analysis
}

/// The verdict of each obligation of a set, by its name.
pub fn verdicts(set: &SpecSet, options: &Options) -> Vec<(String, ObligationVerdict)> {
    let analysis = analyze(set, options);
    let stated = proof_obligations(set, &analysis, options.bounds.trace_length);
    let inst = stated.instance(options.bounds.decisions);
    stated.obligations.iter().map(|o| (o.name.clone(), stated.decide(&inst, o).verdict)).collect()
}

/// The verdict of the obligation of consistency of a source.
pub fn consistency(src: &str, options: &Options) -> ObligationVerdict {
    verdicts(&set(src), options).into_iter().find(|(name, _)| name == "consistency").map(|(_, v)| v).expect("an obligation of consistency")
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
