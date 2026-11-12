//! Four properties of the whole package that the reader must have, checked
//! for every statement.
//!
//! - *Context independence.* The local reading of a statement, compiled from
//!   the statement with only the definitions and the vocabulary of the
//!   package and the statements that it names, equals its local reading in
//!   the package.
//! - *Relation locality.* A relation between entries is found again when it
//!   is computed from the statements that it names and the definitions alone.
//! - *Order independence.* Reordering the statements within one explicit
//!   scope changes no entry and no outcome: the reversed order and one
//!   seeded shuffle are tried.
//! - *Round trip.* The model of the output of `trion expand` equals the
//!   model of the package.
//!
//! Each violation is an error. `TRION_FAULT` seeds a violation of one
//! property, so that a fixture can show that the gate fails.

use super::{analyze, local_reading, relation_keys, Analysis, Isolation, Options};
use trion_language::{Diagnostic, Severity, SpecRef};
use trion_language::document::{parse_statement, Document, Spec, SpecSet};
use trion_solver::Formula;
use trion_language::reading::Model;
use trion_language::syntax::ast::Core;
use std::collections::{BTreeMap, BTreeSet};

/// The seeded defect of a test run, when the environment names one.
fn fault(name: &str) -> bool {
    std::env::var("TRION_FAULT").is_ok_and(|value| value == name)
}

fn at(spec: &Spec) -> SpecRef {
    SpecRef { id: spec.display_id(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() }
}

/// The root statements of a set, each with its document.
fn root_statements(set: &SpecSet) -> Vec<(&Document, &Spec, &str)> {
    set.packages.iter().filter(|p| p.is_root).flat_map(|p| p.documents.iter().flat_map(move |d| d.specs.iter().map(move |s| (d, s, p.name.as_str())))).collect()
}

/// A document of the namespace of `doc` that holds the given statements only.
fn alone(doc: &Document, specs: Vec<Spec>) -> Document {
    Document { namespace: doc.namespace.clone(), file: doc.file.clone(), imports: doc.imports.clone(), specs, ..Document::default() }
}

fn in_parallel<T: Sync, R: Send>(items: &[T], work: impl Fn(&T) -> Option<R> + Sync) -> Vec<R> {
    let threads = std::thread::available_parallelism().map_or(4, usize::from).min(items.len().max(1));
    let size = items.len().div_ceil(threads).max(1);
    std::thread::scope(|scope| {
        let handles: Vec<_> = items.chunks(size).map(|chunk| scope.spawn(|| chunk.iter().filter_map(&work).collect::<Vec<R>>())).collect();
        handles.into_iter().flat_map(|handle| handle.join().unwrap_or_default()).collect()
    })
}

/// Context independence: each statement read alone has the local reading
/// that it has in the package.
fn context(set: &SpecSet, package: &Model, scope: usize) -> Vec<Diagnostic> {
    let isolation = Isolation::of(set, scope);
    let statements = root_statements(set);
    let by_id: BTreeMap<String, &Spec> = statements.iter().map(|(_, s, _)| (s.display_id(), *s)).collect();
    let seeded = fault("context");
    in_parallel(&statements, |(doc, spec, name)| {
        let id = spec.display_id();
        // A definition is part of what every statement is read with.
        let mut specs = if matches!(spec.sentence.core, Core::Definition { .. }) { Vec::new() } else { vec![(*spec).clone()] };
        for named in spec.details.iter().chain(&spec.overrides) {
            if let Some(other) = by_id.get(named).filter(|o| !matches!(o.sentence.core, Core::Definition { .. })) {
                specs.push((*other).clone());
            }
        }
        let mini = isolation.compile_naming(name, vec![alone(doc, specs)], &spec.sentence.source);
        let mut here = local_reading(&mini, &id);
        let there = local_reading(package, &id);
        if seeded {
            here.push("seeded: a reading that depends on the context".to_string());
        }
        (here != there).then(|| {
            let differing = here.iter().zip(&there).find(|(a, b)| a != b).map_or_else(|| format!("{} lines alone, {} lines in the package", here.len(), there.len()), |(a, b)| format!("alone `{a}`, in the package `{b}`"));
            Diagnostic::error("context-dependent", format!("the local reading of `{id}` depends on what stands around it: {differing}"), vec![at(spec)])
        })
    })
}

/// Relation locality: each relation of the package is found again among the
/// statements that it names and the definitions.
fn relations(set: &SpecSet, base: &Analysis, options: &Options) -> Vec<Diagnostic> {
    let Some(proof) = &base.proof else { return Vec::new() };
    let isolation = Isolation::of(set, options.bounds.scope);
    let statements = root_statements(set);
    let by_id: BTreeMap<String, (&Document, &Spec, &str)> = statements.iter().map(|(d, s, n)| (s.display_id(), (*d, *s, *n))).collect();
    let seeded = fault("relation");
    in_parallel(&proof.relations, |relation| {
        let key = format!("{} {} <- {}", relation.kind, relation.subject.id, relation.rests_on.iter().map(|r| r.id.as_str()).collect::<BTreeSet<_>>().into_iter().collect::<Vec<_>>().join(", "));
        let (doc, _, name) = by_id.get(&relation.subject.id)?;
        let mut documents: BTreeMap<&str, Document> = BTreeMap::new();
        // A definition that the relation names is read with itself.
        let mut definitions = String::new();
        for id in std::iter::once(&relation.subject.id).chain(relation.rests_on.iter().map(|r| &r.id)) {
            let Some((home, spec, _)) = by_id.get(id) else { continue };
            if matches!(spec.sentence.core, Core::Definition { .. }) {
                definitions.push_str(&spec.sentence.source);
                definitions.push(' ');
            } else {
                documents.entry(home.file.as_str()).or_insert_with(|| alone(home, Vec::new())).specs.push((*spec).clone());
            }
        }
        let _ = doc;
        let mini = isolation.set_naming(name, documents.into_values().collect(), &definitions);
        // A yielding rests on answers of the solver; a refinement is stated.
        let analysis = if matches!(relation.kind.as_str(), "refinement" | "applied" | "individuals") { analyze(&mini, &Options::read_only()) } else { analyze(&mini, &Options { bounds: options.bounds, ..Options::default() }) };
        let found = relation_keys(&analysis.model);
        (seeded || !found.contains(&key)).then(|| Diagnostic::error("relation-not-local", format!("the relation `{key}` is not found among the statements that it names and the definitions alone: it depends on other statements"), vec![relation.subject.clone()]))
    })
}

/// A formula as text, with the members of each conjunction and disjunction in one order.
fn canonical(formula: &Formula) -> String {
    let joined = |items: &[Formula], sign: &str| {
        let mut texts: Vec<String> = items.iter().map(canonical).collect();
        texts.sort();
        texts.dedup();
        format!("({})", texts.join(sign))
    };
    match formula {
        Formula::True => "⊤".to_string(),
        Formula::Atom(atom) => atom.to_string(),
        Formula::Not(inner) => format!("¬{}", canonical(inner)),
        Formula::And(items) => joined(items, " ∧ "),
        Formula::Or(items) => joined(items, " ∨ "),
        Formula::Implies(a, b) => format!("({} → {})", canonical(a), canonical(b)),
    }
}

/// What a certified analysis says, without source locations and revisions:
/// each entry with its local reading and its formula, the background, the
/// relations and the outcomes.
fn signature(analysis: &Analysis) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    if let Some(proof) = &analysis.proof {
        for entry in &proof.entries {
            let id = entry.statement.as_ref().map_or_else(|| format!("constraint {}", entry.constraint), |s| s.id.clone());
            let text = format!("{} {:?} {} => {} | {} | {}", entry.kind.as_str(), entry.weight, canonical(&entry.local_assume), canonical(&entry.local_guarantee), canonical(&proof.pool[entry.formula]), entry.condition.map_or(String::new(), |c| canonical(&proof.pool[c])));
            out.entry(format!("entry {id}")).or_insert_with(String::new).push_str(&text);
        }
        let background: BTreeSet<String> = proof.background.iter().map(|&f| canonical(&proof.pool[f])).collect();
        for (number, text) in background.into_iter().enumerate() {
            out.insert(format!("background {number}"), text);
        }
    }
    for key in relation_keys(&analysis.model) {
        out.insert(format!("relation {key}"), "stated".to_string());
    }
    out.insert("status".to_string(), format!("{:?}", analysis.consistency.status));
    out.insert("verdict".to_string(), analysis.consistency.verdict.clone());
    for check in &analysis.checks {
        out.insert(format!("check {}", check.name), check.result.clone());
    }
    for example in &analysis.examples {
        out.insert(format!("example {}", example.name), example.observed.clone());
    }
    let mut codes: BTreeMap<&str, usize> = BTreeMap::new();
    for diagnostic in analysis.diagnostics.iter().chain(&analysis.silence.opaque).chain(&analysis.silence.ungrounded) {
        *codes.entry(diagnostic.code.as_str()).or_default() += 1;
    }
    for (code, count) in codes {
        out.insert(format!("diagnostics {code}"), count.to_string());
    }
    out.insert("conflicts".to_string(), analysis.conflicts.len().to_string());
    out
}

/// The set with the statements of each explicit scope in another order:
/// reversed, or shuffled from a seed.
fn reordered(set: &SpecSet, seed: Option<u64>) -> SpecSet {
    let mut out = set.clone();
    let mut state = seed.unwrap_or(0);
    for doc in out.packages.iter_mut().filter(|p| p.is_root).flat_map(|p| &mut p.documents) {
        let mut start = 0;
        while start < doc.specs.len() {
            let mut end = start + 1;
            while end < doc.specs.len() && doc.specs[end].scopes == doc.specs[start].scopes {
                end += 1;
            }
            let run = &mut doc.specs[start..end];
            match seed {
                None => run.reverse(),
                Some(_) => {
                    for i in (1..run.len()).rev() {
                        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                        run.swap(i, (state >> 33) as usize % (i + 1));
                    }
                }
            }
            start = end;
        }
    }
    out
}

/// Order independence: the reversed order and one seeded shuffle give the
/// entries and the outcomes of the package.
fn order(set: &SpecSet, base: &Analysis, options: &Options) -> Vec<Diagnostic> {
    let first = signature(base);
    let orders = [("reversed", None), ("shuffled with the seed 1", Some(1))];
    let seeded = fault("order");
    let found: Vec<Vec<Diagnostic>> = in_parallel(&orders, |(name, seed)| {
        let analysis = analyze(&reordered(set, *seed), &Options { certificates: true, outline: true, ..options.clone() });
        let mut second = signature(&analysis);
        if seeded {
            second.insert("status".to_string(), "seeded".to_string());
        }
        let labels: BTreeSet<&String> = first.keys().chain(second.keys()).collect();
        let differing: Vec<&String> = labels.into_iter().filter(|label| first.get(*label) != second.get(*label)).collect();
        Some(differing.iter().take(10).map(|label| Diagnostic::error("order-dependent", format!("`{label}` differs when the statements of each scope are {name}: `{}` in the written order and `{}` then", first.get(*label).map_or("absent", String::as_str), second.get(*label).map_or("absent", String::as_str)), Vec::new())).chain((differing.len() > 10).then(|| Diagnostic::error("order-dependent", format!("{} further parts differ when the statements of each scope are {name}", differing.len() - 10), Vec::new()))).collect())
    });
    found.into_iter().flatten().collect()
}

/// The readings of a model, by statement: its contracts and its temporal shape.
fn readings(model: &Model) -> BTreeMap<String, Vec<String>> {
    let ids: BTreeSet<String> = model.constraints.iter().filter_map(|c| c.refs.first().map(|r| r.id.clone())).collect();
    let mut out: BTreeMap<String, Vec<String>> = ids.into_iter().map(|id| (id.clone(), local_reading(model, &id))).collect();
    for lines in out.values_mut() {
        lines.sort();
    }
    let mut background: Vec<String> = model.background.iter().map(canonical).collect();
    background.sort();
    background.dedup();
    out.insert("the background".to_string(), background);
    out
}

/// Round trip: the package with each statement replaced by its expansion in
/// controlled English has the model of the package.
fn round_trip(set: &SpecSet, package: &Model) -> Vec<Diagnostic> {
    let mut expanded = set.clone();
    let mut out = Vec::new();
    for doc in expanded.packages.iter_mut().filter(|p| p.is_root).flat_map(|p| &mut p.documents) {
        let mut specs = Vec::new();
        for spec in std::mem::take(&mut doc.specs) {
            // A bound variable is read again by its mark: the letter alone needs the statement around it.
            let text = trion_language::expand::expand_with_marks(&spec);
            let written_alone = spec.scopes.is_empty() && spec.elements.is_empty() && spec.expansion.is_none() && spec.diagram.is_none();
            // A statement whose expansion is its own text, as a sentence that inherits
            // nothing and a flow with choices, is read as it stands.
            let _ = written_alone;
            if text.trim() == spec.sentence.source.trim() {
                specs.push(spec);
                continue;
            }
            let (parsed, diags) = parse_statement(&text);
            if let Some(error) = diags.iter().find(|d| d.severity == Severity::Error) {
                out.push(Diagnostic::error("round-trip-differs", format!("the expansion of `{}` is not read again: {}", spec.display_id(), error.message), vec![at(&spec)]));
                specs.push(spec);
                continue;
            }
            for sentence in parsed.specs {
                specs.push(Spec { sentence: sentence.sentence, scopes: sentence.scopes, expansion: None, elements: Vec::new(), diagram: None, ..spec.clone() });
            }
        }
        doc.specs = specs;
    }
    let (first, mut second) = (readings(package), readings(&analyze(&expanded, &Options::read_only()).model));
    if fault("roundtrip") {
        second.insert("the background".to_string(), vec!["seeded".to_string()]);
    }
    let labels: BTreeSet<&String> = first.keys().chain(second.keys()).collect();
    let differing: Vec<&String> = labels.into_iter().filter(|label| first.get(*label) != second.get(*label)).collect();
    for label in differing.iter().take(10) {
        let (a, b) = (first.get(*label).cloned().unwrap_or_default(), second.get(*label).cloned().unwrap_or_default());
        let line = a.iter().find(|l| !b.contains(l)).or_else(|| b.iter().find(|l| !a.contains(l))).cloned().unwrap_or_default();
        out.push(Diagnostic::error("round-trip-differs", format!("the model of the expansion differs from the model of the package at `{label}`: `{line}` stands in one of them only"), Vec::new()));
    }
    if differing.len() > 10 {
        out.push(Diagnostic::error("round-trip-differs", format!("{} further statements differ between the expansion and the package", differing.len() - 10), Vec::new()));
    }
    out
}

/// The violations of the four properties in a set. `base` is the certified
/// analysis of the set, and `options` are the options that it was run with.
pub fn check(set: &SpecSet, base: &Analysis, options: &Options) -> Vec<Diagnostic> {
    let scope = base.model.instance_scope.unwrap_or(options.bounds.scope);
    // The four properties do not depend on each other.
    let started = std::time::Instant::now();
    let timed = |what: &str, found: Vec<Diagnostic>| {
        if std::env::var_os("TRION_PROFILE").is_some() {
            eprintln!("profile: {:>8.3}s property: {what}", started.elapsed().as_secs_f64());
        }
        found
    };
    std::thread::scope(|threads| {
        let context = threads.spawn(|| timed("context", context(set, &base.model, scope)));
        let relations = threads.spawn(|| timed("relations", relations(set, base, options)));
        let order = threads.spawn(|| timed("order", order(set, base, options)));
        let round_trip = threads.spawn(|| timed("round trip", round_trip(set, &base.model)));
        [context, relations, order, round_trip].into_iter().flat_map(|handle| handle.join().unwrap_or_default()).collect()
    })
}
