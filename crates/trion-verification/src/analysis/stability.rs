//! Stability: a result is decided within bounds, and an outcome that
//! changes when a bound is raised says nothing about the specification.
//!
//! The set is decided again with each bound raised by one and by two, one
//! bound at a time. An outcome that differs from that of the first run is
//! reported as `bound-sensitive`.

use super::{Analysis, Bounds, Options};
use std::collections::{BTreeMap, BTreeSet};
use trion_language::document::SpecSet;
use trion_language::Diagnostic;

/// The outcomes of an analysis that the bounds may change, by what each is about.
fn outcomes(analysis: &Analysis) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    out.insert("status".to_string(), analysis.consistency.status.as_str().to_string());
    out.insert("verdict".to_string(), analysis.consistency.verdict.clone());
    out.insert("conflicts".to_string(), analysis.conflicts.len().to_string());
    for check in &analysis.checks {
        out.insert(format!("check {}", check.name), check.result.clone());
    }
    // An example of a reading shows an entry, which names the individuals of
    // its domain: only what the solver decides is compared.
    for example in analysis.examples.iter().filter(|e| e.kind == "consistency" || e.kind == "comparison") {
        out.insert(format!("example {}", example.name), example.observed.clone());
    }
    out
}

/// The outcomes of a set that depend on the bounds. `base` is the analysis
/// of the set at the bounds of `options`.
pub fn check(set: &SpecSet, base: &Analysis, options: &Options) -> Vec<Diagnostic> {
    let (k, n) = (options.bounds.trace_length.max(2), base.model.instance_scope.unwrap_or(options.bounds.scope));
    let name = |(moments, individuals): (usize, usize)| format!("({moments} moments, {individuals} individuals)");
    let first = outcomes(base);
    let later: Vec<((usize, usize), BTreeMap<String, String>)> = std::thread::scope(|scope| {
        let handles: Vec<_> = [(k + 1, n), (k + 2, n), (k, n + 1), (k, n + 2)]
            .into_iter()
            .map(|(moments, individuals)| {
                scope.spawn(move || {
                    let bounds = Bounds { trace_length: moments, scope: individuals, ..options.bounds };
                    // What does not depend on the bounds is taken from the first run.
                    ((moments, individuals), outcomes(&base.again(set, &Options { bounds, ..options.clone() })))
                })
            })
            .collect();
        handles.into_iter().filter_map(|handle| handle.join().ok()).collect()
    });
    let mut out = Vec::new();
    if later.len() != 4 {
        out.push(Diagnostic::error("bound-sensitive", "a run at raised bounds ended without a result", Vec::new()));
    }
    // Each later run is compared with the first one: a difference between two
    // later runs is a difference of one of them from the first.
    for (bounds, found) in &later {
        let labels: BTreeSet<&String> = first.keys().chain(found.keys()).collect();
        for label in labels {
            let (before, after) = (first.get(label).map_or("no outcome", String::as_str), found.get(label).map_or("no outcome", String::as_str));
            if before != after {
                out.push(Diagnostic::error("bound-sensitive", format!("`{label}` is `{before}` at {} and `{after}` at {}: the outcome depends on the bounds", name((k, n)), name(*bounds)), Vec::new()));
            }
        }
    }
    out
}
