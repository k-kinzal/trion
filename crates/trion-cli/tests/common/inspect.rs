//! What the libraries read from a project, as text: the contracts of the
//! statements, their expansion, the vocabulary and the relations. The
//! command shows none of these, so a test that examines a reading asks the
//! libraries here.

use super::Result;
use std::path::Path;
use trion_cli::project;
use trion_language::expand::{concept_edge, concept_notation, expand, expressions, flow_notation};
use trion_language::{glossary, rules, ConstraintKind};
use trion_verification::{analyze, smt2, Bounds, Options};

fn to_json<T: serde::Serialize>(value: &T) -> String {
    serde_json::to_string_pretty(value).unwrap()
}

/// Reads a view of the project at `dir`. The first argument names the view
/// (`model`, `vocab`, `relate`, `expand`, `glossary` or `diagram`); `--json`
/// asks for JSON, a path names the project, and `model` takes `--rules`,
/// `--smt2` and `--unrolled`.
pub fn inspect_in(dir: &Path, args: &[&str]) -> Result {
    let ok = |stdout: String| Result { code: 0, stdout, stderr: String::new() };
    let fail = |message: String| Result { code: 2, stdout: String::new(), stderr: format!("error: {message}\n") };
    let json = args.contains(&"--json");
    let flag = |name: &str| args.contains(&name);
    let value = |name: &str| args.iter().position(|a| *a == name).and_then(|at| args.get(at + 1)).and_then(|v| v.parse::<usize>().ok());
    let mut words = args.iter().copied().filter(|a| !a.starts_with("--")).filter(|a| a.parse::<usize>().is_err());
    let view = words.next().unwrap_or_default();
    let rest: Vec<&str> = words.collect();
    // A diagram names its kind and its statements; the other views name the project.
    let path = if view == "diagram" { args.iter().position(|a| *a == "--path").and_then(|at| args.get(at + 1)).copied().unwrap_or(".") } else { rest.first().copied().unwrap_or(".") };
    let project = match project::load(&dir.join(path)) {
        Ok(project) => project,
        Err(message) => return fail(message),
    };
    let mut out = String::new();
    match view {
        "model" if flag("--rules") => {
            for spec in project.set.packages.iter().filter(|p| p.is_root).flat_map(|p| &p.documents).flat_map(|d| &d.specs) {
                out.push_str(&format!("{}\n  rules: {}\n", spec.display_id(), rules(&spec.sentence).join(", ")));
            }
        }
        "model" => {
            let analysis = analyze(&project.set, &Options::read_only());
            let length = value("--trace-length").unwrap_or(Bounds::default().trace_length).max(2);
            if flag("--smt2") {
                out = smt2(&project.set, &analysis, length);
            } else if flag("--unrolled") {
                // Each contract over the trace, as the consistency of the package is decided.
                let trace = trion_language::reading::unroll(&analysis.model, length);
                for (constraint, (formula, _)) in analysis.model.constraints.iter().zip(&trace.groups) {
                    out.push_str(&format!("{}\n  {formula}\n", constraint.refs.first().map_or("", |r| r.id.as_str())));
                }
                for formula in &trace.background {
                    out.push_str(&format!("background\n  {formula}\n"));
                }
            } else if json {
                out = to_json(&analysis.model) + "\n";
            } else {
                for c in &analysis.model.constraints {
                    let id = c.refs.first().map(|r| r.id.as_str()).unwrap_or("");
                    out.push_str(&format!("{id}\n  assume:    {}\n  guarantee: {}\n", c.assume, c.guarantee));
                    // What the statement says about time stands beside its contract.
                    if matches!(c.kind, ConstraintKind::Spec | ConstraintKind::Permission) {
                        for obligation in analysis.model.temporal.iter().filter(|o| o.statement.id == id) {
                            for line in obligation.lines() {
                                out.push_str(&format!("  temporal:  {line}\n"));
                            }
                        }
                    }
                }
            }
        }
        "vocab" => {
            let analysis = analyze(&project.set, &Options::read_only());
            if json {
                out = to_json(&analysis.vocabulary) + "\n";
            } else {
                for e in analysis.vocabulary.values() {
                    let origin = e.declared_kind.as_deref().map_or("inferred".to_string(), |k| format!("declared {k}"));
                    let kinds: Vec<&str> = e.inferred_kinds.iter().map(String::as_str).collect();
                    out.push_str(&format!("{}\t{origin}\t{}\t{}\n", e.term, kinds.join(","), e.occurrences));
                }
            }
        }
        "relate" => {
            let analysis = analyze(&project.set, &Options::read_only());
            let r = &analysis.relations;
            if json {
                out = to_json(r) + "\n";
            } else {
                out.push_str(&format!("{} related groups\n", r.components.len()));
                for (i, c) in r.components.iter().enumerate() {
                    out.push_str(&format!("  group {}: {}\n", i + 1, c.join(", ")));
                }
                out.push_str(&format!("{} isolated specifications (review these for omissions)\n", r.isolated.len()));
                for s in &r.isolated {
                    out.push_str(&format!("  [{}] {}\n", s.id, s.text));
                }
                out.push_str(&format!("{} terms used by one specification\n", r.single_use_terms.len()));
                for t in &r.single_use_terms {
                    out.push_str(&format!("  {t}\n"));
                }
            }
        }
        "expand" => {
            let items: Vec<serde_json::Value> = project.root_specs().map(|spec| serde_json::json!({ "id": spec.display_id(), "expansion": expand(spec), "expressions": expressions(spec) })).collect();
            if json {
                out = to_json(&items) + "\n";
            } else {
                for item in &items {
                    out.push_str(&format!("[{}]\n{}\n\n", item["id"].as_str().unwrap_or_default(), item["expansion"].as_str().unwrap_or_default()));
                }
            }
        }
        "glossary" => {
            let analysis = analyze(&project.set, &Options::read_only());
            let entries = glossary(&analysis.vocabulary);
            if json {
                out = to_json(&entries) + "\n";
            } else {
                for entry in &entries {
                    out.push_str(&format!("{}\t{}\t{}\t{} uses\t{}\n", entry.term, entry.status, entry.namespace, entry.occurrences, entry.occurrences_at.join(",")));
                    if let Some(signature) = &entry.signature {
                        out.push_str(&format!("\tpredicate {}({}) declared at {}\n", entry.identity.as_deref().unwrap_or_default(), signature.join(", "), entry.declared_at.as_deref().unwrap_or_default()));
                    } else if let Some(at) = &entry.declared_at {
                        out.push_str(&format!("\tdeclared at {at}\n"));
                    }
                    if let (Some(at), Some(text)) = (&entry.defined_at, &entry.definition) {
                        out.push_str(&format!("\tdefined at {at}: {text}\n"));
                    }
                    if let Some(derivation) = &entry.derivation {
                        for ((kind, rule), premise) in derivation.interpretation.iter().zip(&derivation.rules).zip(&derivation.premises) {
                            out.push_str(&format!("\tderived as {kind}: {rule} ({premise})\n"));
                        }
                        for identity in &derivation.referenced {
                            out.push_str(&format!("\trefers to {identity}\n"));
                        }
                    }
                }
            }
        }
        // A generated view says what its statements say: each edge and each
        // flow is kept only when its expansion is the statement again.
        "diagram" => {
            let (kind, ids) = (rest.first().copied().unwrap_or_default(), rest.get(1..).unwrap_or_default());
            let chosen: Vec<_> = project.root_specs().filter(|s| ids.is_empty() || s.id.as_ref().is_some_and(|id| ids.contains(&id.as_str()))).collect();
            if let Some(missing) = ids.iter().find(|id| !chosen.iter().any(|s| s.id.as_deref() == Some(**id))) {
                return fail(format!("no statement is identified `{missing}`"));
            }
            match kind {
                "concept" => {
                    let edges: Vec<_> = chosen.iter().filter(|s| ids.is_empty() == s.expansion.is_none() || !ids.is_empty()).filter_map(|s| concept_edge(s)).collect();
                    if let Some(spec) = chosen.iter().find(|s| !ids.is_empty() && concept_edge(s).is_none()) {
                        return fail(format!("`{}` is not a relation of each instance of one type, so no concept edge restates it", spec.display_id()));
                    }
                    out = if json { to_json(&edges) + "\n" } else { concept_notation(None, &edges) };
                }
                "flow" => {
                    if ids.is_empty() {
                        return fail("name the ordered action list to restate".to_string());
                    }
                    for spec in &chosen {
                        match flow_notation(spec) {
                            Some(notation) => out.push_str(&notation),
                            None => return fail(format!("`{}` is not a triggered ordered action list, so no flow restates it", spec.display_id())),
                        }
                    }
                }
                other => return fail(format!("no view of the kind `{other}`: write `concept` or `flow`")),
            }
        }
        other => return fail(format!("no view `{other}`")),
    }
    ok(out)
}
