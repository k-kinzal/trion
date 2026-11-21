//! Reading statements alone: with the definitions and the vocabulary of
//! their set and with nothing else that stands around them.

use super::*;

/// The unrolled formula of each statement of `ids` over a trace of `length`
/// moments, and the unrolled background that the statements add to that of
/// the package (`baseline`).
pub(super) fn unrolled_lines(model: &Model, baseline: &Model, ids: &BTreeSet<String>, length: usize) -> Vec<String> {
    let trace = trion_language::reading::unroll(model, length);
    let mut lines = Vec::new();
    for (constraint, (formula, condition)) in model.constraints.iter().zip(&trace.groups) {
        if !constraint.refs.first().is_some_and(|at| ids.contains(&at.id)) {
            continue;
        }
        lines.push(format!("unrolled: {formula}"));
        if let Some(condition) = condition {
            lines.push(format!("condition: {condition}"));
        }
    }
    let known: BTreeSet<String> = trion_language::reading::unroll_background(baseline, length).iter().map(|f| f.to_string()).collect();
    let mut seen = BTreeSet::new();
    for axiom in &trace.background {
        let text = axiom.to_string();
        if !known.contains(&text) && seen.insert(text.clone()) {
            lines.push(format!("background: {text}"));
        }
    }
    lines
}

/// The definitions and the vocabulary of a set, from which a statement is
/// read alone: with its resolved terms and nothing that stands around it.
pub struct Isolation {
    /// The packages with their declarations and without a statement.
    packages: Vec<Package>,
    /// The definitions of each document, in their order.
    specs: Vec<Vec<Vec<Spec>>>,
    /// For each definition, by package, document and position: the words of
    /// its term and the words of its whole sentence.
    definitions: Vec<(usize, usize, usize, Vec<String>, Vec<String>)>,
    scope: usize,
}

/// The words of a text, each without its plural ending, for matching a term
/// against the statements that may name it. Matching too much is harmless:
/// it only keeps a definition that the statement does not use.
fn stems(text: &str) -> Vec<String> {
    text.split(|c: char| !c.is_alphanumeric())
        .filter(|w| !w.is_empty())
        .map(|w| w.to_lowercase())
        .filter(|w| !matches!(w.as_str(), "a" | "an" | "the"))
        .map(|mut w| {
            // `entries`, `entry`; `classes`, `class`; `references`, `reference`.
            for ending in ['s', 'e', 's'] {
                if w.len() > 2 && w.ends_with(ending) {
                    w.pop();
                }
            }
            if w.len() > 2 && w.ends_with('y') {
                w.pop();
                w.push('i');
            }
            w
        })
        .collect()
}

impl Isolation {
    pub fn of(set: &SpecSet, scope: usize) -> Self {
        // Every declaration stays: a term resolves as it does in the package.
        let mut packages: Vec<Package> = set.packages.iter().map(|pkg| Package {
            name: pkg.name.clone(),
            is_root: pkg.is_root,
            documents: pkg.documents.iter().map(|doc| {
                let mut kept = doc.clone();
                if doc.application_mapping.is_empty() {
                    kept.symbol_sources.extend(doc.specs.iter().filter(|spec| !matches!(spec.sentence.core, Core::Definition { .. })).cloned());
                }
                kept.specs.retain(|s| matches!(s.sentence.core, Core::Definition { .. }) || !doc.application_mapping.is_empty());
                kept.checks.clear();
                kept.propositional_checks.clear();
                kept.examples.clear();
                kept.sources.clear();
                kept.references.clear();
                kept.compatibility.clear();
                kept
            }).collect(),
        }).collect();
        let mut definitions = Vec::new();
        for (p, pkg) in packages.iter().enumerate() {
            for (d, doc) in pkg.documents.iter().enumerate() {
                for (i, spec) in doc.specs.iter().enumerate() {
                    if let Core::Definition { term, .. } = &spec.sentence.core {
                        definitions.push((p, d, i, stems(&term.render()), stems(&spec.sentence.source)));
                    }
                }
            }
        }
        // A set that reads a statement alone copies the definitions that it keeps, and no other.
        let specs: Vec<Vec<Vec<Spec>>> = packages.iter_mut().map(|pkg| pkg.documents.iter_mut().map(|doc| {
            if doc.application_mapping.is_empty() { std::mem::take(&mut doc.specs) } else { Vec::new() }
        }).collect()).collect();
        Isolation { packages, specs, definitions, scope }
    }

    /// The declarations, the definitions of the terms that `documents` name,
    /// and the definitions that those definitions name, together with
    /// `documents` of the package `name`: a statement is read with its
    /// resolved terms and with nothing else that stands around it.
    pub fn set(&self, name: &str, documents: Vec<Document>) -> SpecSet {
        self.set_naming(name, documents, "")
    }

    /// As `set`, with the definitions of the terms that `text` names as well:
    /// a definition is read with itself.
    pub fn set_naming(&self, name: &str, documents: Vec<Document>, text: &str) -> SpecSet {
        let mut words: BTreeSet<String> = documents.iter().flat_map(|d| &d.specs).flat_map(|s| stems(&s.sentence.source)).chain(stems(text)).collect();
        // `TRION_ISOLATION=all` keeps every definition: the two must agree.
        let mut kept = vec![std::env::var("TRION_ISOLATION").is_ok_and(|v| v == "all"); self.definitions.len()];
        loop {
            let mut grew = false;
            for (at, (_, _, _, term, body)) in self.definitions.iter().enumerate() {
                if !kept[at] && term.iter().all(|w| words.contains(w)) {
                    kept[at] = true;
                    grew = true;
                    words.extend(body.iter().cloned());
                }
            }
            if !grew {
                break;
            }
        }
        let mut packages = self.packages.clone();
        // The definitions are listed in the order of their documents.
        for (at, (p, d, i, _, _)) in self.definitions.iter().enumerate() {
            if kept[at] {
                packages[*p].documents[*d].specs.push(self.specs[*p][*d][*i].clone());
            }
        }
        packages.push(Package { name: name.to_string(), is_root: true, documents });
        SpecSet { packages, vocabulary_mode: VocabularyMode::Inferred }
    }

    /// The model of the definitions together with `documents` of the package `name`.
    pub fn compile(&self, name: &str, documents: Vec<Document>) -> Model {
        self.compile_naming(name, documents, "")
    }

    /// As `compile`, with the definitions of the terms that `text` names as well.
    pub fn compile_naming(&self, name: &str, documents: Vec<Document>, text: &str) -> Model {
        let isolated = self.set_naming(name, documents, text);
        trion_language::reading::compile(&isolated, &Lexicon::of(&isolated), self.scope)
    }
}

/// The local reading of a statement in a model: its contracts as their
/// author stated them and its temporal shape, before any relation to
/// another statement is applied.
pub(super) fn local_reading(model: &Model, id: &str) -> Vec<String> {
    let mut lines = Vec::new();
    for constraint in model.constraints.iter().filter(|c| !matches!(c.kind, ConstraintKind::Refinement | ConstraintKind::Carried) && c.refs.first().is_some_and(|at| at.id == id)) {
        lines.push(format!("{:?}: {} => {}", constraint.kind, trion_language::reading::authored_condition(model, constraint), constraint.guarantee));
    }
    for obligation in model.temporal.iter().filter(|o| o.statement.id == id) {
        lines.extend(obligation.lines().into_iter().map(|line| format!("temporal: {line}")));
    }
    lines
}

/// The relations between the entries of a model, each as one line: its
/// kind, the statement it is about and the statements it rests on.
pub(super) fn relation_keys(model: &Model) -> BTreeSet<String> {
    relations_of(model).iter().map(|r| format!("{} {} <- {}", r.kind, r.subject.id, r.rests_on.iter().map(|at| at.id.as_str()).collect::<BTreeSet<_>>().into_iter().collect::<Vec<_>>().join(", "))).collect()
}

/// The temporal forms that the reader distinguishes in the statements of
/// `ids`: how an obligation is activated, and which temporal phrases its
/// responses hold.
pub fn temporal_forms(model: &Model, ids: &BTreeSet<String>) -> BTreeSet<&'static str> {
    use trion_language::reading::Activation;
    let mut forms = BTreeSet::new();
    for obligation in model.temporal.iter().filter(|o| ids.contains(&o.statement.id)) {
        forms.insert(match obligation.activation {
            Activation::Occurrence { .. } => "activation by an occurrence",
            Activation::Invocation { .. } => "activation by an invocation",
            Activation::Interval { .. } => "activation throughout an interval",
            Activation::Always => "always",
        });
        if obligation.exception.is_some() {
            forms.insert("unless");
        }
        for response in &obligation.responses {
            if response.deadline.is_some() {
                forms.insert("deadline");
            }
            if !response.until.is_empty() {
                forms.insert("until");
            }
            for reference in &response.references {
                forms.insert(match reference.relation.as_str() {
                    "before" => "before",
                    "after" => "after",
                    "until" => "until",
                    _ => "temporal reference",
                });
            }
        }
    }
    forms
}
