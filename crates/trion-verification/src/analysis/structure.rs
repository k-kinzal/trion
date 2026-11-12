//! What can be told of a set without asking the solver: identifiers and
//! citations that resolve, units that agree, closed domains that are
//! covered, forms that a role requires, and statements that relate.

use super::*;

/// Checks the identifiers and the citations of each package: no identifier
/// is declared twice, and each reference, citation and trace names what the
/// package declares.
pub(super) fn check_identifiers(set: &SpecSet, out: &mut Vec<Diagnostic>) {
    check_duplicate_ids(set, out);
    check_references(set, out);
}

/// Checks what the compiled model shows without a search: every value of a
/// closed domain has a case, the quantities of a comparison share a unit,
/// `extend` names a closed domain, each sentence has a form that its
/// classifications allow, and each bound role has the forms that it requires.
pub(super) fn check_model(set: &SpecSet, model: &Model, lex: &Lexicon, out: &mut Vec<Diagnostic>) {
    find_missing_cases(model, out);
    find_unit_mismatches(model, out);
    check_extensions(set, model, lex, out);
    check_classifications(set, model, lex, out);
    find_required_missing(set, model, lex, out);
}

/// A quantity measured in two different units cannot be compared.
fn find_unit_mismatches(model: &Model, out: &mut Vec<Diagnostic>) {
    let mut units: BTreeMap<String, (BTreeSet<String>, Vec<SpecRef>)> = BTreeMap::new();
    for c in &model.constraints {
        let mut visit = |a: &trion_solver::Atom, _: bool| {
            if let trion_solver::Atom::Num { attr, unit, .. } = a {
                let entry = units.entry(attr.clone()).or_default();
                entry.0.insert(unit.clone());
                entry.1.extend(c.refs.iter().filter(|r| !entry.1.contains(r)).cloned().collect::<Vec<_>>());
            }
        };
        c.assume.atoms(true, &mut visit);
        c.guarantee.atoms(true, &mut visit);
    }
    for (attr, (found, refs)) in units {
        if found.len() > 1 {
            let list: Vec<String> = found.into_iter().map(|u| format!("`{u}`")).collect();
            out.push(Diagnostic::error("unit-mismatch", format!("{attr} is measured in {}, which cannot be compared", list.join(" and ")), refs));
        }
    }
    // A relation between quantities needs one unit for all of them.
    for c in &model.constraints {
        let mut visit = |a: &trion_solver::Atom, _: bool| {
            let trion_solver::Atom::Lin { terms, unit, .. } = a else { return };
            let mut measured: Vec<String> = Vec::new();
            let mut all: BTreeSet<&String> = BTreeSet::new();
            if !unit.is_empty() {
                all.insert(unit);
            }
            for (attr, _) in terms {
                for found in model.quantity_units.get(attr).into_iter().flatten() {
                    all.insert(found);
                    measured.push(format!("{attr} in `{found}`"));
                }
            }
            if all.len() > 1 {
                out.push(Diagnostic::error("unit-mismatch", format!("the quantities of one comparison are measured in different units, which cannot be compared: {}", measured.join(", ")), c.refs.clone()));
            }
        };
        c.assume.atoms(true, &mut visit);
        c.guarantee.atoms(true, &mut visit);
    }
}

fn mentions_attr(c: &trion_language::reading::Constraint, attr: &str) -> bool {
    c.assume.to_string().contains(&format!("Val({attr},")) || c.guarantee.to_string().contains(&format!("Dom({attr},"))
}

/// Finds the values of a closed domain that no condition handles.
fn find_missing_cases(model: &Model, out: &mut Vec<Diagnostic>) {
    for (attr, domain) in &model.closed_domains {
        let Some(guarded) = model.guarded_values.get(attr) else { continue };
        for value in domain.difference(guarded) {
            let refs = model.constraints.iter().filter(|c| c.kind != ConstraintKind::Binding && c.kind != ConstraintKind::Form && mentions_attr(c, attr)).flat_map(|c| c.refs.clone()).collect();
            out.push(Diagnostic::error("missing-case", format!("no specification covers the case where {attr} is {value}, and the domain of {attr} is closed"), refs));
        }
    }
}

fn role_subjects(f: &trion_solver::Formula, role: &str) -> Vec<String> {
    match f {
        trion_solver::Formula::Atom(trion_solver::Atom::Role { subject, role: r }) if r == role => vec![subject.clone()],
        trion_solver::Formula::And(xs) => xs.iter().flat_map(|x| role_subjects(x, role)).collect(),
        _ => Vec::new(),
    }
}

/// Checks a role's required forms. A role's specification set is known in full,
/// so an absent form is a definite omission.
fn find_required_missing(set: &SpecSet, model: &Model, lex: &Lexicon, out: &mut Vec<Diagnostic>) {
    let specs: Vec<(&Spec, Lexicon)> = set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| d.specs.iter().map(move |s| (s, lex.in_document(d)))).collect();
    for pkg in &set.packages {
        for (doc, role) in pkg.documents.iter().flat_map(|d| d.roles.iter().map(move |r| (d, r))) {
            let qualified = format!("{}.{}", trion_language::reading::role_prefix(&pkg.name, &doc.namespace), role.name);
            let bound: BTreeSet<String> = model.constraints.iter().flat_map(|c| role_subjects(&c.guarantee, &qualified)).collect();
            for subject in &bound {
                for rule in &role.required {
                    let satisfied = specs.iter().any(|(s, scoped)| trion_language::reading::match_core(&rule.pattern.core, &s.sentence.core).iter().any(|b| b.get(trion_language::reading::SUBJECT_VARIABLE).map(|v| scoped.resolve(&scoped.canon(v))).as_ref() == Some(subject)));
                    if !satisfied {
                        let at = SpecRef { id: format!("{qualified}::{}", rule.id), file: rule.file.clone(), line: rule.line, text: rule.text.clone() };
                        out.push(Diagnostic::error("missing-required-form", format!("{subject} is bound to {qualified} but has no specification of the required form `{}`", rule.pattern.source), vec![at]));
                    }
                }
            }
        }
    }
}

fn find(parent: &mut [usize], x: usize) -> usize {
    let mut root = x;
    while parent[root] != root {
        root = parent[root];
    }
    parent[x] = root;
    root
}

/// Links specifications that share a term, where a term also matches any
/// longer term it prefixes (`API` relates to `API GET /foo`).
pub(super) fn relate(set: &SpecSet, lex: &Lexicon) -> RelationReport {
    let scoped: Vec<(&Spec, Lexicon)> = set.packages.iter().filter(|p| p.is_root).flat_map(|p| &p.documents).flat_map(|d| d.specs.iter().map(move |s| (s, lex.in_document(d)))).collect();
    let specs: Vec<&Spec> = scoped.iter().map(|(s, _)| *s).collect();
    let raw: Vec<BTreeSet<String>> = scoped.iter().map(|(s, lex)| occurrences(&s.sentence, lex).into_iter().filter(|(_, k)| *k != "action").map(|(t, _)| t).collect()).collect();
    let known: BTreeSet<&String> = raw.iter().flatten().collect();
    let expanded: Vec<BTreeSet<String>> = raw
        .iter()
        .map(|terms| {
            let mut all = terms.clone();
            for term in terms {
                let words: Vec<&str> = term.split(' ').collect();
                for n in 1..words.len() {
                    let prefix = words[..n].join(" ");
                    if known.contains(&prefix) {
                        all.insert(prefix);
                    }
                }
            }
            all
        })
        .collect();

    let mut users: BTreeMap<&String, Vec<usize>> = BTreeMap::new();
    for (i, terms) in expanded.iter().enumerate() {
        for t in terms {
            users.entry(t).or_default().push(i);
        }
    }
    let mut parent: Vec<usize> = (0..specs.len()).collect();
    for list in users.values() {
        for pair in list.windows(2) {
            let (a, b) = (find(&mut parent, pair[0]), find(&mut parent, pair[1]));
            parent[a] = b;
        }
    }
    let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for i in 0..specs.len() {
        let r = find(&mut parent, i);
        groups.entry(r).or_default().push(i);
    }

    let mut report = RelationReport::default();
    for members in groups.values() {
        report.components.push(members.iter().map(|&i| specs[i].display_id()).collect());
        if let [only] = members.as_slice() {
            let s = specs[*only];
            report.isolated.push(SpecRef { id: s.display_id(), file: s.file.clone(), line: s.line, text: s.sentence.source.clone() });
        }
    }
    report.single_use_terms = users.iter().filter(|(_, l)| l.len() == 1).map(|(t, _)| (*t).clone()).collect();
    report
}

fn check_duplicate_ids(set: &SpecSet, out: &mut Vec<Diagnostic>) {
    for pkg in &set.packages {
        let mut seen: BTreeMap<&String, &Spec> = BTreeMap::new();
        for spec in pkg.documents.iter().flat_map(|d| &d.specs) {
            if let Some(id) = &spec.id {
                if let Some(first) = seen.insert(id, spec) {
                    let refs = [first, spec].iter().map(|s| SpecRef { id: s.display_id(), file: s.file.clone(), line: s.line, text: s.sentence.source.clone() }).collect();
                    out.push(Diagnostic::error("DUPLICATE_ID", format!("the identifier {id} is declared more than once"), refs));
                }
            }
        }
    }
}

/// Checks the identifiers and citations of each package.
fn check_references(set: &SpecSet, out: &mut Vec<Diagnostic>) {
    for pkg in &set.packages {
        let ids = pkg.identifiers();
        let mut parts: BTreeMap<&String, &Spec> = BTreeMap::new();
        let mut sources: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for source in pkg.documents.iter().flat_map(|d| &d.sources) {
            if sources.insert(source.name.as_str(), source.quotes.iter().map(|q| q.name.as_str()).collect()).is_some() {
                out.push(Diagnostic::error("DUPLICATE_ID", format!("the source {} is declared more than once", source.name), vec![SpecRef::point(&source.file, source.line, &source.name)]));
            }
            let mut names = BTreeSet::new();
            for quote in &source.quotes {
                if !names.insert(quote.name.as_str()) {
                    out.push(Diagnostic::error("DUPLICATE_ID", format!("the quote {} is declared twice in {}", quote.name, source.name), vec![SpecRef::point(&source.file, quote.line, &quote.name)]));
                }
            }
        }
        for spec in pkg.documents.iter().flat_map(|d| &d.specs) {
            for part in spec.parts.iter().filter(|p| p.as_str() != "concept-edge") {
                if let Some(first) = parts.insert(part, spec) {
                    let at = [first, spec].iter().map(|s| SpecRef { id: part.clone(), file: s.file.clone(), line: s.line, text: s.sentence.source.clone() }).collect();
                    out.push(Diagnostic::error("DUPLICATE_ID", format!("the identifier {part} is declared more than once"), at));
                }
            }
            for meta in &spec.meta {
                let Meta::Cite { source, quote } = meta else { continue };
                let known = sources.get(source.as_str()).is_some_and(|quotes| quote.as_ref().is_none_or(|q| quotes.contains(q.as_str())));
                if !known {
                    let name = quote.as_ref().map_or(source.clone(), |q| format!("{source}#{q}"));
                    out.push(Diagnostic::error("UNRESOLVED_CITATION", format!("the citation `{name}` names no declared source or quote"), vec![SpecRef { id: spec.display_id(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() }]));
                }
            }
        }
        for doc in &pkg.documents {
            for (id, line) in doc.references.iter().filter(|(id, _)| !id.starts_with("concept:")) {
                if !ids.contains(id) {
                    out.push(Diagnostic::error("UNRESOLVED_REFERENCE", format!("no element is identified as {id}"), vec![SpecRef::point(&doc.file, *line, id)]));
                }
            }
        }
    }
}

/// Reports `extend` on anything but a closed domain.
fn check_extensions(set: &SpecSet, model: &Model, lex: &Lexicon, out: &mut Vec<Diagnostic>) {
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let scoped = lex.in_namespace(&doc.namespace);
        for extension in &doc.extensions {
            let attr = scoped.resolve(&scoped.canon(&extension.attr));
            if !model.base_domains.contains_key(&attr) {
                let at = SpecRef { id: format!("{}:{}", extension.file, extension.line), file: extension.file.clone(), line: extension.line, text: extension.text.clone() };
                out.push(Diagnostic::error("extend-open-domain", format!("`{attr}` is not a closed domain, so there is no whole to extend"), vec![at]));
            }
        }
    }
}

/// Requires the syntactic form of each sentence to belong to every closed
/// domain that classifies it, unless the namespace declares the form as an
/// extension.
fn check_classifications(set: &SpecSet, model: &Model, lex: &Lexicon, out: &mut Vec<Diagnostic>) {
    let docs: Vec<_> = set.packages.iter().flat_map(|p| &p.documents).collect();
    for doc in &docs {
        let uses: BTreeSet<&String> = doc.imports.iter().map(|i| &i.namespace).collect();
        let mut attrs = BTreeSet::new();
        // A classification binds the blocks that use its namespace, not the
        // namespace that defines it.
        for source in docs.iter().filter(|d| !d.classifications.is_empty() && d.namespace != doc.namespace && uses.contains(&d.namespace)) {
            let scoped = lex.in_namespace(&source.namespace);
            attrs.extend(source.classifications.iter().map(|c| scoped.resolve(&scoped.canon(&c.attr))));
        }
        for attr in &attrs {
            let Some(base) = model.base_domains.get(attr) else { continue };
            let extended = |value: &str| model.domain_extensions.get(attr).is_some_and(|all| all.iter().any(|(v, ns)| v == value && (*ns == doc.namespace || uses.contains(ns))));
            for spec in &doc.specs {
                for form in trion_language::syntax::syntax_forms(&spec.sentence) {
                    if !base.contains(form) && !extended(form) {
                        let at = SpecRef { id: spec.display_id(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
                        out.push(Diagnostic::error("syntax-not-allowed", format!("this sentence uses {form}, which `{attr}` does not include; rewrite it or declare `extend {attr} with {form}.`"), vec![at]));
                    }
                }
            }
        }
    }
}

/// Reports each accepted behavioural statement that compiles to no contract,
/// with the obligations that therefore say nothing about it.
pub(super) fn find_unsupported(set: &SpecSet, model: &Model, out: &mut Vec<Diagnostic>) {
    for pkg in set.packages.iter().filter(|p| p.is_root) {
        for doc in &pkg.documents {
            for spec in &doc.specs {
                if !matches!(spec.sentence.core, Core::Deontic { .. }) {
                    continue;
                }
                let id = spec.display_id();
                let nested = format!("{id}/");
                if model.constraints.iter().any(|c| c.refs.iter().any(|r| r.file == spec.file && (r.id == id || r.id.starts_with(&nested)))) {
                    continue;
                }
                let mut affected = vec!["the consistency result".to_string()];
                for d in &pkg.documents {
                    affected.extend(d.checks.iter().filter(|c| c.left.iter().chain(&c.right).any(|o| *o == id)).map(|c| format!("check {}", c.name)));
                    affected.extend(d.examples.iter().filter(|e| e.base.iter().chain(&e.candidate).any(|o| *o == id)).map(|e| format!("example {}", e.name)));
                }
                let at = SpecRef { id, file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
                out.push(Diagnostic::warning("UNSUPPORTED_SEMANTICS", format!("this statement has no supported formal interpretation; it is left out of {}", affected.join(", ")), vec![at]));
            }
        }
    }
}
