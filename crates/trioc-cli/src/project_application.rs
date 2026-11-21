//! A reference loads an interface. Application instantiates a checked
//! contract fragment and keeps the originating sentences.

use std::collections::{BTreeMap, BTreeSet};

use trion_language::document::{Binding, Document, Role};
use trion_language::reading::{
    mappable_nominal, match_core, occurrences, role_prefix, Lexicon, SUBJECT_VARIABLE,
};
use trion_language::syntax::ast::*;
use trion_language::{Diagnostic, SpecRef, SpecSet};

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ResolvedSpecification {
    pub name: String,
    pub package: String,
    pub namespace: String,
    pub exports_from: Vec<String>,
    pub file: String,
    pub line: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct AppliedSpecification {
    pub name: String,
    pub package: String,
    pub file: String,
    pub line: usize,
    pub mapping: BTreeMap<String, String>,
    pub statements: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub dependencies: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub nested: Vec<AppliedSpecification>,
}

/// `use` imports contracts. A `refer` edge loads an interface only.
fn use_closure(set: &SpecSet, start: &str) -> BTreeSet<String> {
    let mut active = BTreeSet::from([start.to_string()]);
    loop {
        let next: BTreeSet<String> = set
            .packages
            .iter()
            .filter(|package| active.contains(&package.name))
            .flat_map(|package| &package.documents)
            .flat_map(|doc| &doc.imports)
            .filter(|import| !import.reference_only)
            .map(|import| {
                import
                    .namespace
                    .split('.')
                    .next()
                    .unwrap_or_default()
                    .to_string()
            })
            .collect();
        let count = active.len();
        active.extend(next);
        if active.len() == count {
            return active;
        }
    }
}

fn role_name(doc: &Document, written: &str) -> String {
    let Some((namespace, role)) = written.rsplit_once('.') else {
        return written.to_string();
    };
    doc.imports
        .iter()
        .find_map(|import| {
            let tail = namespace.strip_prefix(&import.name)?;
            (tail.is_empty() || tail.starts_with('.'))
                .then(|| format!("{}{tail}.{role}", import.namespace))
        })
        .unwrap_or_else(|| written.to_string())
}

fn plain(group: &NpGroup) -> bool {
    matches!(group, NpGroup::Single(np) if np.of.is_none() && np.of_also.is_empty() && np.relative.is_none())
}

fn nominal(predicate: &Predicate) -> bool {
    matches!(predicate, Predicate::Words { nominal: Some(group), .. } if mappable_nominal(group))
}

fn argument_role(role: &RolePp) -> bool {
    match role {
        RolePp::Recipient(argument)
        | RolePp::Source(argument)
        | RolePp::Goal(argument)
        | RolePp::Topic(argument) => plain(argument),
        _ => false,
    }
}

fn clause(clause: &Clause) -> bool {
    plain(&clause.subject)
        && match &clause.body {
            ClauseBody::Verbal {
                object,
                roles,
                content: None,
                ..
            } => object.as_ref().is_none_or(plain) && roles.iter().all(argument_role),
            ClauseBody::Copular {
                predicate,
                agent: None,
                roles,
                ..
            } => roles.is_empty() && nominal(predicate),
            _ => false,
        }
}

fn simple_vp(vp: &Vp) -> bool {
    vp.object.as_ref().is_none_or(plain)
        && vp.complement.is_none()
        && vp.content.is_none()
        && vp.roles.iter().all(|role| {
            argument_role(role)
                || matches!(
                    role,
                    RolePp::Deadline(Measure::Quantity { .. })
                        | RolePp::Duration(Measure::Quantity { .. })
                )
        })
}

fn supported(sentence: &Sentence) -> bool {
    if sentence.necessary.is_some() || sentence.iff.is_some() || sentence.concession.is_some() {
        return false;
    }
    let frames = sentence
        .frames
        .scopes
        .iter()
        .chain(&sentence.frames.states)
        .map(|frame| &frame.clause)
        .chain(
            sentence
                .frames
                .trigger
                .iter()
                .map(|trigger| &trigger.clause),
        );
    if !frames
        .flat_map(|group| &group.items)
        .chain(&sentence.exception)
        .all(clause)
    {
        return false;
    }
    match &sentence.core {
        Core::Deontic {
            subject,
            vp: VpGroup::Single(vp),
            ..
        }
        | Core::Relation {
            subject,
            vp: VpGroup::Single(vp),
        } => plain(subject) && simple_vp(vp),
        Core::Existence { subject } => plain(subject),
        // Validated as part of the source interface. An abbreviation is
        // expanded at a use and contributes no contract on its own.
        Core::Definition { .. } => true,
        Core::Description {
            subject,
            predicate,
            agent: None,
            roles,
            ..
        } => plain(subject) && roles.is_empty() && nominal(predicate),
        _ => false,
    }
}

fn is_actor(kind: &str) -> bool {
    matches!(kind, "entity" | "attribute")
}

fn compatible_kind(actual: &str, expected: &str) -> bool {
    actual == expected
        || matches!(
            (actual, expected),
            ("entity" | "object", "entity" | "object")
        )
}

pub(crate) fn expand(
    set: &mut SpecSet,
    diagnostics: &mut Vec<Diagnostic>,
) -> (Vec<ResolvedSpecification>, Vec<AppliedSpecification>) {
    let mut references = Vec::new();
    let mut recorded = Vec::new();
    let Some(root) = set.packages.iter().find(|package| package.is_root) else {
        return (references, recorded);
    };
    if set
        .packages
        .iter()
        .flat_map(|pkg| &pkg.documents)
        .all(|doc| {
            doc.applications.is_empty()
                && doc.imports.iter().all(|import| !import.reference_only)
                && doc.bindings.is_empty()
        })
    {
        return (references, recorded);
    }
    let lexicon = Lexicon::of(set);
    let (table, _) = trion_language::reading::build_table(set, &lexicon);
    let roles: BTreeMap<String, (&str, &str, &Role)> = set
        .packages
        .iter()
        .flat_map(|package| {
            package.documents.iter().flat_map(move |doc| {
                let namespace = role_prefix(&package.name, &doc.namespace);
                doc.roles.iter().map(move |role| {
                    (
                        format!("{namespace}.{}", role.name),
                        (package.name.as_str(), namespace, role),
                    )
                })
            })
        })
        .collect();
    // Dependencies arrive in postorder. Each owner can compose mappings
    // with the applications already prepared by its dependencies.
    let owners = set
        .packages
        .iter()
        .filter(|package| !package.is_root)
        .chain([root]);
    let mut planned = BTreeMap::<String, Vec<(String, Document)>>::new();
    let mut declared_applications = BTreeMap::<String, Vec<AppliedSpecification>>::new();
    let mut processed = BTreeSet::new();
    for owner in owners {
        let target_types: BTreeSet<String> = owner
            .documents
            .iter()
            .flat_map(|doc| {
                let scoped = lexicon.in_document(doc);
                doc.individuals
                    .iter()
                    .map(move |decl| scoped.resolve(&scoped.canon(&decl.name)))
            })
            .collect();
        let mut names = BTreeSet::new();
        for doc in &owner.documents {
            let lex = lexicon.in_document(doc);
            for import in doc.imports.iter().filter(|import| import.reference_only) {
                let at =
                    SpecRef::point(&import.file, import.line, &format!("refer {}", import.name));
                if let Some(package) = set
                    .packages
                    .iter()
                    .find(|package| package.name == import.namespace && package.name != owner.name)
                {
                    let exports_from = package
                        .documents
                        .iter()
                        .map(|doc| doc.namespace.clone())
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect();
                    references.push(ResolvedSpecification {
                        name: import.name.clone(),
                        package: package.name.clone(),
                        namespace: doc.namespace.clone(),
                        exports_from,
                        file: import.file.clone(),
                        line: import.line,
                    });
                } else {
                    diagnostics.push(Diagnostic::error(
                        "unresolved-import",
                        format!("`{}` must name a dependency package", import.name),
                        vec![at],
                    ));
                }
            }
            for application in &doc.applications {
                let mut errors = Vec::new();
                let reference = doc
                    .imports
                    .iter()
                    .find(|import| import.name == application.dependency && import.reference_only);
                let Some(reference) = reference else {
                    diagnostics.push(Diagnostic::error(
                        "unresolved-import",
                        format!(
                            "application `{}` needs a resolved reference to `{}` in this namespace",
                            application.name, application.dependency
                        ),
                        vec![application.at.clone()],
                    ));
                    continue;
                };
                let Some(source) = set
                    .packages
                    .iter()
                    .find(|pkg| pkg.name == reference.namespace && pkg.name != owner.name)
                else {
                    diagnostics.push(Diagnostic::error(
                        "unresolved-import",
                        format!(
                            "application `{}` must select a dependency package",
                            application.name
                        ),
                        vec![application.at.clone()],
                    ));
                    continue;
                };
                if !names.insert(application.name.clone()) {
                    diagnostics.push(Diagnostic::error(
                        "DUPLICATE_ID",
                        format!(
                            "application `{}` is already named in this package",
                            application.name
                        ),
                        vec![application.at.clone()],
                    ));
                    continue;
                }
                let mut expected = BTreeMap::<String, BTreeSet<&str>>::new();
                let mut boundary = BTreeMap::new();
                let closure = use_closure(set, &source.name);
                if set
                    .packages
                    .iter()
                    .filter(|package| closure.contains(&package.name))
                    .any(|package| {
                        !processed.contains(&package.name)
                            && package
                                .documents
                                .iter()
                                .any(|doc| !doc.applications.is_empty())
                    })
                {
                    diagnostics.push(Diagnostic::error(
                        "UNSUPPORTED_SEMANTICS",
                        format!(
                            "cyclic application dependencies reach `{}` from `{}`",
                            source.name, owner.name
                        ),
                        vec![application.at.clone()],
                    ));
                    continue;
                }
                let documents: Vec<_> = set
                    .packages
                    .iter()
                    .filter(|package| closure.contains(&package.name))
                    .flat_map(|package| {
                        package
                            .documents
                            .iter()
                            .map(move |doc| (package.name.as_str(), doc))
                    })
                    .chain(
                        closure
                            .iter()
                            .filter_map(|name| planned.get(name))
                            .flatten()
                            .map(|(package, doc)| (package.as_str(), doc)),
                    )
                    .collect();
                let mut source_types = BTreeSet::new();
                let mut role_bindings = BTreeMap::<usize, Vec<Binding>>::new();
                let mut bound = BTreeSet::new();
                let mut activations = BTreeSet::new();
                for (index, (_, source_doc)) in documents.iter().enumerate() {
                    if !source_doc.extensions.is_empty() || !source_doc.classifications.is_empty() {
                        errors.push((
                            "UNSUPPORTED_SEMANTICS",
                            format!(
                                "namespace `{}` contains extensions or classifications that require a separate application rule",
                                source_doc.namespace
                            ),
                        ));
                        continue;
                    }
                    for spec in &source_doc.specs {
                        if !supported(&spec.sentence) || !spec.overrides.is_empty() || spec.default
                        {
                            errors.push((
                                "UNSUPPORTED_SEMANTICS",
                                format!(
                                    "application `{}` cannot instantiate `{}` in `{}` ({}:{}): {}",
                                    application.name,
                                    spec.display_id(),
                                    source_doc.namespace,
                                    spec.file,
                                    spec.line,
                                    spec.sentence.render(),
                                ),
                            ));
                        }
                    }
                    let source_lex = lexicon.in_document(source_doc);
                    for declared in &source_doc.individuals {
                        let key = source_lex.resolve(&source_lex.canon(&declared.name));
                        source_types.insert(key.clone());
                        expected.entry(key).or_default();
                    }
                    for control in &source_doc.controls {
                        let key = source_lex.resolve(&source_lex.canon(&control.name));
                        if boundary
                            .insert(key.clone(), control.by.as_str())
                            .is_some_and(|previous| previous != control.by)
                        {
                            errors.push(("vocabulary-kind-conflict", format!("source actor `{key}` has conflicting responsibility declarations")));
                        }
                        expected.entry(key).or_default().insert("entity");
                    }
                    for binding in &source_doc.bindings {
                        let key = role_name(source_doc, &binding.role);
                        let visible = roles.get(&key).is_some_and(|(package, namespace, _)| {
                            closure.contains(*package)
                                || source_doc.application_scope.is_some()
                                || source_doc.imports.iter().any(|import| {
                                    *namespace == import.namespace
                                        || namespace.starts_with(&format!("{}.", import.namespace))
                                })
                        });
                        if !visible {
                            errors.push((
                                "unresolved-import",
                                format!(
                                    "source form role `{}` is not available in `{}`",
                                    binding.role, source_doc.namespace
                                ),
                            ));
                            continue;
                        }
                        let subject = source_lex.resolve(&source_lex.canon(&binding.term));
                        expected
                            .entry(subject.clone())
                            .or_default()
                            .insert("entity");
                        bound.insert((key.clone(), subject));
                        role_bindings.entry(index).or_default().push(Binding {
                            role: key,
                            ..binding.clone()
                        });
                    }
                    for (role, targets) in &source_doc.application_roles {
                        bound.extend(targets.iter().map(|target| (role.clone(), target.clone())));
                    }
                    for spec in &source_doc.specs {
                        if matches!(spec.sentence.core, Core::Definition { .. }) {
                            continue;
                        }
                        for (symbol, kind) in occurrences(&spec.sentence, &source_lex) {
                            if kind == "action" {
                                if let Some(predicate) = source_lex.predicate_identity(&symbol) {
                                    expected.entry(predicate).or_default().insert("predicate");
                                }
                            } else {
                                expected.entry(symbol).or_default().insert(kind);
                            }
                        }
                    }
                }
                if !errors.is_empty() {
                    diagnostics.extend(errors.into_iter().map(|(code, message)| {
                        Diagnostic::error(code, message, vec![application.at.clone()])
                    }));
                    continue;
                }
                let mut classes: Vec<String> = expected
                    .iter()
                    .filter(|(_, kinds)| kinds.contains("class"))
                    .map(|(name, _)| name.clone())
                    .collect();
                let mut expanded = BTreeSet::new();
                while let Some(name) = classes.pop() {
                    if !expanded.insert(name.clone()) {
                        continue;
                    }
                    let Some(definition) = table.get(&name).filter(|entry| {
                        entry.declared_kind.as_deref() == Some("class")
                            && entry.defined_at.is_some()
                    }) else {
                        continue;
                    };
                    if let Some(kinds) = expected.get_mut(&name) {
                        kinds.remove("class");
                        if kinds.is_empty() {
                            expected.remove(&name);
                        }
                    }
                    for leaf in &definition.targets {
                        expected.entry(leaf.clone()).or_default().insert("class");
                        classes.push(leaf.clone());
                    }
                }
                for (name, (package, _, role)) in &roles {
                    if !closure.contains(*package) {
                        continue;
                    }
                    for activation in &role.activations {
                        for (_, source_doc) in documents
                            .iter()
                            .filter(|(_, doc)| doc.application_scope.is_none())
                        {
                            let scoped = lexicon.in_document(source_doc);
                            for spec in &source_doc.specs {
                                for matched in match_core(&activation.core, &spec.sentence.core) {
                                    let Some(subject) = matched.get(SUBJECT_VARIABLE) else {
                                        continue;
                                    };
                                    let subject = scoped.resolve(&scoped.canon(subject));
                                    if source_types.contains(&subject) {
                                        errors.push(("UNSUPPORTED_SEMANTICS", format!(
                                            "source role `{name}` activates over individuals of `{subject}`. This application cannot map the role's individual activations"
                                        )));
                                    }
                                    activations.insert((name.clone(), subject.clone()));
                                    expected.entry(subject).or_default().insert("entity");
                                }
                            }
                        }
                    }
                }
                let source_lex = source
                    .documents
                    .iter()
                    .find(|doc| doc.namespace == source.name)
                    .map_or_else(
                        || lexicon.in_namespace(&source.name),
                        |doc| lexicon.in_document(doc),
                    );
                let mut mapping = BTreeMap::new();
                for (source, target) in &application.mapping {
                    let (source, target) = match (
                        source_lex.resolve_explicit(source),
                        lex.resolve_explicit(target),
                    ) {
                        (Ok(source), Ok(target)) => (source, target),
                        (Err(error), _) | (_, Err(error)) => {
                            errors.push(("unresolved-import", error));
                            continue;
                        }
                    };
                    let Some(kinds) = expected.get(&source) else {
                        errors.push((
                            "UNRESOLVED_TERM",
                            format!(
                                "no mapped symbol `{source}` is required by this specification"
                            ),
                        ));
                        continue;
                    };
                    let Some(entry) = table.get(&target) else {
                        errors.push(("UNRESOLVED_TERM", format!("target `{target}` is absent from the local and imported vocabulary")));
                        continue;
                    };
                    let source_type = source_types.contains(&source);
                    let target_type = target_types.contains(&target);
                    if source_type != target_type {
                        let (expected, actual) = if source_type {
                            ("a declared type of individuals", "a representative")
                        } else {
                            ("a representative", "a declared type of individuals")
                        };
                        errors.push(("vocabulary-kind-conflict", format!("mapping `{source} = {target}` expects {expected} but the target names {actual}")));
                        continue;
                    }
                    if !kinds.iter().all(|kind| {
                        (source_type && matches!(*kind, "entity" | "object" | "class"))
                            || entry.declared_kind.as_deref().map_or_else(
                                || {
                                    entry
                                        .inferred_kinds
                                        .iter()
                                        .any(|actual| compatible_kind(actual, kind))
                                },
                                |actual| compatible_kind(actual, kind),
                            )
                            || (*kind == "entity"
                                && boundary.contains_key(&source)
                                && entry.declared_kind.is_none()
                                && entry.inferred_kinds.is_empty())
                    }) {
                        let actual: BTreeSet<_> = entry
                            .declared_kind
                            .iter()
                            .chain(&entry.inferred_kinds)
                            .map(String::as_str)
                            .collect();
                        let actual = if actual.is_empty() {
                            "a name without an inferred or declared kind".to_string()
                        } else {
                            actual.into_iter().collect::<Vec<_>>().join(" and ")
                        };
                        errors.push((
                            "vocabulary-kind-conflict",
                            format!(
                            "mapping `{source} = {target}` expects {} but `{target}` is {actual}",
                            kinds.iter().copied().collect::<Vec<_>>().join(" and ")
                        ),
                        ));
                        continue;
                    }
                    if let Some(owner_kind) = boundary.get(&source) {
                        let owners: BTreeSet<&str> = owner
                            .documents
                            .iter()
                            .flat_map(|target_doc| {
                                let target_lex = lexicon.in_document(target_doc);
                                let target = &target;
                                target_doc
                                    .controls
                                    .iter()
                                    .filter(move |decl| {
                                        target_lex.resolve(&target_lex.canon(&decl.name)) == *target
                                    })
                                    .map(|decl| decl.by.as_str())
                            })
                            .collect();
                        if owners != BTreeSet::from([*owner_kind]) {
                            errors.push(("vocabulary-kind-conflict", format!("mapping `{source} = {target}` requires a local `{owner_kind}` responsibility for `{target}`")));
                        }
                    }
                    if mapping.insert(source.clone(), target).is_some() {
                        errors.push((
                            "NAME_COLLISION",
                            format!("multiple mappings resolve to `{source}`"),
                        ));
                    }
                }
                for (symbol, kinds) in &expected {
                    if !mapping.contains_key(symbol) {
                        errors.push(("UNRESOLVED_TERM", format!("missing mapping for `{symbol}`")));
                    }
                    if kinds.iter().any(|kind| is_actor(kind)) && !boundary.contains_key(symbol) {
                        errors.push(("vocabulary-kind-conflict", format!("the source must declare system or environment responsibility for `{symbol}`")));
                    }
                    if !kinds.contains("predicate") {
                        continue;
                    }
                    let Some(target) = mapping.get(symbol) else {
                        continue;
                    };
                    let (Some(source_signature), Some(target_signature)) = (
                        table.get(symbol).and_then(|entry| entry.signature.as_ref()),
                        table.get(target).and_then(|entry| entry.signature.as_ref()),
                    ) else {
                        continue;
                    };
                    let mapped: Vec<&str> = source_signature
                        .iter()
                        .map(|slot| mapping.get(slot).unwrap_or(slot).as_str())
                        .collect();
                    if mapped.len() != target_signature.len()
                        || mapped
                            .iter()
                            .zip(target_signature)
                            .any(|(expected, actual)| !compatible_kind(actual, expected))
                    {
                        errors.push(("vocabulary-kind-conflict", format!(
                            "mapping `{symbol} = {target}` expects signature ({}) but the target declares ({})",
                            mapped.join(", "), target_signature.join(", ")
                        )));
                    }
                }
                for (role, _) in bound.union(&activations) {
                    let Some((_, namespace, recipe)) = roles.get(role) else {
                        continue;
                    };
                    let scoped = lexicon.in_namespace(namespace);
                    for pattern in recipe
                        .forms
                        .iter()
                        .map(|form| &form.pattern)
                        .chain(recipe.required.iter().map(|rule| &rule.pattern))
                    {
                        if occurrences(pattern, &scoped).iter().any(|(name, kind)| {
                            let predicate = (*kind == "action")
                                .then(|| scoped.predicate_identity(name))
                                .flatten();
                            let symbol = predicate.as_ref().unwrap_or(name);
                            mapping.get(symbol).is_some_and(|target| target != symbol)
                        }) {
                            errors.push(("UNSUPPORTED_SEMANTICS", format!("form role `{role}` contains a literal name that changes under the application. Use a role parameter for the mapped name")));
                        }
                    }
                }
                if expected.is_empty() || !errors.is_empty() {
                    if expected.is_empty() {
                        errors.push((
                            "UNSUPPORTED_SEMANTICS",
                            "the reference has no applicable target contracts".into(),
                        ));
                    }
                    diagnostics.extend(errors.into_iter().map(|(code, message)| {
                        Diagnostic::error(code, message, vec![application.at.clone()])
                    }));
                    continue;
                }
                let mut statements = Vec::new();
                let mut instance_documents = Vec::new();
                let mut application_roles = BTreeMap::<String, BTreeSet<String>>::new();
                for (role, subject) in activations {
                    if let Some(target) = mapping.get(&subject) {
                        application_roles
                            .entry(role)
                            .or_default()
                            .insert(target.clone());
                    }
                }
                let scope = SpecRef {
                    id: format!("apply-{}", application.name),
                    ..application.at.clone()
                };
                for (index, (package, source_doc)) in documents.into_iter().enumerate() {
                    let bindings = role_bindings.remove(&index).unwrap_or_default();
                    let mut composed = mapping.clone();
                    composed.extend(source_doc.application_mapping.iter().map(
                        |(source, target)| {
                            (
                                source.clone(),
                                mapping.get(target).unwrap_or(target).clone(),
                            )
                        },
                    ));
                    let (scope, ancestors, roles) =
                        if let Some(inner) = &source_doc.application_scope {
                            let roles = source_doc
                                .application_roles
                                .iter()
                                .map(|(role, targets)| {
                                    (
                                        role.clone(),
                                        targets
                                            .iter()
                                            .filter_map(|target| mapping.get(target).cloned())
                                            .collect(),
                                    )
                                })
                                .collect();
                            let ancestors = std::iter::once(scope.clone())
                                .chain(source_doc.application_ancestors.iter().cloned())
                                .collect();
                            (inner.clone(), ancestors, roles)
                        } else {
                            (scope.clone(), Vec::new(), application_roles.clone())
                        };
                    let mut applied = Document {
                        file: source_doc.file.clone(),
                        namespace: source_doc.namespace.clone(),
                        imports: source_doc.imports.clone(),
                        bindings,
                        application_roles: roles,
                        application_mapping: composed,
                        application_scope: Some(scope),
                        application_ancestors: ancestors,
                        ..Default::default()
                    };
                    for spec in &source_doc.specs {
                        if matches!(spec.sentence.core, Core::Definition { .. }) {
                            continue;
                        }
                        let mut spec = spec.clone();
                        let prefix = |id: &str| format!("apply-{}/{id}", application.name);
                        spec.id = Some(prefix(&spec.display_id()));
                        spec.details = spec.details.iter().map(|id| prefix(id)).collect();
                        spec.parts = spec.parts.iter().map(|id| prefix(id)).collect();
                        statements.push(format!("{package}::{}", spec.display_id()));
                        applied.specs.push(spec);
                    }
                    instance_documents.push((package.to_string(), applied));
                }
                let nested = closure
                    .iter()
                    .filter_map(|name| declared_applications.get(name))
                    .flatten()
                    .cloned()
                    .collect();
                declared_applications
                    .entry(owner.name.clone())
                    .or_default()
                    .push(AppliedSpecification {
                        name: application.name.clone(),
                        package: source.name.clone(),
                        file: application.at.file.clone(),
                        line: application.at.line,
                        mapping,
                        statements,
                        nested,
                        dependencies: closure
                            .iter()
                            .filter(|package| *package != &source.name)
                            .cloned()
                            .collect(),
                    });
                planned
                    .entry(owner.name.clone())
                    .or_default()
                    .extend(instance_documents);
            }
        }
        processed.insert(owner.name.clone());
    }
    // Existing use edges still take the whole dependency and its use closure.
    let active = use_closure(set, &root.name);
    let mut additions = BTreeMap::<String, Vec<Document>>::new();
    for owner in &active {
        recorded.extend(declared_applications.remove(owner).unwrap_or_default());
        for (origin, doc) in planned.remove(owner).unwrap_or_default() {
            additions.entry(origin).or_default().push(doc);
        }
    }
    let available_roles: BTreeMap<String, (String, String)> = set
        .packages
        .iter()
        .flat_map(|pkg| {
            pkg.documents.iter().flat_map(move |doc| {
                doc.roles.iter().map(move |role| {
                    let namespace = trion_language::reading::role_prefix(&pkg.name, &doc.namespace);
                    (
                        format!("{namespace}.{}", role.name),
                        (pkg.name.clone(), namespace.to_string()),
                    )
                })
            })
        })
        .collect();
    let classification_roles: BTreeMap<String, (String, String)> = set
        .packages
        .iter()
        .flat_map(|package| {
            package.documents.iter().flat_map(move |doc| {
                let namespace = role_prefix(&package.name, &doc.namespace);
                doc.classifications.iter().map(move |class| {
                    (
                        format!("{namespace}.{}", class.attr),
                        (package.name.clone(), namespace.to_string()),
                    )
                })
            })
        })
        .collect();
    for pkg in &mut set.packages {
        for doc in pkg.documents.iter_mut() {
            for binding in &mut doc.bindings {
                let key = doc
                    .imports
                    .iter()
                    .find_map(|import| {
                        let (namespace, role) = binding.role.rsplit_once('.')?;
                        let tail = namespace.strip_prefix(&import.name)?;
                        (tail.is_empty() || tail.starts_with('.'))
                            .then(|| format!("{}{tail}.{role}", import.namespace))
                    })
                    .unwrap_or_else(|| binding.role.clone());
                if available_roles.contains_key(&key) && classification_roles.contains_key(&key) {
                    diagnostics.push(Diagnostic::error(
                        "NAME_COLLISION",
                        format!("both a role and a sentence classification are named `{key}`"),
                        vec![SpecRef::point(&binding.file, binding.line, &binding.text)],
                    ));
                    continue;
                }
                let visible = available_roles
                    .get(&key)
                    .or_else(|| classification_roles.get(&key))
                    .is_some_and(|(package, namespace)| {
                        pkg.name == *package
                            || active.contains(package)
                            || doc.imports.iter().any(|import| {
                                namespace == &import.namespace
                                    || namespace.starts_with(&format!("{}.", import.namespace))
                            })
                    });
                if visible {
                    binding.role = key;
                } else {
                    diagnostics.push(Diagnostic::error(
                        "unresolved-import",
                        format!("form role `{}` is missing from the available role declarations; use or refer to its package", binding.role),
                        vec![SpecRef::point(&binding.file, binding.line, &binding.text)],
                    ));
                }
            }
        }
    }
    for pkg in &mut set.packages {
        if !active.contains(&pkg.name) {
            for doc in &mut pkg.documents {
                doc.symbol_sources.append(&mut doc.specs);
                doc.primitives.extend(doc.controls.drain(..).map(|decl| {
                    trion_language::document::PrimitiveDecl {
                        name: decl.name,
                        file: decl.file,
                        line: decl.line,
                    }
                }));
                doc.primitives.append(&mut doc.individuals);
                doc.primitives.append(&mut doc.measures);
                doc.bindings.clear();
                doc.roles_require_binding = true;
                doc.extensions.clear();
                doc.checks.clear();
                doc.propositional_checks.clear();
                doc.scenarios.clear();
                doc.examples.clear();
                doc.compatibility.clear();
            }
        }
        pkg.documents
            .extend(additions.remove(&pkg.name).unwrap_or_default());
    }
    (references, recorded)
}
