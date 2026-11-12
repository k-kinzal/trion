//! Vocabulary: the usable terms are the declared ones plus the ones inferred
//! from the specification set.

use crate::document::SpecSet;
use crate::diagnostic::{Diagnostic, SpecRef};
use crate::reading::model::{base_verb, np_key, participle_base, role_nps};
use crate::reading::lexicon::Lexicon;
use crate::syntax::ast::*;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct VocabEntry {
    pub term: String,
    pub declared_kind: Option<String>,
    pub inferred_kinds: BTreeSet<String>,
    pub occurrences: usize,
    pub first_use: Option<SpecRef>,
    /// The namespace that owns the term. The root namespace is empty.
    pub namespace: String,
    /// The `term` declaration, if any.
    pub declared_at: Option<SpecRef>,
    /// The `means` sentence that defines the term, if any.
    pub defined_at: Option<SpecRef>,
    /// Every statement that uses the term, once per statement.
    pub uses: Vec<SpecRef>,
    /// How the resolver derived the term, when no declaration supplies it.
    pub derivation: Option<Derivation>,
    /// The argument signature of a declared uninterpreted predicate.
    pub signature: Option<Vec<String>>,
    /// The stable identity of a declared uninterpreted predicate.
    pub identity: Option<String>,
}

/// A derived interpretation with what it was derived from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Derivation {
    /// The derived kinds of the term.
    pub interpretation: Vec<String>,
    /// One rule per derived kind, in the order of `interpretation`.
    pub rules: Vec<String>,
    /// The statement that each rule was applied to, in the same order.
    pub premises: Vec<SpecRef>,
    /// The identities of the definitions and declarations that the term refers to.
    pub referenced: Vec<String>,
}

const PREDICATE: &str = "predicate";

fn derivation_rule(kind: &str) -> &'static str {
    match kind {
        "entity" => "the subject of an action is an entity",
        "object" => "the object or role of an action is an object",
        "attribute" => "the subject of a description is an attribute",
        "value" => "the predicate of a description is a value",
        _ => "the verb of a clause is an action",
    }
}

/// The terms that the right side of a definition mentions.
fn definiens_terms(definiens: &Definiens, lex: &Lexicon) -> Vec<String> {
    let mut out = Vec::new();
    match definiens {
        Definiens::Np { np, roles } => {
            out.extend(group_keys(np, lex).into_iter().map(|k| (k, "object")));
            role_terms(roles, lex, &mut out);
        }
        Definiens::Clause(clause) => clause_terms(clause, lex, &mut out),
    }
    out.into_iter().map(|(k, _)| k).collect()
}

fn definitions(core: &Core, lex: &Lexicon, out: &mut Vec<(String, Vec<String>)>) {
    match core {
        Core::Conjoined { items } => items.iter().for_each(|item| definitions(item, lex, out)),
        Core::Definition { term, definiens } => out.push((np_key(term, lex), definiens_terms(definiens, lex))),
        _ => {}
    }
}

const KINDS: [&str; 5] = ["entity", "object", "attribute", "value", "action"];
/// The kind of a term that a `means` sentence defines. It fits any use.
const DEFINED: &str = "defined";

fn compatible(a: &str, b: &str) -> bool {
    let group = |k: &str| if k == "entity" || k == "object" { "thing".to_string() } else { k.to_string() };
    a == DEFINED || (a == PREDICATE && b == "action") || group(a) == group(b)
}

fn group_keys(group: &NpGroup, lex: &Lexicon) -> Vec<String> {
    match group {
        NpGroup::Single(np) => vec![np_key(np, lex)],
        NpGroup::Coordinated { items, .. } => items.iter().map(|np| np_key(np, lex)).collect(),
    }
}

fn role_terms(roles: &[RolePp], lex: &Lexicon, out: &mut Vec<(String, &'static str)>) {
    out.extend(roles.iter().flat_map(role_nps).map(|np| (np_key(np, lex), "object")));
}

/// A perfect form such as `has completed` is the same action as `completes`,
/// when the specification set uses that verb.
fn verb_lemma(verb: &str, lex: &Lexicon) -> String {
    let base = base_verb(verb);
    let lemma = participle_base(&base, lex);
    if lex.verbs.contains(&lemma) { lemma } else { base }
}

fn clause_terms(clause: &Clause, lex: &Lexicon, out: &mut Vec<(String, &'static str)>) {
    match &clause.body {
        ClauseBody::Copular { predicate, .. } => {
            out.extend(group_keys(&clause.subject, lex).into_iter().map(|k| (k, "attribute")));
            if !matches!(predicate, Predicate::Comparison(_)) {
                out.push((crate::reading::key::text(&crate::reading::key::value_parts(predicate, None, &[], lex)), "value"));
            }
        }
        ClauseBody::Verbal { verb, object, roles, .. } => {
            out.extend(group_keys(&clause.subject, lex).into_iter().map(|k| (k, "entity")));
            out.push((verb_lemma(verb, lex), "action"));
            out.extend(object.iter().flat_map(|g| group_keys(g, lex)).map(|k| (k, "object")));
            role_terms(roles, lex, out);
        }
    }
}

/// The terms of a sentence with the kind each one plays.
pub fn occurrences(s: &Sentence, lex: &Lexicon) -> Vec<(String, &'static str)> {
    let mut out = Vec::new();
    let groups = s.frames.scopes.iter().chain(&s.frames.states).map(|f| &f.clause).chain(s.frames.trigger.iter().map(|t| &t.clause));
    for clause in groups.flat_map(|g| &g.items).chain(s.exception.iter()) {
        clause_terms(clause, lex, &mut out);
    }
    core_terms(&s.core, lex, &mut out);
    out
}

fn core_terms(core: &Core, lex: &Lexicon, out: &mut Vec<(String, &'static str)>) {
    match core {
        Core::Conjoined { items } => items.iter().for_each(|item| core_terms(item, lex, out)),
        Core::Existence { subject } => out.extend(group_keys(subject, lex).into_iter().map(|k| (k, "entity"))),
        Core::Definition { term, .. } => out.push((np_key(term, lex), DEFINED)),
        Core::Description { subject, predicate, .. } => {
            // `No error is a warning.` names two concepts: its subject is no attribute.
            let excluded = matches!(subject, NpGroup::Single(np) if matches!(np.det, Some(Det::No)) && np.of.is_none() && np.relative.is_none())
                && matches!(predicate, Predicate::Words { words } if words.first().is_some_and(|w| !w.eq_ignore_ascii_case("the")) && !words.iter().any(|w| w.eq_ignore_ascii_case("of")));
            out.extend(group_keys(subject, lex).into_iter().map(|k| (k, if excluded { "value" } else { "attribute" })));
            match predicate {
                Predicate::Comparison(_) => {}
                Predicate::Enumeration { values, .. } => out.extend(values.iter().map(|v| (crate::reading::model::value_name(v, lex), "value"))),
                other => out.push((crate::reading::key::text(&crate::reading::key::value_parts(other, None, &[], lex)), "value")),
            }
        }
        Core::Deontic { subject, vp, .. } | Core::Relation { subject, vp } => {
            out.extend(group_keys(subject, lex).into_iter().map(|k| (k, "entity")));
            for item in vp.items() {
                out.push((item.verb.clone(), "action"));
                out.extend(item.object.iter().flat_map(|g| group_keys(g, lex)).map(|k| (k, "object")));
                role_terms(&item.roles, lex, out);
            }
        }
    }
}

fn levenshtein(a: &[char], b: &[char]) -> usize {
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    for (i, ca) in a.iter().enumerate() {
        let mut cur = vec![i + 1];
        for (j, cb) in b.iter().enumerate() {
            let cost = usize::from(ca != cb);
            cur.push((prev[j + 1] + 1).min(cur[j] + 1).min(prev[j] + cost));
        }
        prev = cur;
    }
    prev[b.len()]
}

pub fn build_table(set: &SpecSet, lex: &Lexicon) -> (BTreeMap<String, VocabEntry>, Vec<Diagnostic>) {
    let mut table: BTreeMap<String, VocabEntry> = BTreeMap::new();
    let mut diags = Vec::new();
    let new_entry = |term: &str| VocabEntry { term: term.to_string(), declared_kind: None, inferred_kinds: BTreeSet::new(), occurrences: 0, first_use: None, namespace: term.rsplit_once("::").map_or(String::new(), |(ns, _)| ns.to_string()), declared_at: None, defined_at: None, uses: Vec::new(), derivation: None, signature: None, identity: None };

    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let lex = lex.in_document(doc);
        for decl in &doc.vocabulary {
            let at = SpecRef { id: format!("{}:{}", decl.file, decl.line), file: decl.file.clone(), line: decl.line, text: format!("term {}: {}", decl.term, decl.kind) };
            if !KINDS.contains(&decl.kind.as_str()) {
                diags.push(Diagnostic::error("vocabulary-unknown-kind", format!("the term kind `{}` does not exist ({})", decl.kind, KINDS.join(", ")), vec![at]));
                continue;
            }
            let key = lex.resolve(&lex.canon(&decl.term));
            let entry = table.entry(key.clone()).or_insert_with(|| new_entry(&key));
            entry.declared_at.get_or_insert_with(|| at.clone());
            match &entry.declared_kind {
                Some(k) if k != &decl.kind => diags.push(Diagnostic::error("vocabulary-redeclared", format!("the term `{}` is already declared as {k}", decl.term), vec![at])),
                _ => entry.declared_kind = Some(decl.kind.clone()),
            }
        }
    }

    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let lex = lex.in_document(doc);
        for decl in &doc.predicates {
            let at = SpecRef { id: format!("{}:{}", decl.file, decl.line), file: decl.file.clone(), line: decl.line, text: format!("predicate {}({})", decl.name, decl.signature.join(", ")) };
            let key = lex.resolve(&lex.canon(&decl.name));
            let entry = table.entry(key.clone()).or_insert_with(|| new_entry(&key));
            match (&entry.declared_kind, &entry.signature) {
                (Some(k), _) if k != PREDICATE => diags.push(Diagnostic::error("vocabulary-redeclared", format!("the term `{}` is already declared as {k}", decl.name), vec![at])),
                (_, Some(signature)) if signature != &decl.signature => diags.push(Diagnostic::error("vocabulary-redeclared", format!("the predicate `{}` is already declared with the signature ({})", decl.name, signature.join(", ")), vec![at])),
                _ => {
                    entry.declared_kind = Some(PREDICATE.to_string());
                    entry.identity = Some(format!("{}/{}", if doc.namespace.is_empty() { decl.name.clone() } else { format!("{}::{}", doc.namespace, decl.name) }, decl.signature.len()));
                    entry.signature = Some(decl.signature.clone());
                    entry.declared_at.get_or_insert(at);
                }
            }
        }
    }

    let mut defined: Vec<(String, Vec<String>, SpecRef)> = Vec::new();
    let mut premises: BTreeMap<(String, String), SpecRef> = BTreeMap::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let lex = lex.in_document(doc);
        for spec in &doc.specs {
            let at = SpecRef { id: spec.display_id(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
            let mut found = Vec::new();
            definitions(&spec.sentence.core, &lex, &mut found);
            defined.extend(found.into_iter().map(|(term, mentions)| (term, mentions, at.clone())));
            for (term, kind) in occurrences(&spec.sentence, &lex) {
                if kind != DEFINED {
                    premises.entry((term.clone(), kind.to_string())).or_insert_with(|| at.clone());
                }
                let entry = table.entry(term.clone()).or_insert_with(|| new_entry(&term));
                if entry.uses.last() != Some(&at) {
                    entry.uses.push(at.clone());
                }
            }
        }
    }

    // A definition that reaches itself through other definitions has no meaning.
    let edges: BTreeMap<&String, &Vec<String>> = defined.iter().map(|(term, mentions, _)| (term, mentions)).collect();
    let mut reported: BTreeSet<Vec<String>> = BTreeSet::new();
    for (start, _, _) in &defined {
        let mut path: Vec<&String> = vec![start];
        let mut stack: Vec<(usize, usize)> = vec![(0, 0)];
        while let Some((depth, next)) = stack.pop() {
            path.truncate(depth + 1);
            let Some(mentions) = edges.get(path[depth]) else { continue };
            let Some(mention) = mentions.get(next) else { continue };
            stack.push((depth, next + 1));
            if mention == start {
                let mut cycle: Vec<String> = path.iter().map(|t| (*t).clone()).collect();
                cycle.sort();
                if reported.insert(cycle.clone()) {
                    let refs = defined.iter().filter(|(term, _, _)| cycle.contains(term)).map(|(_, _, at)| at.clone()).collect();
                    diags.push(Diagnostic::error("CYCLIC_DEFINITION", format!("the definition of `{}` is cyclic: {} -> {start}", start, path.iter().map(|t| t.as_str()).collect::<Vec<_>>().join(" -> ")), refs));
                }
            } else if !path.contains(&mention) && edges.contains_key(mention) && path.len() < 64 {
                path.push(mention);
                stack.push((depth + 1, 0));
            }
        }
    }

    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let lex = lex.in_document(doc);
        for spec in &doc.specs {
            let at = SpecRef { id: spec.display_id(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
            for (term, kind) in occurrences(&spec.sentence, &lex) {
                let entry = table.entry(term.clone()).or_insert_with(|| new_entry(&term));
                entry.occurrences += 1;
                if kind == DEFINED {
                    entry.defined_at.get_or_insert_with(|| at.clone());
                    entry.declared_kind.get_or_insert_with(|| DEFINED.to_string());
                } else {
                    entry.inferred_kinds.insert(kind.to_string());
                }
                entry.first_use.get_or_insert_with(|| at.clone());
            }
        }
    }

    // A term without a declaration or a definition is derived from its uses.
    let local_words = |t: &str| t.rsplit("::").next().unwrap_or(t).to_lowercase().split_whitespace().map(str::to_string).collect::<Vec<String>>();
    let declared: Vec<(String, String)> = table
        .values()
        .filter_map(|e| e.defined_at.as_ref().or(e.declared_at.as_ref()).map(|at| (e.term.clone(), format!("{} @ {}:{}", e.term, at.file, at.line))))
        .collect();
    for entry in table.values_mut() {
        if entry.declared_at.is_some() || entry.defined_at.is_some() || entry.inferred_kinds.is_empty() {
            continue;
        }
        let words = local_words(&entry.term);
        let referenced = declared
            .iter()
            .filter(|(term, _)| {
                let part = local_words(term);
                term != &entry.term && !part.is_empty() && part.len() < words.len() && words.windows(part.len()).any(|w| w == part.as_slice())
            })
            .map(|(_, identity)| identity.clone())
            .collect();
        let interpretation: Vec<String> = entry.inferred_kinds.iter().cloned().collect();
        entry.derivation = Some(Derivation {
            rules: interpretation.iter().map(|k| derivation_rule(k).to_string()).collect(),
            premises: interpretation.iter().filter_map(|k| premises.get(&(entry.term.clone(), k.clone())).cloned()).collect(),
            interpretation,
            referenced,
        });
    }

    for entry in table.values() {
        let at: Vec<SpecRef> = entry.first_use.iter().cloned().collect();
        match &entry.declared_kind {
            Some(declared) => {
                for used in &entry.inferred_kinds {
                    if !compatible(declared, used) {
                        diags.push(Diagnostic::error("vocabulary-kind-conflict", format!("the term `{}` is declared as {declared} but used as {used}", entry.term), at.clone()));
                    }
                }
            }
            None => {
                if entry.inferred_kinds.contains("attribute") && entry.inferred_kinds.contains("value") {
                    diags.push(Diagnostic::warning("vocabulary-kind-ambiguous", format!("the term `{}` is used as both an attribute and a value; declare its kind", entry.term), at.clone()));
                }
                let only_action = entry.inferred_kinds.len() == 1 && entry.inferred_kinds.contains("action");
                if set.vocabulary_mode == crate::document::VocabularyMode::Declared && !only_action {
                    diags.push(Diagnostic::error("UNRESOLVED_TERM", format!("the term `{}` has no interpretation: it is not declared", entry.term), entry.uses.clone()));
                }
            }
        }
    }

    let terms: Vec<&String> = table.keys().collect();
    let local = |t: &str| t.rsplit("::").next().unwrap_or(t).to_string();
    // An inflection is the same word, which number and verb agreement settle.
    let inflected = |a: &str, b: &str| [("s", ""), ("es", "")].iter().any(|(s, _)| a.strip_suffix(s) == Some(b) || b.strip_suffix(s) == Some(a));
    // A typo occurs once; two words that each recur are both meant.
    let recurs = |t: &str| table.get(t).is_some_and(|e| e.occurrences > 1);
    // Each term is prepared once: the check compares every pair.
    struct Prepared<'a> {
        name: &'a String,
        local: String,
        lower: String,
        chars: Vec<char>,
        owner: Option<String>,
        kinds: BTreeSet<String>,
        recurs: bool,
    }
    let prepared: Vec<Prepared> = terms
        .iter()
        // The marks of two bound objects differ by a line number, on purpose.
        .filter(|name| !local(name).starts_with(crate::document::BINDING_MARK))
        .map(|name| {
            let local = local(name);
            Prepared {
                name,
                lower: local.to_lowercase(),
                chars: local.chars().collect(),
                local,
                owner: name.rsplit_once("::").map(|(n, _)| n.to_string()),
                kinds: table.get(*name).map(|e| e.inferred_kinds.clone()).unwrap_or_default(),
                recurs: recurs(name),
            }
        })
        .collect();
    for (i, a) in prepared.iter().enumerate() {
        for b in &prepared[i + 1..] {
            // One edit changes the length by at most one.
            if a.chars.len().abs_diff(b.chars.len()) > 1 {
                continue;
            }
            // A typo is a slip within one vocabulary, in one role.
            let same_role = a.kinds.is_empty() || b.kinds.is_empty() || !a.kinds.is_disjoint(&b.kinds);
            let same_name = a.name.eq_ignore_ascii_case(b.name);
            if a.owner != b.owner || !same_role || inflected(&a.lower, &b.lower) || (a.recurs && b.recurs && !same_name) {
                continue;
            }
            // The same name in two namespaces is two terms on purpose.
            if a.local == b.local {
                continue;
            }
            let long_enough = a.chars.len() >= 5 && b.chars.len() >= 5;
            // Numbered names such as `node1` and `node2` are deliberate.
            let letters = |w: &[char]| w.iter().filter(|c| !c.is_ascii_digit()).copied().collect::<Vec<char>>();
            if same_name || (long_enough && letters(&a.chars) != letters(&b.chars) && levenshtein(&a.chars, &b.chars) <= 1) {
                let refs = [a.name, b.name].iter().filter_map(|t| table.get(*t).and_then(|e| e.first_use.clone())).collect();
                diags.push(Diagnostic::warning("vocabulary-similar", format!("the terms `{}` and `{}` are spelled almost the same; one may be a typo, or declare an alias", a.name, b.name), refs));
            }
        }
    }
    (table, diags)
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct GlossaryEntry {
    pub term: String,
    /// `explicit`, `primitive`, `imported`, `derived` or `unresolved`.
    pub status: String,
    pub namespace: String,
    pub kinds: Vec<String>,
    pub occurrences: usize,
    pub first_use: Option<String>,
    /// The source declaration of the term (`term` or `predicate`), as `file:line`.
    pub declared_at: Option<String>,
    /// The source definition of the term (`means`), as `file:line`.
    pub defined_at: Option<String>,
    /// The text of the definition.
    pub definition: Option<String>,
    /// How the term was derived, when it has no declaration and no definition.
    pub derivation: Option<GlossaryDerivation>,
    /// The namespace that supplies an imported term.
    pub referenced_domain: Option<String>,
    /// Every statement that uses the term, as `file:line`.
    pub occurrences_at: Vec<String>,
    /// The argument signature and identity of a declared uninterpreted predicate.
    pub signature: Option<Vec<String>>,
    pub identity: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct GlossaryDerivation {
    pub interpretation: Vec<String>,
    pub rules: Vec<String>,
    /// The statements the rules were applied to, as `file:line`.
    pub premises: Vec<String>,
    /// The identities of the definitions that the term refers to.
    pub referenced: Vec<String>,
}

/// One entry per term, with how the term came to exist. The glossary is a
/// view: it points at declarations and adds no statement of its own.
pub fn glossary(table: &BTreeMap<String, VocabEntry>) -> Vec<GlossaryEntry> {
    let place = |r: &SpecRef| format!("{}:{}", r.file, r.line);
    table
        .values()
        // A bound object is no term of the vocabulary: its type is.
        .filter(|e| !e.term.rsplit("::").next().unwrap_or(&e.term).starts_with(crate::document::BINDING_MARK))
        .map(|e| {
            let status = if e.signature.is_some() {
                "primitive"
            } else if e.defined_at.is_some() || e.declared_at.is_some() {
                "explicit"
            } else if e.term.contains("::") {
                "imported"
            } else if e.inferred_kinds.is_empty() {
                "unresolved"
            } else {
                "derived"
            };
            GlossaryEntry {
                term: e.term.clone(),
                status: status.to_string(),
                namespace: e.namespace.clone(),
                kinds: e.inferred_kinds.iter().cloned().collect(),
                occurrences: e.occurrences,
                first_use: e.first_use.as_ref().map(place),
                declared_at: e.declared_at.as_ref().map(place),
                defined_at: e.defined_at.as_ref().map(place),
                definition: e.defined_at.as_ref().map(|r| r.text.clone()),
                derivation: e.derivation.as_ref().map(|d| GlossaryDerivation { interpretation: d.interpretation.clone(), rules: d.rules.clone(), premises: d.premises.iter().map(place).collect(), referenced: d.referenced.clone() }),
                referenced_domain: e.term.rsplit_once("::").map(|(domain, _)| domain.to_string()),
                occurrences_at: e.uses.iter().map(place).collect(),
                signature: e.signature.clone(),
                identity: e.identity.clone(),
            }
        })
        .collect()
}
