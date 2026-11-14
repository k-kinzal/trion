//! What a specification says without saying anything a check can use.
//!
//! Two reports keep such statements in view. An opaque reading is an atom
//! whose name still carries a comparison, a temporal word, a quantifier or a
//! clause: that part was not read. An ungrounded statement is a statement
//! with normative force that excludes no interpretation of the other
//! statements: nothing shares its atoms, and one of its terms has neither a
//! definition nor a primitive declaration nor a description. A statement
//! without normative force describes its terms: it says which situations can
//! occur, and so it gives each term that it relates a place in them.

use crate::document::SpecSet;
use crate::diagnostic::{Diagnostic, SpecRef};
use crate::document::Spec;
use crate::reading::model::{ConstraintKind, Model};
use crate::reading::lexicon::Lexicon;
use trion_solver::{Atom, Formula};
use crate::syntax::ast::Core;
use crate::reading::vocabulary::{occurrences, VocabEntry};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

/// The statements that say less than they seem to.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct Silence {
    /// One warning for each atom that keeps an unread part in its name.
    pub opaque: Vec<Diagnostic>,
    /// One warning for each statement that constrains nothing.
    pub ungrounded: Vec<Diagnostic>,
    /// One error for each statement whose property one model of a
    /// conjunction cannot state: a relation between runs, a proportion, an
    /// optimum, or a quality without a measure. The statement is accepted
    /// and what it requires has no meaning, so no result covers it.
    pub inexpressible: Vec<Diagnostic>,
    /// The statements that are grounded only because an abstract statement
    /// names them in `detailed by`: no other statement shares an atom with
    /// them, no definition, inclusion or exclusion relates them, and one of
    /// their terms is neither defined nor primitive. They pass, and they
    /// add little to the weight of a consistency result.
    pub refinement_only: Vec<SpecRef>,
}

const QUALITIES: &[&str] = &["secure", "securely", "safe", "safely", "quick", "quickly", "fast", "slow", "slowly", "easy", "easily", "efficient", "efficiently", "reliable", "reliably", "robust", "robustly", "scalable", "performant", "responsive", "promptly", "graceful", "gracefully", "intuitive", "flexible", "maintainable", "reasonable", "reasonably", "appropriate", "appropriately", "adequate", "adequately", "timely", "user-friendly", "smoothly", "seamlessly"];
const RUNS: &[&str] = &["deterministic", "deterministically", "idempotent", "idempotently", "repeatable", "repeatably", "reproducible", "every time", "each time"];
const PROPORTIONS: &[&str] = &["percent of", "probability", "probable", "probably", "likely", "availability", "on average", "expected value", "majority of", "usually", "typically", "rarely"];
const OPTIMA: &[&str] = &["as possible", "minimize", "minimizes", "maximize", "maximizes", "optimal", "optimally", "fastest", "slowest", "preferably", "ideally", "best effort"];

/// `<verb> same X for same Y` and nothing else that repeats.
fn functional_shape(padded: &str) -> bool {
    padded.matches(" same ").count() == 2 && padded.matches(" for same ").count() == 1
}

/// The kind of property that a name states and that a conjunction of
/// contracts over one model cannot express, with advice for the author.
fn beyond(name: &str, quality_grounded: &dyn Fn(&str) -> bool) -> Option<(&'static str, String, &'static str)> {
    let padded = format!(" {} ", name.to_lowercase().replace([',', ';'], " "));
    let find = |words: &[&'static str]| words.iter().copied().find(|w| padded.contains(&format!(" {w} ")));
    // `same response for same request`: the second `same` names what is repeated.
    let repeated = padded.split(" for same ").next().is_some_and(|before| before.len() < padded.len() && before.contains(" same "));
    // `return the same response for the same request` alone is read: the
    // response is a function of the request, counted over individuals.
    if repeated && functional_shape(&padded) {
        return None;
    }
    if repeated {
        return Some(("a relation between runs", "same … same".to_string(), "it compares two runs of the system, and a check reads one run: state what determines the result, as in a definition of the response by the request, or verify it with a test"));
    }
    if let Some(word) = find(RUNS) {
        return Some(("a relation between runs", word.to_string(), "it compares two runs of the system, and a check reads one run: state what determines the result, or verify it with a test"));
    }
    if let Some(word) = find(PROPORTIONS) {
        return Some(("a proportion or a probability", word.to_string(), "it speaks about a share of the cases, and a check reads each case: state the bound for every case, or declare a measure and bound it"));
    }
    if let Some(word) = find(OPTIMA) {
        return Some(("an optimum or a preference", word.to_string(), "it compares the system with every alternative: state a bound, or write a `should` statement with a `weight`"));
    }
    let quality = QUALITIES.iter().copied().find(|w| padded.contains(&format!(" {w} ")) && !quality_grounded(w))?;
    Some(("a quality without a measure", quality.to_string(), "nothing says when it holds: define the term, or state a measure with a bound, as in `within 200 ms`"))
}

/// The part of an atom that is a free name.
fn name_of(atom: &Atom) -> Option<&str> {
    match atom {
        Atom::Act { key } | Atom::Forbid { key } | Atom::Discouraged { key } | Atom::Event { key } | Atom::Config { key } => Some(key.split_once('|').map_or(key.as_str(), |(_, action)| action)),
        Atom::Dom { value, .. } | Atom::Val { value, .. } => Some(value),
        _ => None,
    }
}

/// What two contracts must share to constrain each other.
fn signatures(formula: &Formula, out: &mut BTreeSet<String>) {
    formula.atoms(true, &mut |atom, _| match atom {
        Atom::Act { key } | Atom::Forbid { key } | Atom::Discouraged { key } => {
            out.insert(format!("act {key}"));
        }
        Atom::Event { key } => {
            out.insert(format!("event {key}"));
        }
        Atom::Config { key } => {
            out.insert(format!("config {key}"));
        }
        Atom::Dom { attr, value } | Atom::Val { attr, value } => {
            out.insert(format!("value {attr} = {value}"));
        }
        Atom::Num { attr, unit, .. } => {
            out.insert(format!("number {attr} {unit}"));
        }
        // A relation between quantities shares each of them with its bounds.
        Atom::Lin { terms, unit, .. } => {
            out.extend(terms.iter().map(|(attr, _)| format!("number {attr} {unit}")));
        }
        Atom::Before { first, second } => {
            out.insert(format!("act {first}"));
            out.insert(format!("act {second}"));
        }
        Atom::Role { subject, role } => {
            out.insert(format!("role {subject} {role}"));
        }
        // Statements about the individuals of one relation share that relation.
        Atom::Rel { name, .. } => {
            out.insert(format!("relation {name}"));
        }
    });
}

/// Finds the opaque readings and the ungrounded statements of a model.
pub fn silence(set: &SpecSet, model: &Model, vocabulary: &BTreeMap<String, VocabEntry>, lex: &Lexicon) -> Silence {
    let statements = model.constraints.iter().filter(|c| matches!(c.kind, ConstraintKind::Spec | ConstraintKind::Permission));

    // Unread parts: what the keys of a statement could not hold, and each
    // closed-class word in an open place of a node that reached no key.
    let mut opaque: Vec<Diagnostic> = Vec::new();
    let mut told: BTreeSet<String> = BTreeSet::new();
    // An article inside a name is often the trace of a word before it that
    // has no reading: that word is the better report, so it is told first.
    let mut unread_parts: Vec<&(SpecRef, crate::reading::key::Unread)> = model.unread.iter().collect();
    unread_parts.sort_by_key(|(_, unread)| unread.kind == "an article" && unread.place.starts_with("between two words"));
    for (at, unread) in unread_parts {
        // A word of time or order that the temporal shape of the statement reads.
        if model.temporal.iter().any(|shape| shape.statement.id == at.id && shape.read.contains(&unread.part)) {
            continue;
        }
        if !told.insert(at.id.clone()) {
            continue;
        }
        let phrase = if unread.phrase.is_empty() { String::new() } else { format!(" (`{}`)", unread.phrase) };
        opaque.push(Diagnostic::error(UNSUPPORTED, format!("`{}` is {} {}{phrase}: no reading rule reads it there, so the statement is rejected; {}", unread.part, unread.kind, unread.place, advice(unread.kind)), vec![at.clone()]));
    }
    opaque.extend(unvisited(set, model, &told, lex));
    // A statement that names a declared type outside the typed fragment has
    // no reading over individuals: its atoms would stand apart from the
    // instances of the other statements.
    for outside in model.individuals.iter().flat_map(|i| &i.outside) {
        opaque.push(Diagnostic::error(UNSUPPORTED, format!("`{}` names a type of individuals in a form that no rule reads over individuals, so the statement is rejected: {}", outside.construct, outside.why), vec![outside.statement.clone()]));
    }
    // A share is a count of the activations of its statement. A statement
    // that is not read over individuals has no activations to count: one
    // representative stands for each type, and the share would be a
    // quantity that nothing ties to a behaviour.
    let counted: BTreeSet<&str> = model.individuals.iter().flat_map(|i| &i.shares).map(|share| share.statement.as_str()).collect();
    for pkg in &set.packages {
        for spec in pkg.documents.iter().flat_map(|doc| &doc.specs) {
            let display = if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) };
            let bounds_a_share = crate::expand::formalized(spec).iter().any(|sentence| matches!(&sentence.core, Core::Deontic { vp, .. } if vp.items().iter().any(|vp| crate::reading::model::proportion(vp).is_some())));
            if bounds_a_share && !counted.contains(display.as_str()) {
                let at = SpecRef { id: display, file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
                opaque.push(Diagnostic::error(UNSUPPORTED, "the statement bounds a share of a population (`share-of-representative`), and no rule counts the population here, so the statement is rejected: a share is a count of the activations of its statement, and a statement that names no declared type of individuals has one representative of each thing and no activations to count; declare the type that the statement is about, as in `individuals request`, and name it in the statement".to_string(), vec![at]));
            }
        }
    }

    // Ungrounded statements.
    let mut own: BTreeMap<String, (SpecRef, BTreeSet<String>)> = BTreeMap::new();
    for constraint in statements {
        let Some(at) = constraint.refs.first() else { continue };
        let entry = own.entry(at.id.clone()).or_insert_with(|| (at.clone(), BTreeSet::new()));
        signatures(&constraint.assume, &mut entry.1);
        signatures(&constraint.guarantee, &mut entry.1);
    }
    let mut held_by: BTreeMap<&String, BTreeSet<&String>> = BTreeMap::new();
    for (id, (_, signs)) in &own {
        for sign in signs {
            held_by.entry(sign).or_default().insert(id);
        }
    }
    // An axiom relates a statement to another one when it holds atoms of both.
    let mut related: BTreeSet<&String> = BTreeSet::new();
    // What a definition, an inclusion, an exclusion or a refinement says is an axiom too.
    let stated = model.constraints.iter().filter(|c| c.kind.is_axiom()).map(|c| (&c.guarantee, c.kind == ConstraintKind::Refinement));
    // Related by something other than a refinement.
    let mut related_closely: BTreeSet<&String> = BTreeSet::new();
    for (axiom, refinement) in model.background.iter().map(|f| (f, false)).chain(stated) {
        let mut signs = BTreeSet::new();
        signatures(axiom, &mut signs);
        let touched: BTreeSet<&String> = signs.iter().filter_map(|s| held_by.get(s)).flatten().copied().collect();
        if touched.len() > 1 {
            if !refinement {
                related_closely.extend(touched.iter().copied());
            }
            related.extend(touched);
        }
    }
    let mut refinement_only: Vec<SpecRef> = Vec::new();
    let documents = || set.packages.iter().flat_map(|p| &p.documents);
    // A check states a relation that a proof must establish.
    let checked: BTreeSet<&String> = documents().flat_map(|d| &d.checks).flat_map(|c| c.left.iter().chain(&c.right)).collect();
    // A primitive is named as it is written, in the namespace that declares it.
    let primitives: BTreeSet<String> = documents()
        .flat_map(|d| {
            let scoped = lex.in_document(d);
            // A measure declares the population that it names: the name is taken as given, as a primitive is.
            d.primitives.iter().chain(&d.measures).flat_map(move |p| {
                let plain = scoped.canon(&p.name);
                [scoped.resolve(&plain), plain]
            })
        })
        .collect();
    let local = |term: &str| term.rsplit("::").next().unwrap_or(term).to_string();
    // A statement without normative force describes the terms that it relates.
    let mut described: BTreeSet<String> = BTreeSet::new();
    for doc in documents() {
        let scoped = lex.in_document(doc);
        for spec in doc.specs.iter().filter(|spec| describes(&spec.sentence.core)) {
            for (term, kind) in occurrences(&spec.sentence, &scoped).into_iter().filter(|(_, kind)| *kind != "action") {
                // A value is named without its namespace, and the term that it names is described with it.
                if kind == "value" {
                    described.insert(scoped.resolve(&term));
                }
                described.insert(term);
            }
        }
    }
    // A modified phrase is a kind of its head, and is grounded with it.
    let heads: BTreeSet<Vec<String>> = crate::reading::meaning::grounded_heads(set, lex).into_keys().collect();
    let through_head = |term: &str| {
        let words: Vec<String> = local(term).split_whitespace().map(str::to_string).collect();
        words.len() > 1 && crate::reading::meaning::head_of(&words, &heads).is_some()
    };
    // A value is named without its namespace: the definition of the term that it names grounds it.
    let defined_locals: BTreeSet<String> = vocabulary.iter().filter(|(_, e)| e.defined_at.is_some() || e.signature.is_some()).map(|(term, _)| local(term).to_lowercase()).collect();
    let plain_term = |term: &str| described.contains(term) || primitives.contains(term) || primitives.contains(&local(term)) || vocabulary.get(term).is_some_and(|e| e.defined_at.is_some() || e.signature.is_some()) || (!term.contains("::") && defined_locals.contains(&term.to_lowercase())) || through_head(term);
    // A restricted phrase is a kind of the phrase that its clause restricts.
    let restricted_head = |term: &str| -> Option<String> {
        let padded = format!(" {} ", local(term).to_lowercase());
        let at = model.read_clauses.iter().filter_map(|clause| padded.find(&format!(" {clause} ")).or_else(|| padded.find(&format!(" {} ", clause.split_whitespace().take(2).collect::<Vec<_>>().join(" "))))).min()?;
        let head = padded[..at].trim().to_string();
        (!head.is_empty()).then_some(head)
    };
    // `trion language vocabulary::statement`: the owner of an `of` phrase stands before the qualified head.
    let owned_head = |term: &str| -> Option<String> {
        let at = term.split_whitespace().position(|w| w.contains("::"))?;
        (at > 0).then(|| term.split_whitespace().skip(at).collect::<Vec<_>>().join(" "))
    };
    // `noun of the specification` is named `specification noun`: a phrase is a kind of the head that ends it.
    let through_tail = |term: &str| {
        let (namespace, name) = term.rsplit_once("::").map_or((None, term), |(namespace, name)| (Some(namespace), name));
        let words: Vec<&str> = name.split_whitespace().collect();
        // `former statement` is no statement: a modifier that denies its head names no kind of it.
        let denied = words.iter().any(|word| crate::syntax::words::is_privative(&word.to_lowercase()) || word.starts_with("non-"));
        !denied && (1..words.len()).any(|at| {
            let tail = words[at..].join(" ");
            plain_term(&tail) || namespace.is_some_and(|namespace| plain_term(&format!("{namespace}::{tail}")))
        })
    };
    let grounded_term = |term: &str| {
        plain_term(term)
            || through_tail(term)
            // `one or more statements` names the term `statement`.
            || term.strip_suffix('s').is_some_and(|single| !single.ends_with('s') && (plain_term(single) || defined_locals.contains(&local(single).to_lowercase())))
            || owned_head(term).is_some_and(|head| plain_term(&head))
            || restricted_head(term).is_some_and(|head| {
                let scoped = term.rsplit_once("::").map(|(namespace, _)| format!("{namespace}::{head}"));
                plain_term(&head) || scoped.is_some_and(|name| plain_term(&name))
            })
    };

    // Properties beyond one model of a conjunction: one report for each statement and kind.
    let mut inexpressible = Vec::new();
    let mut told: BTreeSet<(String, &'static str)> = BTreeSet::new();
    let defined_names: BTreeSet<String> = vocabulary.iter().filter(|(_, e)| e.defined_at.is_some() || e.signature.is_some()).map(|(term, _)| local(term)).collect();
    let quality_grounded = |word: &str| primitives.contains(word) || defined_names.contains(word);
    // What a definition says about a value or an action gives it a meaning.
    let mut meant: BTreeSet<String> = BTreeSet::new();
    for axiom in model.constraints.iter().filter(|c| c.kind.is_axiom()) {
        signatures(&axiom.guarantee, &mut meant);
    }
    for constraint in model.constraints.iter().filter(|c| matches!(c.kind, ConstraintKind::Spec | ConstraintKind::Permission)) {
        let Some(at) = constraint.refs.first() else { continue };
        let mut visit = |atom: &Atom, _: bool| {
            let mut own = BTreeSet::new();
            signatures(&Formula::Atom(atom.clone()), &mut own);
            if own.iter().any(|sign| meant.contains(sign)) {
                return;
            }
            // The value of a closed domain is one of its listed states, not a quality.
            if let Atom::Val { attr, value } | Atom::Dom { attr, value } = atom {
                if model.closed_domains.get(attr).is_some_and(|values| values.contains(value)) {
                    return;
                }
            }
            let Some((kind, word, advice)) = name_of(atom).and_then(|name| beyond(name, &quality_grounded)) else { return };
            if told.insert((at.id.clone(), kind)) {
                // The statement is accepted and its quality has no meaning:
                // while it stands, nothing is verified of the statement.
                inexpressible.push(Diagnostic::error("inexpressible-property", format!("`{word}` states {kind}: {advice}"), vec![at.clone()]));
            }
        };
        constraint.assume.atoms(true, &mut visit);
        constraint.guarantee.atoms(true, &mut visit);
    }

    // Where a term is defined in a namespace that the statement does not use.
    let mut defined_in: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (term, entry) in vocabulary.iter().filter(|(_, e)| e.defined_at.is_some()) {
        if let Some((namespace, name)) = term.rsplit_once("::") {
            defined_in.entry(name.to_lowercase()).or_default().insert(namespace.to_string());
        }
        let _ = entry;
    }
    // A namespace of the root package is written with the package name before it.
    let root = set.packages.iter().find(|p| p.is_root).map(|p| p.name.clone()).unwrap_or_default();
    let foreign: Vec<&str> = set.packages.iter().filter(|p| !p.is_root).map(|p| p.name.as_str()).collect();
    let written = |namespace: &str| {
        let own = |package: &str| namespace == package || namespace.starts_with(&format!("{package}."));
        if root.is_empty() || own(&root) || foreign.iter().any(|package| own(package)) { namespace.to_string() } else { format!("{root}.{namespace}") }
    };
    let closed_values: BTreeSet<String> = model.closed_domains.values().flatten().flat_map(|value| [value.clone(), local(value)]).collect();
    let mut ungrounded = Vec::new();
    for doc in documents() {
        let scoped = lex.in_document(doc);
        let reachable: BTreeSet<&str> = std::iter::once(doc.namespace.as_str()).chain(doc.imports.iter().map(|i| i.namespace.as_str())).collect();
        let elsewhere = |term: &str| -> Option<String> {
            let name = local(term).to_lowercase();
            let owners: Vec<&String> = defined_in.get(&name)?.iter().filter(|ns| !reachable.contains(ns.as_str())).collect();
            match owners.as_slice() {
                [] => None,
                [one] => Some(format!("`{name}` is defined in the namespace `{one}`, which this namespace does not use: `use {}` gives it that meaning", written(one))),
                many => Some(format!("`{name}` is defined in the namespaces {}: a `use` of more than one of them makes the term ambiguous, so write the namespace, as in `{}::{name}`", many.iter().map(|ns| format!("`{ns}`")).collect::<Vec<_>>().join(" and "), many[0])),
            }
        };
        for spec in &doc.specs {
            // A definition says what its term is, and a statement without normative
            // force says which situations can occur: neither is a statement that
            // could constrain nothing.
            if matches!(spec.sentence.core, Core::Definition { .. }) || describes(&spec.sentence.core) {
                continue;
            }
            let id = spec.display_id();
            let Some((at, signs)) = own.get(&id) else { continue };
            let shares = signs.iter().any(|s| held_by.get(s).is_some_and(|ids| ids.len() > 1));
            if shares || related_closely.contains(&id) || checked.contains(&id) || is_part_checked(spec, &checked) {
                continue;
            }
            if related.contains(&id) {
                let listed = |term: &str, kind: &str| kind == "value" && (closed_values.contains(term) || closed_values.contains(&local(term)));
                if occurrences(&spec.sentence, &scoped).into_iter().any(|(term, kind)| kind != "action" && !listed(&term, kind) && !grounded_term(&term)) {
                    refinement_only.push(at.clone());
                }
                continue;
            }
            // The listed values of a closed domain are what the domain is: an enumeration grounds them.
            let listed = |term: &str, kind: &str| kind == "value" && (closed_values.contains(term) || closed_values.contains(&local(term)));
            let mut loose: Vec<String> = occurrences(&spec.sentence, &scoped).into_iter().filter(|(term, kind)| *kind != "action" && !listed(term, kind)).map(|(term, _)| term).filter(|term| !grounded_term(term)).collect();
            loose.sort();
            loose.dedup();
            if loose.is_empty() {
                continue;
            }
            let terms = loose.iter().map(|t| format!("`{t}`")).collect::<Vec<_>>().join(", ");
            let hints: Vec<String> = loose.iter().filter_map(|t| elsewhere(t)).collect();
            let hint = if hints.is_empty() { String::new() } else { format!("; {}", hints.join("; ")) };
            ungrounded.push(Diagnostic::error("ungrounded", format!("this statement excludes no interpretation of the other statements: no other statement, axiom or check shares an atom with it, and {terms} {} neither a definition nor a primitive declaration nor a description: define each term with `A <term> means …`, describe it in a statement without a modal verb, or declare it with `primitive <term>`{hint}", if loose.len() == 1 { "has" } else { "have" }), vec![at.clone()]));
        }
    }
    if std::env::var("TRION_PROFILE").is_ok() {
        eprintln!("grounded only through `detailed by`: {} statements", refinement_only.len());
    }
    Silence { opaque, ungrounded, inexpressible, refinement_only }
}

/// Whether a sentence has no normative force and defines no term: it
/// describes the things that it names.
fn describes(core: &Core) -> bool {
    match core {
        Core::Description { .. } | Core::Relation { .. } | Core::Existence { .. } => true,
        Core::Conjoined { items } => items.iter().all(describes),
        Core::Definition { .. } | Core::Deontic { .. } => false,
    }
}

/// The code of a statement with a part that has no formal reading.
pub(super) const UNSUPPORTED: &str = "UNSUPPORTED_SEMANTICS";

/// A form that is read, for each kind of unread part.
fn advice(kind: &str) -> &'static str {
    match kind {
        "a comparison" => "write the comparison after a copula with a number or a named quantity, as in `The size is at most 10 MB.` or `The timeout is less than the retry interval.`",
        "a clause" => "write the condition as a frame of the sentence (`When …,`, `While …,`, `If …, then`, `unless …`) or as a relative clause directly after its noun",
        "a temporal word" => "write the time as a role of the verb, as in `within 5 seconds`, `before the room is archived` or `until the user confirms`",
        "a word that tells two things apart" => "two things of one type are told apart by statements about individuals, as in `No two rooms have the same name.`, or by a term that a definition declares",
        "a quantifier" | "a pronoun" => "write the quantifier as the determiner of a noun phrase, as in `each request`, `no request` or `at most 3 requests`, and name the thing instead of pointing at it",
        "a preposition" => "write the phrase as a role after the verb, or define the whole phrase as a term with `A … means …`",
        "a conjunction" => "state each part as its own statement, or join whole noun phrases or whole verb phrases",
        "an article" => "write one determiner before the modifiers and the head of a noun phrase, as in `the source file`",
        "an auxiliary" | "a negation" => "write the modal and the negation before the verb, as in `shall not send`",
        "a word of time, order, number or degree" => "write `eventually`, `always` or `immediately` before the verb, or a deadline after it",
        _ => "state it with a number, as in `at most 10 MB`, or define the phrase as a term",
    }
}

/// The closed-class words that stand in an open place of a sentence. The
/// keys of a statement report the ones that reach them; this walk of the
/// whole tree finds the ones in a node that reached no key.
fn unvisited(set: &SpecSet, model: &Model, told: &BTreeSet<String>, lex: &Lexicon) -> Vec<Diagnostic> {
    use crate::syntax::words::{classify, WordClass};
    let mut out = Vec::new();
    let typed: BTreeSet<&str> = model.individuals.iter().flat_map(|i| &i.meanings).map(|m| m.statement.as_str()).collect();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let scoped = lex.in_document(doc);
        for spec in &doc.specs {
            let id = spec.display_id();
            if told.contains(&id) {
                continue;
            }
            let at = SpecRef { id: id.clone(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
            // A purpose states what the author intends; no formula follows from it.
            if let Some(purpose) = &spec.sentence.purpose {
                let opener = match purpose {
                    crate::syntax::ast::Purpose::SoThat(_) => "so that",
                    crate::syntax::ast::Purpose::InOrderTo(_) => "in order to",
                };
                out.push(Diagnostic::error(UNSUPPORTED, format!("the purpose after `{opener}` has no formal reading, so the statement is rejected; state the intended consequence as a statement of its own, as in `When the call is logged, the auditor shall review the call.`"), vec![at]));
                continue;
            }
            // `even when P` leaves the claim as it is: the claim holds where
            // P holds and where it does not, and P is no condition. `while
            // retaining X` says that something else holds at the same time,
            // and no rule makes a requirement of it.
            if let Some(concession) = spec.sentence.concession.as_ref().filter(|c| !crate::reading::rules::is_emphasis(c)) {
                out.push(Diagnostic::error(UNSUPPORTED, format!("`{concession}` states what holds while the statement is kept, and no reading rule makes a requirement of it, so the statement is rejected; state it as a requirement of its own, as in `The API shall retain the origin.`, or join it to the action with `and`"), vec![at]));
                continue;
            }
            // A construct that a rule names and gives no meaning.
            if let Some((rule, lost)) = crate::reading::rules::unresolved(&spec.sentence).into_iter().next() {
                out.push(Diagnostic::error(UNSUPPORTED, format!("the statement holds a construct without a meaning rule (`{rule}`), so the statement is rejected: {lost}"), vec![at]));
                continue;
            }
            for open in crate::reading::rules::open_words(&spec.sentence) {
                // The reading over individuals reads each word of a predicate
                // that it accepts: `is not a member of the room` is a relation.
                if open.place == crate::reading::rules::Place::Predicate && typed.contains(id.as_str()) {
                    continue;
                }
                // A word of time or order that the temporal shape of the statement reads.
                if model.temporal.iter().any(|shape| shape.statement.id == id && shape.read.contains(&open.word)) {
                    continue;
                }
                // `eventually respond` names `respond`: an obligation without a deadline is met at some later moment.
                if open.place == crate::reading::rules::Place::Manner && crate::syntax::words::is_liveness(&open.word) {
                    continue;
                }
                let WordClass::Closed(kind) = classify(&open.word) else { continue };
                // An article is read with its noun phrase. `only` restricts an
                // action: the key of the action reads it or reports it.
                if kind == crate::syntax::words::Closed::Article || open.word == "only" {
                    continue;
                }
                let phrase: Vec<String> = open.phrase.split_whitespace().map(str::to_string).collect();
                if scoped.in_declared_term(&open.word, &phrase) {
                    continue;
                }
                out.push(Diagnostic::error(UNSUPPORTED, format!("`{}` is {} {} (`{}`): no reading rule reads it there, so the statement is rejected; {}", open.word, kind.describe(), open.place.describe(), open.phrase, advice(kind.describe())), vec![at.clone()]));
                break;
            }
        }
    }
    out
}

fn is_part_checked(spec: &Spec, checked: &BTreeSet<&String>) -> bool {
    spec.parts.iter().any(|part| checked.contains(part))
}
