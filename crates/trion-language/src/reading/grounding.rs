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
use crate::reading::model::{ConstraintKind, Model};
use crate::reading::lexicon::Lexicon;
use trion_solver::{Atom, Formula};
use crate::syntax::ast::Core;
use crate::reading::vocabulary::{VocabEntry};
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
        return Some(("an optimum or a preference", word.to_string(), "it compares the system with every alternative: state a bound that each behaviour keeps"));
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

/// Finds unsupported readings and inexpressible properties.
pub fn silence(set: &SpecSet, model: &Model, vocabulary: &BTreeMap<String, VocabEntry>, lex: &Lexicon) -> Silence {
    // Unread parts: what the keys of a statement could not hold, and each
    // closed-class word in an open place of a node that reached no key.
    let mut opaque: Vec<Diagnostic> = Vec::new();
    let mut told: BTreeSet<String> = BTreeSet::new();
    // An article inside a name is often the trace of a word before it that
    // has no reading: that word is the better report, so it is told first.
    let mut unread_parts: Vec<&(SpecRef, crate::reading::key::Unread)> = model.unread.iter().collect();
    unread_parts.sort_by_key(|(_, unread)| unread.kind == "an article" && unread.place.starts_with("between two words"));
    // The reading over individuals reads each word of a predicate or a
    // value that it accepts: `is one of the members of the room` is a relation.
    let typed: BTreeSet<&str> = model.individuals.iter().flat_map(|i| &i.meanings).map(|m| m.statement.as_str()).chain(model.over_instances.iter().map(String::as_str)).collect();
    let sums = summed(model);
    for (at, unread) in unread_parts {
        // The arithmetic of a sum, and the articles of its terms, are read.
        if sums.get(at.id.as_str()).is_some_and(|read| unread.kind == "an article" || read.contains(&unread.part.to_lowercase())) {
            continue;
        }
        if typed.contains(at.id.as_str()) && (unread.place == crate::reading::key::Place::Predicate.describe() || unread.place == crate::reading::key::Place::Value.describe()) {
            continue;
        }
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

    let documents = || set.packages.iter().flat_map(|p| &p.documents);
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

    Silence { opaque, inexpressible, ..Silence::default() }
}

/// Whether a sentence has no normative force and defines no term: it
/// describes the things that it names.
pub(super) fn describes(core: &Core) -> bool {
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
        "a preposition" => "write the phrase as a role after the verb where the role has the intended meaning",
        "a conjunction" => "state each part as its own statement, or join whole noun phrases or whole verb phrases",
        "an article" => "write one determiner before the modifiers and the head of a noun phrase, as in `the source file`",
        "an auxiliary" | "a negation" => "write the modal and the negation before the verb, as in `shall not send`",
        "a word of time, order, number or degree" => "write `eventually`, `always` or `immediately` before the verb, or a deadline after it",
        _ => "state it with a number, as in `at most 10 MB` where the number captures the intended property",
    }
}

/// The closed-class words that stand in an open place of a sentence. The
/// keys of a statement report the ones that reach them; this walk of the
/// whole tree finds the ones in a node that reached no key.
/// The statements whose reading holds a sum of quantities, with the words
/// that the sum reads: the words of the names of its terms, and `twice`,
/// `half`, `times`, `plus` and `minus`, its arithmetic (`model::linear_np`).
fn summed(model: &Model) -> BTreeMap<&str, BTreeSet<String>> {
    let mut summed: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
    for c in &model.constraints {
        let mut words: Option<BTreeSet<String>> = None;
        let mut look = |atom: &Atom, _: bool| {
            if let Atom::Lin { terms, .. } = atom {
                let read = words.get_or_insert_with(|| ["plus", "minus", "twice", "half", "times"].iter().map(|w| w.to_string()).collect());
                for (name, _) in terms {
                    let local = name.rsplit("::").next().unwrap_or(name);
                    read.extend(local.split_whitespace().map(str::to_lowercase));
                }
            }
        };
        c.assume.atoms(true, &mut look);
        c.guarantee.atoms(true, &mut look);
        if let Some(words) = words {
            for r in &c.refs {
                summed.entry(r.id.as_str()).or_default().extend(words.iter().cloned());
            }
        }
    }
    summed
}

fn unvisited(set: &SpecSet, model: &Model, told: &BTreeSet<String>, lex: &Lexicon) -> Vec<Diagnostic> {
    let summed = summed(model);
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
                if summed.get(id.as_str()).is_some_and(|read| read.contains(&open.word)) {
                    continue;
                }
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
