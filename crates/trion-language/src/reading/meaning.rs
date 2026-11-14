//! What the vocabulary means: definitions, inclusion, exclusion and refinement.
//!
//! A statement of one of these kinds is an axiom about terms. It obliges
//! nobody; it relates the atoms that other statements are written over, so a
//! conflict in one term reaches the terms that are defined by it, included in
//! it or detailed by it.
//!
//! - `A guest means a user.` makes the two terms one.
//! - `A guest means a user without an account.` includes the guest in the
//!   user and denies the guest an account.
//! - `An archived room means a room that accepts no messages.` ties the state
//!   to what the room does in it.
//! - `Each guest is a user.` and `A guest is a kind of user.` include.
//! - `No guest is a member.` excludes two concepts.
//! - `No request is both accepted and rejected.` excludes two actions.
//! - `detailed by [ID], [ID]` under a statement makes the statement hold
//!   exactly when its details hold.
//!
//! The model speaks about one representative of each type. An inclusion
//! therefore carries what holds of every member of the wider term to the
//! narrower one; what holds of some individual is outside this reading.

use crate::document::SpecSet;
use crate::diagnostic::{Diagnostic, SpecRef};
use crate::document::Spec;
use crate::reading::model::{action_key, base_verb, np_key, participle_base, subject_key, Constraint, ConstraintKind, Model};
use crate::reading::lexicon::Lexicon;
use trion_solver::{Atom, Formula};
use crate::syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};

/// The name of a term without its namespace, as the words that keys spell it with.
fn local(key: &str) -> Vec<String> {
    key.rsplit("::").next().unwrap_or(key).split_whitespace().map(str::to_string).collect()
}

/// A word without its plural ending, in lower case.
/// A word as the heads of the vocabulary spell it.
pub(crate) fn fold_word(word: &str) -> String {
    fold(word)
}

fn fold(word: &str) -> String {
    let lower = word.to_lowercase();
    match lower.strip_suffix('s') {
        Some(stem) if stem.len() > 2 && !stem.ends_with('s') && !stem.ends_with('u') && !stem.ends_with('i') => stem.to_string(),
        _ => lower,
    }
}

/// A key cut into its words and what stands between them.
fn pieces(key: &str) -> Vec<(bool, String)> {
    let mut out: Vec<(bool, String)> = Vec::new();
    for c in key.chars() {
        let word = c.is_alphanumeric() || c == '-' || c == '_' || c == '\'' || c == '`' || c == '/' || c == '.';
        match out.last_mut() {
            Some((kind, text)) if *kind == word => text.push(c),
            _ => out.push((word, c.to_string())),
        }
    }
    out
}

/// The pieces of a key with the folded spelling of each word. A key is cut
/// once: the relations of a package ask for the same keys again and again.
type Cut = std::rc::Rc<Vec<(bool, String, String)>>;

fn cut(key: &str) -> Cut {
    thread_local! {
        static CUTS: std::cell::RefCell<std::collections::HashMap<String, Cut>> = std::cell::RefCell::new(std::collections::HashMap::new());
    }
    CUTS.with(|cuts| {
        if let Some(found) = cuts.borrow().get(key) {
            return found.clone();
        }
        let made: Cut = std::rc::Rc::new(pieces(key).into_iter().map(|(word, text)| { let folded = if word { fold(&text) } else { text.clone() }; (word, text, folded) }).collect());
        cuts.borrow_mut().insert(key.to_string(), made.clone());
        made
    })
}

fn folded(key: &str) -> String {
    thread_local! {
        static FOLDED: std::cell::RefCell<std::collections::HashMap<String, String>> = std::cell::RefCell::new(std::collections::HashMap::new());
    }
    FOLDED.with(|known| {
        if let Some(found) = known.borrow().get(key) {
            return found.clone();
        }
        let made: String = cut(key).iter().map(|(_, _, folded)| folded.as_str()).collect();
        known.borrow_mut().insert(key.to_string(), made.clone());
        made
    })
}

/// The key with each occurrence of the words `from` replaced by `to`. An
/// occurrence is a run of whole words that single spaces separate.
fn substitute(key: &str, from: &[String], to: &[String]) -> Option<String> {
    if from.is_empty() {
        return None;
    }
    let parts = cut(key);
    let first = fold(&from[0]);
    // Most keys do not hold the first word at all.
    if !parts.iter().any(|(word, _, folded)| *word && *folded == first) {
        return None;
    }
    let from: Vec<String> = std::iter::once(first).chain(from[1..].iter().map(|w| fold(w))).collect();
    let mut out = String::new();
    let mut found = false;
    let mut i = 0;
    while i < parts.len() {
        let matches = parts[i].0
            && from.iter().enumerate().all(|(k, word)| {
                let at = i + 2 * k;
                parts.get(at).is_some_and(|(is_word, _, folded)| *is_word && folded == word) && (k == 0 || parts.get(at - 1).is_some_and(|(_, gap, _)| gap == " "))
            });
        if matches {
            out.push_str(&to.join(" "));
            found = true;
            i += 2 * from.len() - 1;
        } else {
            out.push_str(&parts[i].1);
            i += 1;
        }
    }
    found.then_some(out)
}

#[derive(Debug, Clone)]
enum Relation {
    /// Every `narrow` is a `wide`. `asserted` is the atom that says so.
    Includes { narrow: Vec<String>, wide: Vec<String>, both_ways: bool },
    /// Nothing is both.
    Excludes { first: Vec<String>, second: Vec<String> },
    /// No `object` undergoes both actions.
    ExclusiveActions { first: String, second: String, object: Vec<String> },
    /// What holds of the holder in the defined state or class.
    Property { holder: String, state: Option<String>, formula: Formula },
    /// The holder is in the state whenever the formula holds: the other
    /// direction of a definition of a state.
    Converse { holder: String, state: String, formula: Formula },
}

struct Stated {
    relation: Relation,
    origin: SpecRef,
    /// The atom that states an inclusion, for the chains through other inclusions.
    atom: Option<Atom>,
}

fn article(word: &str) -> bool {
    crate::syntax::words::is_article(word)
}

/// The term that a predicate nominal names: `a user`, `a kind of user`.
fn nominal(words: &[String], bare: bool, lex: &Lexicon) -> Option<Vec<String>> {
    let (first, rest) = words.split_first()?;
    // `No controlled natural language is English.` names its second concept without an article.
    let rest = if ["a", "an"].contains(&first.to_lowercase().as_str()) {
        rest
    } else if bare {
        words
    } else {
        return None;
    };
    if rest.is_empty() {
        return None;
    }
    let rest = match rest {
        [kind, of, tail @ ..] if ["kind", "sort", "type"].contains(&kind.to_lowercase().as_str()) && of.eq_ignore_ascii_case("of") && !tail.is_empty() => tail,
        other => other,
    };
    // A term is a plain noun phrase: `a document in the trion language` describes, it does not classify.
    use crate::syntax::words::{classify, Closed, WordClass};
    if rest.iter().any(|w| matches!(classify(w), WordClass::Closed(Closed::Preposition | Closed::Conjunction | Closed::Pronoun | Closed::Negation))) {
        return None;
    }
    let rest: Vec<&str> = rest.iter().map(String::as_str).filter(|w| !article(w)).collect();
    Some(local(&lex.canon(&rest.join(" "))))
}

fn plain(np: &Np) -> bool {
    np.of.is_none() && np.relative.is_none()
}

/// The verb forms under which statements may spell one action.
fn spellings(verb: &str) -> Vec<String> {
    let base = base_verb(verb);
    let third = match base.as_str() {
        "have" => "has".to_string(),
        "do" => "does".to_string(),
        other if other.ends_with('y') && !other.ends_with("ay") && !other.ends_with("ey") && !other.ends_with("oy") => format!("{}ies", &other[..other.len() - 1]),
        other if ["s", "x", "z", "ch", "sh", "o"].iter().any(|e| other.ends_with(e)) => format!("{other}es"),
        other => format!("{other}s"),
    };
    let mut out = vec![base, third, verb.to_string()];
    out.sort();
    out.dedup();
    out
}

/// The actions of `holder` that a difference of a definition speaks about,
/// and whether the difference denies them.
fn difference(holder: &str, verb: &str, particle: &Option<String>, object: &Option<NpGroup>, denied: bool, lex: &Lexicon) -> (Vec<String>, bool) {
    let mut object = object.clone();
    let mut denied = denied;
    if let Some(NpGroup::Single(np)) = &mut object {
        if matches!(np.det, Some(Det::No)) {
            np.det = None;
            denied = true;
        }
    }
    let keys = spellings(verb).into_iter().map(|verb| action_key(holder, &Vp { verb, particle: particle.clone(), manner: Vec::new(), object: object.clone(), roles: Vec::new(), complement: None, content: None }, lex)).collect();
    (keys, denied)
}

/// What a relative clause says of each member of `class`, whose key is `holder`.
fn relative_property(class: &Np, holder: &str, relative: &Relative, lex: &Lexicon) -> Option<Formula> {
    let exists = Formula::atom(Atom::Event { key: format!("exists {holder}") });
    match &relative.body {
        RelativeBody::Verbal { verb, particle, object, negation, .. } => {
            let (keys, denied) = difference(holder, verb, particle, object, negation.is_some(), lex);
            let acts: Vec<Formula> = keys.into_iter().map(|key| Formula::atom(Atom::Act { key })).collect();
            Some(if denied { Formula::And(acts.into_iter().map(Formula::not).collect()) } else { Formula::implies(exists, Formula::Or(acts)) })
        }
        RelativeBody::Copular { copula, predicate, agent, roles } => {
            let described = Clause { subject: NpGroup::Single(class.clone()), body: ClauseBody::Copular { copula: *copula, predicate: predicate.clone(), agent: agent.clone(), roles: roles.clone() } };
            Some(crate::reading::model::clause_formula(&described, lex))
        }
        // `a request that the gateway forwards`: the subject of the clause acts on each member.
        RelativeBody::ObjectGap { subject: NpGroup::Single(actor), verb, particle, .. } if relative.marker != RelMarker::Whose => {
            let mut object = class.clone();
            object.det = None;
            let (keys, _) = difference(&subject_key(actor, lex), verb, particle, &Some(NpGroup::Single(object)), false, lex);
            let acts: Vec<Formula> = keys.into_iter().map(|key| Formula::atom(Atom::Act { key })).collect();
            // `a weight that no set exceeds`: no member undergoes the action.
            Some(if matches!(actor.det, Some(Det::No)) { Formula::And(acts.into_iter().map(Formula::not).collect()) } else { Formula::implies(exists, Formula::Or(acts)) })
        }
        // `a name whose first component is the package name`: the clause describes a part of each member.
        RelativeBody::Content { clause } if relative.marker == RelMarker::Whose => match &clause.subject {
            NpGroup::Single(part) if part.of.is_none() => {
                let mut owned = part.clone();
                let mut owner = class.clone();
                owner.det = None;
                owned.of = Some(Box::new(owner));
                let described = Clause { subject: NpGroup::Single(owned), body: clause.body.clone() };
                Some(crate::reading::model::clause_formula(&described, lex))
            }
            _ => None,
        },
        // `a moment where the condition holds`: the clause holds of each member.
        RelativeBody::Content { clause } if relative.marker == RelMarker::Where => Some(Formula::implies(exists, crate::reading::model::clause_formula(clause, lex))),
        _ => None,
    }
}

/// The preposition and the noun phrases of a role that says where, with what
/// or about what a thing is. A role of time or of measure is none.
fn role_predicate(role: &RolePp) -> Option<(String, NpGroup)> {
    match role {
        RolePp::Other { preposition, np } | RolePp::Location { preposition, np } => Some((preposition.to_lowercase(), np.clone())),
        RolePp::Topic(np) => Some(("about".to_string(), np.clone())),
        RolePp::Recipient(np) => Some(("to".to_string(), np.clone())),
        RolePp::Source(np) => Some(("from".to_string(), np.clone())),
        RolePp::Goal(np) => Some(("into".to_string(), np.clone())),
        RolePp::Agent(np) => Some(("by".to_string(), np.clone())),
        _ => None,
    }
}

/// The reading of a definition: the term is a kind of its genus, and each
/// difference is a property of the members of the term. A definiens that
/// has no such reading is reported as unread.
fn definition(term: &Np, definiens: &Definiens, lex: &Lexicon) -> Vec<(Relation, Option<Atom>)> {
    let mut out: Vec<(Relation, Option<Atom>)> = Vec::new();
    if term.relative.is_some() {
        crate::reading::key::unread_node("that", "a relative clause", "in the defined term of a definition");
        return out;
    }
    let term_words = local(&np_key(term, lex));
    let includes = |narrow: &[String], wide: &[String], both_ways: bool, attr: String| (Relation::Includes { narrow: narrow.to_vec(), wide: wide.to_vec(), both_ways }, Some(Atom::Dom { attr, value: wide.join(" ") }));
    match definiens {
        Definiens::Clause(_) => {
            crate::reading::key::unread_node("means", "a clause", "after `means`, where the kind of the term is expected: name a kind and state what its members do in a relative clause");
        }
        // `a diagram of the steps and the choices`: a definition names one kind, so the list belongs to its `of`.
        Definiens::Np { np: NpGroup::Coordinated { conj: Conj::And, items, .. }, roles } if items[0].of.as_ref().is_some_and(|of| of.relative.is_none()) && items[0].of_also.is_empty() && items[0].relative.is_none() => {
            let mut genus = items[0].clone();
            genus.of_also = items[1..].to_vec();
            genus.of_conj = Some(Conj::And);
            return definition(term, &Definiens::Np { np: NpGroup::Single(genus), roles: roles.clone() }, lex);
        }
        Definiens::Np { np: NpGroup::Coordinated { conj: Conj::And, .. }, .. } => {
            crate::reading::key::unread_node("and", "a conjunction", "between two kinds in a definition, where one kind is expected: name the kind, as in `a pair of A and B` or `a collection of A and of B`");
        }
        Definiens::Np { np: NpGroup::Coordinated { conj: Conj::Or, items, .. }, roles } => {
            if !roles.is_empty() {
                crate::reading::key::unread_node(&roles[0].render(), "a role", "after the alternative kinds of a definition");
                return out;
            }
            // `A statement means a definition, a description or an obligation.`:
            // each kind is a kind of the term, and each member of the term is of one of the kinds.
            let mut kinds = Vec::new();
            for item in items {
                let mut kind = item.clone();
                kind.relative = None;
                let words = local(&np_key(&kind, lex));
                if words.is_empty() || words == term_words {
                    continue;
                }
                out.push((Relation::Includes { narrow: words.clone(), wide: term_words.clone(), both_ways: false }, Some(Atom::Dom { attr: subject_key(&kind, lex), value: term_words.join(" ") })));
                kinds.push(Formula::atom(Atom::Dom { attr: subject_key(term, lex), value: words.join(" ") }));
                let holder = subject_key(&kind, lex);
                let mut relative = item.relative.as_deref();
                while let Some(clause) = relative {
                    match relative_property(&kind, &holder, clause, lex) {
                        Some(formula) => out.push((Relation::Property { holder: holder.clone(), state: None, formula }, None)),
                        None => crate::reading::key::unread_node(&crate::reading::key::text(&crate::reading::key::relative_parts(clause, lex)), "a relative clause", "that has no reading in a definition"),
                    }
                    relative = clause.and.as_deref();
                }
            }
            if kinds.len() > 1 {
                let exists = Formula::atom(Atom::Event { key: format!("exists {}", subject_key(term, lex)) });
                out.push((Relation::Property { holder: subject_key(term, lex), state: None, formula: Formula::implies(exists, Formula::Or(kinds)) }, None));
            }
        }
        Definiens::Np { np: NpGroup::Single(genus), roles } => {
            let mut genus_plain = genus.clone();
            genus_plain.relative = None;
            let mut genus_head = genus_plain.clone();
            genus_head.of = None;
            genus_head.of_also = Vec::new();
            genus_head.of_conj = None;
            let genus_words = local(&np_key(&genus_head, lex));
            let owned_words = genus.of.is_some().then(|| local(&np_key(&genus_plain, lex)));
            // `a specification assembled from files`: a participle after the noun is a clause without its marker.
            let head = genus.head.to_lowercase();
            let participle = head.len() > 4 && head.ends_with("ed") && !head.ends_with("eed") && !genus.modifiers.is_empty() && (!roles.is_empty() || genus.of.is_some()) && !lex.declares(&genus_words);
            if participle {
                crate::reading::key::unread_node(&genus.head, "a participle", "after the noun of a definition, where a relative clause is expected: write `that is ...` or `that ...`");
                return out;
            }
            // `An archived room means a room that …`: a state of the genus.
            let state = ((genus.relative.is_some() || !roles.is_empty()) && genus.of.is_none() && !term.modifiers.is_empty() && term.head.eq_ignore_ascii_case(&genus.head) && genus.modifiers.is_empty()).then(|| crate::reading::key::collect(|| crate::reading::key::text(&crate::reading::key::word_parts(&term.modifiers, crate::reading::key::Place::Modifier, lex))).0);
            let (class, holder) = if state.is_some() { (genus_head.clone(), subject_key(&genus_head, lex)) } else { (term.clone(), subject_key(term, lex)) };
            let mut differences: Vec<Formula> = Vec::new();
            let mut relative = genus.relative.as_deref();
            while let Some(clause) = relative {
                let property = match &clause.body {
                    RelativeBody::Verbal { verb, particle, object, negation, .. } => {
                        let (keys, denied) = difference(&holder, verb, particle, object, negation.is_some(), lex);
                        let acts: Vec<Formula> = keys.into_iter().map(|key| Formula::atom(Atom::Act { key })).collect();
                        // What every member does is said of the members that exist, as a relation is.
                        let exists = Formula::atom(Atom::Event { key: format!("exists {holder}") });
                        Some(if denied {
                            Formula::And(acts.into_iter().map(Formula::not).collect())
                        } else if state.is_some() {
                            Formula::Or(acts)
                        } else {
                            Formula::implies(exists, Formula::Or(acts))
                        })
                    }
                    // `the assumption that each trace gives a model`: the clause is the content of the genus, a part of its name.
                    RelativeBody::Content { .. } if clause.marker == RelMarker::That => {
                        relative = clause.and.as_deref();
                        continue;
                    }
                    _ => relative_property(&class, &holder, clause, lex),
                };
                match property {
                    Some(formula) => differences.push(formula),
                    None => crate::reading::key::unread_node(&crate::reading::key::text(&crate::reading::key::relative_parts(clause, lex)), "a relative clause", "that has no reading in a definition"),
                }
                relative = clause.and.as_deref();
            }
            for role in roles {
                let property = match role {
                    RolePp::Other { preposition, np } if preposition.eq_ignore_ascii_case("without") => {
                        let (keys, _) = difference(&holder, "have", &None, &Some(np.clone()), true, lex);
                        Some(Formula::And(keys.into_iter().map(|key| Formula::not(Formula::atom(Atom::Act { key }))).collect()))
                    }
                    RolePp::Other { preposition, np } if preposition.eq_ignore_ascii_case("with") => {
                        let (keys, denied) = difference(&holder, "have", &None, &Some(np.clone()), false, lex);
                        let acts: Vec<Formula> = keys.into_iter().map(|key| Formula::atom(Atom::Act { key })).collect();
                        let exists = Formula::atom(Atom::Event { key: format!("exists {holder}") });
                        Some(if denied {
                            Formula::And(acts.into_iter().map(Formula::not).collect())
                        } else if state.is_some() {
                            Formula::Or(acts)
                        } else {
                            Formula::implies(exists, Formula::Or(acts))
                        })
                    }
                    other => role_predicate(other).map(|(preposition, np)| {
                        let described = Clause { subject: NpGroup::Single(class.clone()), body: ClauseBody::Copular { copula: ClauseCopula::Is, predicate: Predicate::Pp { preposition, np }, agent: None, roles: Vec::new() } };
                        crate::reading::model::clause_formula(&described, lex)
                    }),
                };
                match property {
                    Some(formula) => differences.push(formula),
                    None => crate::reading::key::unread_node(&role.render(), "a role", "that has no reading after the genus of a definition"),
                }
            }
            if state.is_none() && term_words != genus_words {
                let alone = differences.is_empty() && roles.is_empty() && genus.relative.is_none();
                let attr = subject_key(term, lex);
                match &owned_words {
                    // `a collection of declarations`: the term is such a collection, and such a collection is a collection.
                    Some(owned) if *owned != term_words => {
                        out.push(includes(&term_words, owned, alone, attr.clone()));
                        out.push(includes(&term_words, &genus_words, false, attr));
                    }
                    _ => out.push(includes(&term_words, &genus_words, alone, attr)),
                }
            }
            // `An archived room means a room that accepts no messages.` states an
            // equivalence. In the definition of a state, what the holder does is
            // a disposition of the holder: the room is disposed to accept
            // messages or it is not, at each moment, whether or not a message
            // arrives. An action completes only where its holder is disposed to
            // it. Read so, the state holds exactly when the differences hold,
            // and a holder that is idle is in no state for that reason.
            if let Some(value) = &state {
                let keys = std::cell::RefCell::new(Vec::<String>::new());
                let disposed = |key: &str| Atom::Event { key: format!("disposed to {key}") };
                let differences: Vec<Formula> = differences
                    .into_iter()
                    .map(|formula| {
                        formula.map_atoms(&|atom| match atom {
                            Atom::Act { key } => {
                                keys.borrow_mut().push(key.clone());
                                disposed(&key)
                            }
                            other => other,
                        })
                    })
                    .collect();
                let mut keys = keys.into_inner();
                keys.sort();
                keys.dedup();
                for key in keys {
                    out.push((Relation::Property { holder: holder.clone(), state: None, formula: Formula::implies(Formula::atom(Atom::Act { key: key.clone() }), Formula::atom(disposed(&key))) }, None));
                    // A holder that is forbidden an action is not one that does
                    // it: `a secure API means an API that encrypts the message`
                    // and `the API shall not encrypt the message` leave no
                    // secure API. Without this, a definition by an action that
                    // is done kept its word from being reported and nothing
                    // followed from it against a prohibition (acceptance case A03b).
                    out.push((Relation::Property { holder: holder.clone(), state: None, formula: Formula::implies(Formula::atom(Atom::Forbid { key: key.clone() }), Formula::not(Formula::atom(disposed(&key)))) }, None));
                }
                if !differences.is_empty() {
                    out.push((Relation::Converse { holder: holder.clone(), state: value.clone(), formula: Formula::And(differences.clone()) }, None));
                }
                for formula in differences {
                    out.push((Relation::Property { holder: holder.clone(), state: state.clone(), formula }, None));
                }
                return out;
            }
            for formula in differences {
                out.push((Relation::Property { holder: holder.clone(), state: state.clone(), formula }, None));
            }
        }
    }
    out
}

fn stated(spec: &Spec, origin: &SpecRef, lex: &Lexicon) -> Vec<Stated> {
    let sentence = &spec.sentence;
    let unconditional = sentence.frames.scopes.is_empty() && sentence.frames.states.is_empty() && sentence.frames.trigger.is_none() && sentence.exception.is_none();
    let mut out = Vec::new();
    let mut push = |relation: Relation, atom: Option<Atom>| out.push(Stated { relation, origin: origin.clone(), atom });
    match &sentence.core {
        Core::Definition { term, definiens } => {
            let (found, sink) = crate::reading::key::collect(|| definition(term, definiens, lex));
            // A definition that passes says what its term is: one that yields no axiom is rejected.
            let silent = found.is_empty() && sink.unread.is_empty();
            crate::reading::key::forward(sink);
            if silent {
                crate::reading::key::unread_node(&term.render(), "a definition", "that says nothing of its term: name a kind that differs from the term, or state a difference in a relative clause");
            }
            for (relation, atom) in found {
                push(relation, atom);
            }
        }
        Core::Description { subject: NpGroup::Single(subject), adverb: None, predicate: Predicate::Words { words }, agent: None, .. } if unconditional && plain(subject) => {
            let Some(other) = nominal(words, matches!(subject.det, Some(Det::No)), lex) else { return out };
            let own = local(&np_key(subject, lex));
            if own == other {
                return out;
            }
            match subject.det {
                Some(Det::Each | Det::Every | Det::A | Det::An) => {
                    let atom = Atom::Dom { attr: subject_key(subject, lex), value: crate::reading::key::text(&crate::reading::key::predicate_word_parts(words, lex)) };
                    push(Relation::Includes { narrow: own, wide: other, both_ways: false }, Some(atom));
                }
                Some(Det::No) => push(Relation::Excludes { first: own, second: other }, None),
                _ => {}
            }
        }
        Core::Description { subject: NpGroup::Single(subject), adverb: None, predicate: Predicate::Enumeration { conj: Conj::And, values, .. }, agent: None, .. } if unconditional && matches!(subject.det, Some(Det::No)) && plain(subject) => {
            let object = local(&np_key(subject, lex));
            let verbs: Vec<String> = values.iter().map(|v| participle_base(&v.to_lowercase(), lex)).collect();
            for (i, first) in verbs.iter().enumerate() {
                for second in &verbs[i + 1..] {
                    push(Relation::ExclusiveActions { first: first.clone(), second: second.clone(), object: object.clone() }, None);
                }
            }
        }
        _ => {}
    }
    out
}

/// Every atom of the contracts, by kind.
#[derive(Default)]
struct Atoms {
    /// Folded key to the keys as written, for actions, prohibitions and advice.
    acts: BTreeMap<String, BTreeSet<String>>,
    events: BTreeMap<String, BTreeSet<String>>,
    /// Attribute to its values, for states and domains.
    values: BTreeMap<String, BTreeSet<String>>,
    numbers: Vec<Atom>,
    /// Each word to the folded keys and the attributes that hold it, so an
    /// inclusion looks only at the atoms that name its wider term.
    act_words: BTreeMap<String, BTreeSet<String>>,
    event_words: BTreeMap<String, BTreeSet<String>>,
    value_words: BTreeMap<String, BTreeSet<String>>,
    /// The subjects whose existence a statement speaks about.
    existing: BTreeSet<String>,
}

fn index(keys: impl Iterator<Item = String>) -> BTreeMap<String, BTreeSet<String>> {
    let mut out: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for key in keys {
        for (word, text) in pieces(&key) {
            if word {
                out.entry(fold(&text)).or_default().insert(key.clone());
            }
        }
    }
    out
}

/// What an atom is about, whichever way a statement speaks of it: a value
/// of an attribute, held or admitted, and an action, done, forbidden or
/// advised against.
fn owned(atom: &Atom) -> String {
    match atom {
        Atom::Val { attr, value } | Atom::Dom { attr, value } => format!("value {attr} = {value}"),
        Atom::Act { key } | Atom::Forbid { key } | Atom::Discouraged { key } => format!("action {key}"),
        other => other.to_string(),
    }
}

fn atoms_of(model: &Model) -> Atoms {
    atoms_of_constraints(model.constraints.iter())
}

fn atoms_of_constraints<'a>(constraints: impl Iterator<Item = &'a Constraint>) -> Atoms {
    let mut atoms = Atoms::default();
    for c in constraints {
        let mut visit = |a: &Atom, _: bool| match a {
            Atom::Act { key } | Atom::Forbid { key } | Atom::Discouraged { key } => {
                atoms.acts.entry(folded(key)).or_default().insert(key.clone());
            }
            Atom::Event { key } if key.starts_with("exists ") => {
                atoms.existing.insert(key["exists ".len()..].to_string());
            }
            Atom::Event { key } if !key.starts_with("reach ") => {
                atoms.events.entry(folded(key)).or_default().insert(key.clone());
            }
            Atom::Val { attr, value } | Atom::Dom { attr, value } => {
                atoms.values.entry(attr.clone()).or_default().insert(value.clone());
            }
            Atom::Num { .. } => {
                if !atoms.numbers.contains(a) {
                    atoms.numbers.push(a.clone());
                }
            }
            _ => {}
        };
        c.assume.atoms(true, &mut visit);
        c.guarantee.atoms(true, &mut visit);
    }
    atoms.act_words = index(atoms.acts.keys().cloned());
    atoms.event_words = index(atoms.events.keys().cloned());
    atoms.value_words = index(atoms.values.keys().cloned());
    atoms
}

fn act(key: &str) -> Formula {
    Formula::atom(Atom::Act { key: key.to_string() })
}

/// What an inclusion says about the atoms that exist: whatever holds of every
/// member of the wider term holds of the narrower one, and whatever happens to
/// a member of the narrower term happens to a member of the wider one.
fn carry(narrow: &[String], wide: &[String], atoms: &Atoms, out: &mut Vec<Formula>) {
    let Some(first) = wide.first().map(|w| fold(w)) else { return };
    let none = BTreeSet::new();
    for key in atoms.act_words.get(&first).unwrap_or(&none) {
        let Some(written) = atoms.acts.get(key) else { continue };
        let Some(narrowed) = substitute(key, wide, narrow) else { continue };
        let Some(targets) = atoms.acts.get(&folded(&narrowed)) else { continue };
        for general in written {
            for specific in targets.iter().filter(|t| *t != general) {
                out.push(Formula::implies(act(general), act(specific)));
                out.push(Formula::implies(Formula::atom(Atom::Forbid { key: general.clone() }), Formula::atom(Atom::Forbid { key: specific.clone() })));
                out.push(Formula::implies(Formula::atom(Atom::Discouraged { key: general.clone() }), Formula::atom(Atom::Discouraged { key: specific.clone() })));
            }
        }
    }
    for key in atoms.event_words.get(&first).unwrap_or(&none) {
        let Some(written) = atoms.events.get(key) else { continue };
        let Some(narrowed) = substitute(key, wide, narrow) else { continue };
        let Some(sources) = atoms.events.get(&folded(&narrowed)) else { continue };
        for general in written {
            for specific in sources.iter().filter(|s| *s != general) {
                out.push(Formula::implies(Formula::atom(Atom::Event { key: specific.clone() }), Formula::atom(Atom::Event { key: general.clone() })));
            }
        }
    }
    // Where a member of the narrower term exists, a member of the wider term exists.
    let named = |subject: &String, words: &[String]| local(subject).iter().map(|w| fold(w)).eq(words.iter().map(|w| fold(w)));
    for specific in atoms.existing.iter().filter(|s| named(s, narrow)) {
        for general in atoms.existing.iter().filter(|s| named(s, wide)) {
            let exists = |subject: &String| Formula::atom(Atom::Event { key: format!("exists {subject}") });
            out.push(Formula::implies(exists(specific), exists(general)));
        }
    }
    // A description of the wider term describes the narrower one.
    for attr in atoms.value_words.get(&first).unwrap_or(&none) {
        let Some(values) = atoms.values.get(attr) else { continue };
        let Some(narrowed) = substitute(attr, wide, narrow) else { continue };
        let wanted = folded(&narrowed);
        let Some((target, theirs)) = atoms.value_words.get(&fold(&narrow[0])).unwrap_or(&none).iter().filter(|other| *other != attr && folded(other) == wanted).find_map(|other| atoms.values.get_key_value(other)) else { continue };
        for value in values.intersection(theirs) {
            let dom = |attr: &String| Formula::atom(Atom::Dom { attr: attr.clone(), value: value.clone() });
            out.push(Formula::implies(dom(attr), dom(target)));
        }
    }
    // A thing whose value is the narrower concept has the wider one too.
    let (narrow_value, wide_value) = (narrow.join(" "), wide.join(" "));
    let (narrow_folded, wide_folded) = (folded(&narrow_value), folded(&wide_value));
    for (attr, values) in &atoms.values {
        let find = |name: &String| values.iter().find(|v| folded(v) == *name);
        if let (Some(n), Some(w)) = (find(&narrow_folded), find(&wide_folded)) {
            let dom = |value: &String| Formula::atom(Atom::Dom { attr: attr.clone(), value: value.clone() });
            let val = |value: &String| Formula::atom(Atom::Val { attr: attr.clone(), value: value.clone() });
            out.push(Formula::implies(dom(n), dom(w)));
            out.push(Formula::implies(val(n), val(w)));
        }
    }
}


/// The grounded head of a modified phrase: `cited statement` is a kind of
/// `statement`. `heads` holds the folded words of each defined or primitive
/// term; the longest one that ends the phrase decides.
pub(crate) fn head_of<'a>(phrase: &[String], heads: &'a BTreeSet<Vec<String>>) -> Option<&'a Vec<String>> {
    let words: Vec<String> = phrase.iter().map(|w| fold(w)).collect();
    if words.iter().any(|w| crate::syntax::words::is_privative(w) || w.starts_with("non-")) {
        return None;
    }
    (1..words.len()).find_map(|at| heads.get(&words[at..].to_vec()))
}

/// The folded words of each term that a definition or a primitive declaration grounds.
pub(crate) fn grounded_heads(set: &SpecSet, lex: &Lexicon) -> BTreeMap<Vec<String>, SpecRef> {
    let mut heads = BTreeMap::new();
    for pkg in &set.packages {
        for doc in &pkg.documents {
            let scoped = lex.in_document(doc);
            for spec in &doc.specs {
                if let Core::Definition { term, .. } = &spec.sentence.core {
                    let words: Vec<String> = local(&np_key(term, &scoped)).iter().map(|w| fold(w)).collect();
                    let display = if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) };
                    heads.entry(words).or_insert(SpecRef { id: display, file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() });
                }
            }
            for primitive in &doc.primitives {
                let words: Vec<String> = local(&scoped.canon(&primitive.name)).iter().map(|w| fold(w)).collect();
                heads.entry(words).or_insert(SpecRef { id: format!("{}:{}", primitive.file, primitive.line), file: primitive.file.clone(), line: primitive.line, text: format!("primitive {}", primitive.name) });
            }
        }
    }
    heads
}

/// The folded words of each declared name as it is written: the term of a
/// definition, a primitive, a declared term, an alias and what it stands for.
/// A closed-class word is a word of a name only inside one of these.
pub(super) fn declared_terms(set: &SpecSet, lex: &Lexicon) -> BTreeSet<Vec<String>> {
    let mut out: BTreeSet<Vec<String>> = grounded_heads(set, lex).into_keys().collect();
    let written = |name: &str| -> Vec<String> { name.split_whitespace().map(|w| fold(w.trim_matches('`'))).filter(|w| !matches!(w.as_str(), "the" | "a" | "an")).collect() };
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        out.extend(doc.vocabulary.iter().map(|d| written(&d.term)));
        out.extend(doc.primitives.iter().chain(&doc.measures).map(|d| written(&d.name)));
        out.extend(doc.aliases.iter().flat_map(|a| [written(&a.term), written(&a.canonical)]));
        for spec in &doc.specs {
            if let Core::Definition { term, .. } = &spec.sentence.core {
                out.insert(crate::reading::model::np_words(term).iter().flat_map(|w| written(w)).collect());
            }
        }
    }
    out
}

/// The restricted noun phrases of a sentence, and each clause that stands as
/// the content of a verb or of a noun: `assert that the trigger occurs`,
/// `a proof that the guards are exclusive`.
fn restricted_and_contents(sentence: &Sentence, out: &mut Vec<Np>, contents: &mut Vec<Clause>) {
    let mut nps = Vec::new();
    restricted_walk(sentence, &mut nps, contents);
    out.extend(nps);
}

fn restricted_walk(sentence: &Sentence, out: &mut Vec<Np>, contents: &mut Vec<Clause>) {
    fn in_np(contents: &mut Vec<Clause>, np: &Np, out: &mut Vec<Np>) {
        if np.relative.is_some() {
            out.push(np.clone());
        }
        if let Some(of) = &np.of {
            in_np(contents, of, out);
        }
        np.of_also.iter().for_each(|n| in_np(contents, n, out));
        let mut relative = np.relative.as_deref();
        while let Some(r) = relative {
            match &r.body {
                RelativeBody::Content { clause } => {
                    if r.marker == RelMarker::That {
                        contents.push((**clause).clone());
                    }
                    in_clause(contents, clause, out)
                }
                RelativeBody::Copular { predicate, agent, roles, .. } => {
                    in_predicate(contents, predicate, out);
                    agent.iter().for_each(|g| in_group(contents, g, out));
                    roles.iter().for_each(|r| in_role(contents, r, out));
                }
                RelativeBody::Verbal { object, roles, .. } => {
                    object.iter().for_each(|g| in_group(contents, g, out));
                    roles.iter().for_each(|r| in_role(contents, r, out));
                }
                RelativeBody::ObjectGap { subject, roles, .. } => {
                    in_group(contents, subject, out);
                    roles.iter().for_each(|r| in_role(contents, r, out));
                }
            }
            relative = r.and.as_deref();
        }
    }
    fn in_group(contents: &mut Vec<Clause>, g: &NpGroup, out: &mut Vec<Np>) {
        match g {
            NpGroup::Single(n) => in_np(contents, n, out),
            NpGroup::Coordinated { items, .. } => items.iter().for_each(|n| in_np(contents, n, out)),
        }
    }
    fn in_predicate(contents: &mut Vec<Clause>, p: &Predicate, out: &mut Vec<Np>) {
        match p {
            Predicate::AbleTo { vp } => in_vp(contents, vp, out),
            Predicate::Pp { np, .. } => in_group(contents, np, out),
            _ => {}
        }
    }
    fn in_role(contents: &mut Vec<Clause>, r: &RolePp, out: &mut Vec<Np>) {
        match r {
            RolePp::Before(c) | RolePp::After(c) | RolePp::Until(c) => in_clause(contents, c, out),
            other => crate::reading::model::role_nps(other).into_iter().for_each(|n| in_np(contents, n, out)),
        }
    }
    fn in_clause(contents: &mut Vec<Clause>, c: &Clause, out: &mut Vec<Np>) {
        in_group(contents, &c.subject, out);
        match &c.body {
            ClauseBody::Copular { predicate, agent, roles, .. } => {
                in_predicate(contents, predicate, out);
                agent.iter().for_each(|g| in_group(contents, g, out));
                roles.iter().for_each(|r| in_role(contents, r, out));
            }
            ClauseBody::Verbal { object, roles, content, .. } => {
                object.iter().for_each(|g| in_group(contents, g, out));
                roles.iter().for_each(|r| in_role(contents, r, out));
                if let Some(c) = content {
                    contents.push((**c).clone());
                    in_clause(contents, c, out);
                }
            }
        }
    }
    fn in_vp(contents: &mut Vec<Clause>, v: &Vp, out: &mut Vec<Np>) {
        v.object.iter().for_each(|g| in_group(contents, g, out));
        v.roles.iter().for_each(|r| in_role(contents, r, out));
        v.complement.iter().for_each(|p| in_predicate(contents, p, out));
        if let Some(c) = &v.content {
            contents.push((**c).clone());
            in_clause(contents, c, out);
        }
    }
    fn in_core(contents: &mut Vec<Clause>, c: &Core, out: &mut Vec<Np>) {
        match c {
            Core::Definition { definiens, .. } => match definiens {
                Definiens::Np { np, roles } => {
                    // The clause of the genus is the difference of the definition; the noun phrases inside it are read as elsewhere.
                    let inner = |n: &Np, contents: &mut Vec<Clause>, out: &mut Vec<Np>| {
                        if let Some(of) = &n.of {
                            in_np(contents, of, out);
                        }
                        n.of_also.iter().for_each(|o| in_np(contents, o, out));
                    };
                    match np {
                        NpGroup::Single(n) => inner(n, contents, out),
                        NpGroup::Coordinated { items, .. } => items.iter().for_each(|n| inner(n, contents, out)),
                    }
                    roles.iter().for_each(|r| in_role(contents, r, out));
                }
                Definiens::Clause(_) => {}
            },
            Core::Description { subject, predicate, .. } => {
                in_group(contents, subject, out);
                in_predicate(contents, predicate, out);
            }
            Core::Deontic { subject, vp, .. } | Core::Relation { subject, vp } => {
                in_group(contents, subject, out);
                vp.items().iter().for_each(|v| in_vp(contents, v, out));
            }
            Core::Existence { subject } => in_group(contents, subject, out),
            Core::Conjoined { items } => items.iter().for_each(|c| in_core(contents, c, out)),
        }
    }
    let frames = &sentence.frames;
    for g in frames.scopes.iter().chain(&frames.states).map(|f| &f.clause).chain(frames.trigger.iter().map(|t| &t.clause)).chain(sentence.necessary.iter()).chain(sentence.iff.iter()) {
        g.items.iter().for_each(|c| in_clause(contents, c, out));
    }
    sentence.exception.iter().for_each(|c| in_clause(contents, c, out));
    in_core(contents, &sentence.core, out);
}

/// The reading of a restricted noun phrase: `a statement that shares no atom`
/// is a kind of `statement`, and each such statement shares no atom. A clause
/// that gets this reading is recorded as read.
fn restricted(np: &Np, origin: &SpecRef, lex: &Lexicon, all: &mut Vec<Stated>, read: &mut BTreeSet<String>) {
    // A variable or a pronoun is no class.
    if np.head.len() < 2 || np.head.chars().all(|c| c.is_ascii_uppercase() || c.is_ascii_digit()) {
        return;
    }
    let mut class = np.clone();
    crate::reading::model::general_class(&mut class);
    let mut head = class.clone();
    head.relative = None;
    let narrow = local(&np_key(&class, lex));
    let wide = local(&np_key(&head, lex));
    if narrow.is_empty() || wide.is_empty() || narrow == wide {
        return;
    }
    let holder = subject_key(&class, lex);
    let mut properties: Vec<Formula> = Vec::new();
    let mut clause = class.relative.as_deref();
    while let Some(relative) = clause {
        let one = Relative { marker: relative.marker, body: relative.body.clone(), and: None };
        let property = relative_property(&class, &holder, relative, lex);
        if let Some(formula) = property {
            // A comparison between quantities is read whole.
            if matches!(formula, Formula::Atom(Atom::Num { .. } | Atom::Lin { .. })) {
                read.insert(format!("={}", crate::reading::key::text(&crate::reading::key::relative_parts(&one, lex)).to_lowercase().replace([',', ';'], " ").split_whitespace().collect::<Vec<_>>().join(" ")));
            }
            properties.push(formula);
            // The key may cut the clause where a list is distributed: its opening words name it.
            let text = crate::reading::key::text(&crate::reading::key::relative_parts(&one, lex)).to_lowercase().replace([',', ';'], " ");
            read.insert(text.split_whitespace().take(3).collect::<Vec<_>>().join(" "));
        }
        clause = relative.and.as_deref();
    }
    if properties.is_empty() {
        return;
    }
    all.push(Stated { relation: Relation::Includes { narrow, wide, both_ways: false }, origin: origin.clone(), atom: None });
    for formula in properties {
        all.push(Stated { relation: Relation::Property { holder: holder.clone(), state: None, formula }, origin: origin.clone(), atom: None });
    }
}


/// The readings of the marks that stand inside the key of an action or an event.
///
/// - `apply only to that item` is the action on that item and on nothing
///   else: it excludes each other action of the subject that differs from it
///   only in what follows `only`.
/// - `have exactly 1 title` bounds the number of things that the action
///   reaches: the counted action implies the bound on one shared quantity.
/// - `identify the activation before formalization` is the action with an
///   order role: it implies the action without that role.
/// - `each`, `every`, `all`, `any`, `both` and `same` before an inner noun
///   say how many things the action reaches, not which action it is: the key
///   is equivalent to the key without the mark.
///
/// Each reading is taken from the parts of the key, which the nodes of the
/// sentence gave it; no word of a name is searched for.
fn key_readings(model: &mut Model, lex: &Lexicon) {
    use crate::reading::key::{text, Mark, Part};
    #[derive(Clone, Copy, PartialEq)]
    enum Kind {
        Act,
        Event,
    }
    let mut keys: BTreeMap<String, Kind> = BTreeMap::new();
    for c in &model.constraints {
        let mut visit = |a: &Atom, _: bool| match a {
            Atom::Act { key } | Atom::Forbid { key } | Atom::Discouraged { key } => {
                keys.insert(key.clone(), Kind::Act);
            }
            Atom::Event { key } => {
                keys.entry(key.clone()).or_insert(Kind::Event);
            }
            _ => {}
        };
        c.assume.atoms(true, &mut visit);
        c.guarantee.atoms(true, &mut visit);
    }
    let atom = |key: &str, kind: Kind| match kind {
        Kind::Act => Formula::atom(Atom::Act { key: key.to_string() }),
        Kind::Event => Formula::atom(Atom::Event { key: key.to_string() }),
    };
    // The subject of an action stands before its parts.
    let named = |subject: &str, parts: &[Part]| if subject.is_empty() { text(parts) } else { format!("{subject}|{}", text(parts)) };
    let structured: Vec<(&String, Kind, &str, &Vec<Part>)> = keys.iter().filter_map(|(key, kind)| {
        let parts = model.keys.get(key)?;
        let subject = match kind {
            Kind::Act => key.split_once('|').map_or("", |(subject, _)| subject),
            Kind::Event => "",
        };
        Some((key, *kind, subject, parts))
    }).collect();
    let mut axioms: Vec<Formula> = Vec::new();
    // The exclusive focus: the subject, what stands before the focus, the focus.
    let mut exclusive: Vec<(&String, &str, String, String)> = Vec::new();
    for (key, kind, subject, parts) in &structured {
        if *kind != Kind::Act {
            continue;
        }
        let Some(at) = parts.iter().position(|p| p.mark() == Some(Mark::Focus)) else { continue };
        let (mut before, mut after) = (text(&parts[..at]), text(&parts[at + 1..]));
        // `accept sentences only` beside `accept sentences only in the
        // grammar` is that action without its roles: the focus is the role.
        if after.is_empty() && keys.keys().any(|other| other.starts_with(&format!("{key} "))) {
            continue;
        }
        // `start only`: the focus is what precedes.
        if after.is_empty() {
            let Some(verb) = parts.first() else { continue };
            after = text(&parts[1..at]);
            before = verb.text().to_string();
        }
        exclusive.push((key, subject, before, after));
    }
    for (key, subject, before, focus) in &exclusive {
        let allowed: Vec<&String> = exclusive.iter().filter(|(_, s, b, _)| s == subject && b == before).map(|(_, _, _, f)| f).collect();
        let plain = format!("{subject}|{before} {focus}");
        if keys.get(&plain) == Some(&Kind::Act) {
            axioms.push(Formula::implies(act(key), act(&plain)));
        }
        let stem = format!("{subject}|{before} ");
        for (other, kind) in &keys {
            if *kind != Kind::Act || other == *key || !other.starts_with(&stem) {
                continue;
            }
            let rest = &other[stem.len()..];
            // The action without its roles names the same action.
            if rest == "only" {
                continue;
            }
            let rest = rest.strip_prefix("only ").unwrap_or(rest);
            let related = allowed.iter().any(|f| rest == f.as_str() || rest.starts_with(&format!("{f} ")) || f.starts_with(&format!("{rest} ")));
            if !related {
                // An action that completes at some moment was performed; the
                // exclusive action and the other one are not both performed.
                let done = |key: &str| Formula::atom(Atom::Config { key: format!("performed {key}") });
                axioms.push(Formula::implies(act(key), done(key)));
                axioms.push(Formula::implies(act(other), done(other)));
                axioms.push(Formula::not(Formula::And(vec![done(key), done(other)])));
            }
        }
    }
    for (key, kind, subject, parts) in &structured {
        // A counted object.
        if let Some(at) = parts.iter().position(|p| p.count().is_some()) {
            let (cmp, n) = parts[at].count().unwrap_or((trion_solver::Cmp::Ge, 0));
            let end = at + parts[at..].iter().take_while(|p| p.mark() == Some(Mark::Count)).count();
            // Nothing is counted where no noun follows, and `at least 0` bounds nothing.
            let vacuous = cmp == trion_solver::Cmp::Ge && n == 0;
            // `at most 1 step for each step name` bounds no total.
            let per_thing = parts[end..].iter().any(|p| p.mark() == Some(Mark::General));
            if end < parts.len() && !vacuous && !per_thing && !(at > 0 && parts[at - 1].text() == "be") {
                // `1 title` and `2 titles` count the same things.
                let shared: Vec<String> = parts[..at].iter().chain(&parts[end..]).flat_map(|p| p.text().split(' ')).map(fold).collect();
                let attr = if subject.is_empty() { format!("{} count", shared.join(" ")) } else { format!("{subject}|{} count", shared.join(" ")) };
                let bound = Formula::atom(Atom::Num { attr, unit: "count".to_string(), cmp, n: n * trion_solver::NUMERIC_SCALE });
                axioms.push(Formula::implies(atom(key, *kind), bound));
            }
        }
        // An order role.
        if let Some(at) = parts.iter().position(|p| p.mark() == Some(Mark::Order)) {
            if at > 0 && at + 1 < parts.len() {
                let plain = named(subject, &parts[..at]);
                if keys.get(&plain) == Some(kind) {
                    axioms.push(Formula::implies(atom(key, *kind), atom(&plain, *kind)));
                }
            }
        }
        // `the first statement` is a statement: an action on a kind that a
        // declared term names is an action on the noun.
        for (at, part) in parts.iter().enumerate() {
            if part.names_kind() && at + 1 < parts.len() {
                let mut plain_parts = (*parts).clone();
                plain_parts.remove(at);
                axioms.push(Formula::implies(atom(key, *kind), atom(&named(subject, &plain_parts), *kind)));
            }
        }
        // A determiner of an inner noun phrase.
        for (at, part) in parts.iter().enumerate() {
            if part.mark() != Some(Mark::General) || at + 1 >= parts.len() {
                continue;
            }
            let mut plain_parts = (*parts).clone();
            plain_parts.remove(at);
            let plain = named(subject, &plain_parts);
            if keys.get(&plain) == Some(kind) {
                axioms.push(Formula::implies(atom(key, *kind), atom(&plain, *kind)));
                axioms.push(Formula::implies(atom(&plain, *kind), atom(key, *kind)));
            }
        }
    }
    // `respond within the configured timeout`: where a statement bounds the
    // configured timeout in units of time, the role is a deadline whose bound
    // is that quantity. Where no statement does, the phrase names a place.
    let mut times: BTreeSet<String> = BTreeSet::new();
    for c in &model.constraints {
        let mut visit = |a: &Atom, _: bool| match a {
            Atom::Num { attr, unit, .. } if unit == "ms" && !attr.contains('|') => {
                times.insert(attr.clone());
            }
            Atom::Lin { terms, unit, .. } if unit == "ms" => times.extend(terms.iter().map(|(name, _)| name.clone()).filter(|name| !name.contains('|'))),
            _ => {}
        };
        c.assume.atoms(true, &mut visit);
        c.guarantee.atoms(true, &mut visit);
    }
    let mut undecided: Vec<(String, String)> = Vec::new();
    for (key, kind, subject, parts) in &structured {
        if *kind != Kind::Act {
            continue;
        }
        let Some(at) = parts.iter().position(|p| p.mark() == Some(Mark::Role) && p.text() == "within") else { continue };
        let name = text(&parts[at + 1..]);
        let Some(quantity) = times.iter().find(|attr| attr.rsplit("::").next().is_some_and(|local| folded(local) == folded(&name))) else {
            // `within the namespace` names a place where the namespace is a
            // declared term. A phrase that is neither a bounded quantity of
            // time nor a declared term says neither when nor where.
            let head: Vec<String> = parts[at + 1..].iter().skip_while(|p| !p.is_name()).take_while(|p| p.is_name()).flat_map(|p| p.text().split_whitespace().map(str::to_string).collect::<Vec<_>>()).collect();
            let declared = (0..head.len()).any(|from| lex.declares(&head[from..]));
            if !declared {
                undecided.push(((*key).clone(), name));
            }
            continue;
        };
        let plain = named(subject, &parts[..at]);
        axioms.push(Formula::implies(atom(key, *kind), Formula::atom(Atom::difference(&format!("{plain} elapsed"), quantity, "ms", trion_solver::Cmp::Le, 0))));
    }
    drop(structured);
    for (key, name) in undecided {
        let origin = model.constraints.iter().find(|c| {
            let mut found = false;
            let mut visit = |a: &Atom, _: bool| found |= matches!(a, Atom::Act { key: k } | Atom::Forbid { key: k } | Atom::Discouraged { key: k } if *k == key);
            c.assume.atoms(true, &mut visit);
            c.guarantee.atoms(true, &mut visit);
            found
        }).and_then(|c| c.refs.first().cloned());
        if let Some(origin) = origin {
            model.unread.push((origin, crate::reading::key::Unread { part: format!("within {name}"), kind: "a role", place: "with a phrase that is neither a quantity of time nor a declared term: bound the quantity, as in `The configured timeout is at most 3 seconds.`, or declare the place as a term", phrase: name }));
        }
    }
    if !axioms.is_empty() {
        model.background.extend(axioms);
    }
}

/// Adds the axioms of the vocabulary to a compiled model.
pub(super) fn apply(set: &SpecSet, lex: &Lexicon, model: &mut Model) {
    key_readings(model, lex);
    let mut all: Vec<Stated> = Vec::new();
    let mut refinements: Vec<(SpecRef, Vec<String>)> = Vec::new();
    for pkg in &set.packages {
        for doc in &pkg.documents {
            let scoped = lex.in_document(doc);
            for spec in &doc.specs {
                let display = if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) };
                let origin = SpecRef { id: display, file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
                let (found, sink) = crate::reading::key::collect(|| stated(spec, &origin, &scoped));
                model.absorb(&origin, sink);
                all.extend(found);
                if !spec.details.is_empty() {
                    refinements.push((origin, spec.details.clone()));
                }
            }
        }
    }
    // A modified phrase names a kind of its head: `Each cited statement is a
    // statement.` needs no statement of its own once `statement` has a meaning.
    let heads = grounded_heads(set, lex);
    // What follows is found in other statements: it is no part of what the
    // statement of its origin says alone.
    let first_derived = all.len();
    if !heads.is_empty() {
        let names: BTreeSet<Vec<String>> = heads.keys().cloned().collect();
        let mut phrases: BTreeSet<Vec<String>> = BTreeSet::new();
        for doc in set.packages.iter().flat_map(|p| &p.documents) {
            let scoped = lex.in_document(doc);
            for spec in doc.specs.iter().filter(|s| !matches!(s.sentence.core, Core::Definition { .. })) {
                phrases.extend(crate::reading::vocabulary::occurrences(&spec.sentence, &scoped).into_iter().filter(|(_, kind)| *kind != "action" && *kind != "value").map(|(term, _)| local(&term)).filter(|words| words.len() > 1));
            }
        }
        let stated_pairs: BTreeSet<(Vec<String>, Vec<String>)> = all.iter().filter_map(|s| match &s.relation {
            Relation::Includes { narrow, wide, .. } => Some((narrow.iter().map(|w| fold(w)).collect(), wide.iter().map(|w| fold(w)).collect())),
            _ => None,
        }).collect();
        for phrase in phrases {
            // A phrase that is itself defined says what it is.
            if names.contains(&phrase.iter().map(|w| fold(w)).collect::<Vec<_>>()) {
                continue;
            }
            let Some(head) = head_of(&phrase, &names) else { continue };
            if stated_pairs.contains(&(phrase.iter().map(|w| fold(w)).collect(), head.clone())) {
                continue;
            }
            all.push(Stated { relation: Relation::Includes { narrow: phrase, wide: head.clone(), both_ways: false }, origin: heads[head].clone(), atom: None });
        }
    }
    // An object that a response introduces is one thing of its type: what
    // holds of every such thing holds of it, and nothing identifies it with
    // the object of another binding.
    let mut bound: BTreeMap<Vec<String>, SpecRef> = BTreeMap::new();
    for pkg in &set.packages {
        for doc in &pkg.documents {
            let scoped = lex.in_document(doc);
            for spec in doc.specs.iter().filter(|s| s.sentence.source.chars().any(|c| c.is_ascii_uppercase())) {
                for (term, _) in crate::reading::vocabulary::occurrences(&spec.sentence, &scoped) {
                    let words = local(&term);
                    if words.len() > 1 && words[0].starts_with(crate::document::BINDING_MARK) {
                        let display = if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) };
                        bound.entry(words).or_insert(SpecRef { id: display, file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() });
                    }
                }
            }
        }
    }
    for (phrase, origin) in bound {
        let wide = phrase[1..].to_vec();
        all.push(Stated { relation: Relation::Includes { narrow: phrase, wide, both_ways: false }, origin, atom: None });
    }
    let derived: BTreeSet<usize> = (first_derived..all.len()).collect();
    // A noun phrase with a restrictive relative clause names a restricted
    // class: each of its members is a member of the head, and the clause is
    // what holds of each member.
    let mut propositions: Vec<(String, Formula, Option<String>)> = Vec::new();
    for pkg in &set.packages {
        for doc in &pkg.documents {
            let scoped = lex.in_document(doc);
            for spec in doc.specs.iter().filter(|s| !matches!(s.sentence.core, Core::Definition { .. })) {
                let mut found = Vec::new();
                let mut contents = Vec::new();
                restricted_and_contents(&spec.sentence, &mut found, &mut contents);
                // A content clause is a proposition that the action or the noun
                // is about: it is parsed as a clause, and its atoms are those
                // of the same clause elsewhere.
                for clause in &contents {
                    let content = crate::reading::key::text(&crate::reading::key::content_parts(clause, &scoped));
                    let text = content.to_lowercase().replace([',', ';'], " ");
                    model.read_clauses.insert(text.split_whitespace().take(3).collect::<Vec<_>>().join(" "));
                    // The actor of the clause, where the clause has one: `the gate` of `the gate opens`.
                    let actor = match &clause.subject {
                        NpGroup::Single(np) if matches!(clause.body, ClauseBody::Verbal { negation: None, .. }) => Some(crate::reading::model::subject_key(np, &scoped)),
                        _ => None,
                    };
                    propositions.push((content, crate::reading::model::clause_formula(clause, &scoped), actor));
                }
                if found.is_empty() {
                    continue;
                }
                let display = if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) };
                let origin = SpecRef { id: display, file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
                for np in found {
                    restricted(&np, &origin, &scoped, &mut all, &mut model.read_clauses);
                }
            }
        }
    }
    // `ensure that the token is valid`: an action that makes a proposition
    // hold implies the proposition. The content of any other verb is the
    // proposition that the action is about: the action is named by its verb
    // and that proposition, and two actions about one proposition are one.
    if !propositions.is_empty() {
        let mut keys: BTreeSet<String> = BTreeSet::new();
        for c in &model.constraints {
            let mut visit = |a: &Atom, _: bool| {
                if let Atom::Act { key } | Atom::Forbid { key } | Atom::Discouraged { key } = a {
                    keys.insert(key.clone());
                }
            };
            c.assume.atoms(true, &mut visit);
            c.guarantee.atoms(true, &mut visit);
        }
        for key in keys.iter().cloned() {
            let action = key.split_once('|').map_or(key.as_str(), |(_, action)| action);
            let verb = crate::reading::model::base_verb(action.split_whitespace().next().unwrap_or_default());
            use crate::syntax::words::ContentClass;
            let Some(class) = crate::syntax::words::content_class(&verb).filter(|class| *class != ContentClass::Reporting) else { continue };
            for (text, formula, actor) in &propositions {
                if !action.ends_with(text.as_str()) {
                    continue;
                }
                // The action that the clause names, where the clause is an action.
                let inner = match formula {
                    // The action of the actor has the words of the event after the actor.
                    Formula::Atom(Atom::Event { key: event }) => actor.as_ref().and_then(|actor| event.strip_prefix(&format!("{actor} ")).map(|rest| format!("{actor}|{rest}"))),
                    _ => None,
                };
                let forbidden = |k: &str| Formula::atom(Atom::Forbid { key: k.to_string() });
                match (class, inner) {
                    (ContentClass::Establishing, _) | (ContentClass::Requiring, None) => model.background.push(Formula::implies(act(&key), formula.clone())),
                    // `require the gate to close`: the gate closes, and nothing forbids it.
                    (ContentClass::Requiring, Some(inner)) => model.background.push(Formula::implies(act(&key), Formula::And(vec![formula.clone(), Formula::not(forbidden(&inner))]))),
                    // `allow the gate to open`: nothing forbids the gate to open; what is forbidden to allow is forbidden.
                    (ContentClass::Permitting, Some(inner)) => {
                        model.background.push(Formula::implies(act(&key), Formula::not(forbidden(&inner))));
                        model.background.push(Formula::implies(forbidden(&key), forbidden(&inner)));
                    }
                    (ContentClass::Permitting, None) | (ContentClass::Reporting, _) => {}
                }
            }
        }
    }
    if all.is_empty() && refinements.is_empty() {
        return;
    }
    let atoms = atoms_of(model);
    let inclusions: Vec<(&Vec<String>, &Vec<String>, &Stated)> = all
        .iter()
        .flat_map(|s| match &s.relation {
            Relation::Includes { narrow, wide, both_ways } => {
                let mut pairs = vec![(narrow, wide, s)];
                if *both_ways {
                    pairs.push((wide, narrow, s));
                }
                pairs
            }
            _ => Vec::new(),
        })
        .collect();
    // An attribute may hold a value and the wider value at one moment.
    let compatible: Vec<(String, String)> = inclusions.iter().map(|(n, w, _)| (folded(&n.join(" ")), folded(&w.join(" ")))).collect();
    model.background.retain(|axiom| {
        let Formula::Not(inner) = axiom else { return true };
        let Formula::And(pair) = &**inner else { return true };
        let [Formula::Atom(Atom::Val { value: a, .. }), Formula::Atom(Atom::Val { value: b, .. })] = pair.as_slice() else { return true };
        let (a, b) = (folded(a), folded(b));
        !compatible.iter().any(|(n, w)| (*n == a && *w == b) || (*n == b && *w == a))
    });

    // What a statement says alone is its local reading: its axioms over its
    // own atoms. What it says about the atoms of other statements is carried
    // to them, and is a relation between the entries.
    let closed_domains = model.closed_domains.clone();
    let derive = |s: &Stated, atoms: &Atoms, chains: bool| -> Vec<Formula> {
        let mut axioms = Vec::new();
        match &s.relation {
            Relation::Includes { narrow, wide, both_ways } => {
                carry(narrow, wide, &atoms, &mut axioms);
                if *both_ways {
                    carry(wide, narrow, &atoms, &mut axioms);
                }
                // The statement of the inclusion, and the chains through the others.
                if let Some(atom) = &s.atom {
                    axioms.push(Formula::atom(atom.clone()));
                    if let Atom::Dom { attr, .. } = atom {
                        for (from, to, other) in inclusions.iter().filter(|(from, _, other)| chains && *from == wide && !std::ptr::eq(*other, s)) {
                            let _ = from;
                            if let Some(next) = &other.atom {
                                let reached = Atom::Dom { attr: attr.clone(), value: to.join(" ") };
                                axioms.push(Formula::implies(Formula::And(vec![Formula::atom(atom.clone()), Formula::atom(next.clone())]), Formula::atom(reached)));
                            }
                        }
                    }
                }
            }
            Relation::Excludes { first, second } => {
                let (a, b) = (first.join(" "), second.join(" "));
                for (attr, values) in &atoms.values {
                    let find = |name: &str| values.iter().find(|v| folded(v) == folded(name));
                    if let (Some(x), Some(y)) = (find(&a), find(&b)) {
                        let dom = |value: &String| Formula::atom(Atom::Dom { attr: attr.clone(), value: value.clone() });
                        let val = |value: &String| Formula::atom(Atom::Val { attr: attr.clone(), value: value.clone() });
                        // An enumeration lists the values that an attribute may take;
                        // that both are listed is no claim that one thing is both.
                        let listed = closed_domains.get(attr).is_some_and(|domain| domain.contains(x) && domain.contains(y));
                        if !listed {
                            axioms.push(Formula::not(Formula::And(vec![dom(x), dom(y)])));
                        }
                        axioms.push(Formula::not(Formula::And(vec![val(x), val(y)])));
                    }
                }
                // Nothing that is the one is the other, whichever way it is said.
                for (attr, values) in &atoms.values {
                    let names = local(attr);
                    for (own, other) in [(first, &b), (second, &a)] {
                        if names.iter().map(|w| fold(w)).eq(own.iter().map(|w| fold(w))) {
                            for value in values.iter().filter(|v| folded(v) == folded(other) || folded(v) == folded(&format!("a {other}")) || folded(v) == folded(&format!("an {other}"))) {
                                axioms.push(Formula::not(Formula::atom(Atom::Dom { attr: attr.clone(), value: value.clone() })));
                            }
                        }
                    }
                }
            }
            Relation::ExclusiveActions { first, second, object } => {
                let done = |key: &str| Formula::atom(Atom::Config { key: format!("performed {key}") });
                for written in atoms.acts.values().flatten() {
                    let Some((subject, rest)) = written.split_once('|') else { continue };
                    let mut words = rest.split_whitespace();
                    if words.next().map(base_verb).as_deref() != Some(first.as_str()) {
                        continue;
                    }
                    let tail: Vec<String> = words.map(str::to_string).collect();
                    if substitute(&tail.join(" "), object, object).is_none() {
                        continue;
                    }
                    let twin = format!("{subject}|{second} {}", tail.join(" "));
                    for other in atoms.acts.get(&folded(&twin)).into_iter().flatten() {
                        // An action that completes at some moment was performed.
                        axioms.push(Formula::implies(act(written), done(written)));
                        axioms.push(Formula::implies(act(other), done(other)));
                        axioms.push(Formula::not(Formula::And(vec![done(written), done(other)])));
                    }
                }
            }
            Relation::Property { holder, state, formula } => match state {
                Some(value) => {
                    // Alone, the definition speaks of the state as it names it;
                    // in the package, of every spelling that names that state.
                    let named: BTreeSet<String> = std::iter::once(value.clone()).collect();
                    let values = if chains { atoms.values.get(holder) } else { Some(&named) };
                    for value in values.into_iter().flatten().filter(|v| folded(v) == folded(value)) {
                        let (attr, value) = (holder.clone(), value.clone());
                        axioms.push(Formula::implies(Formula::atom(Atom::Val { attr: attr.clone(), value: value.clone() }), formula.clone()));
                        axioms.push(Formula::implies(Formula::atom(Atom::Dom { attr, value }), formula.clone()));
                    }
                }
                None => axioms.push(formula.clone()),
            },
            Relation::Converse { holder, state, formula } => {
                let named: BTreeSet<String> = std::iter::once(state.clone()).collect();
                let values = if chains { atoms.values.get(holder) } else { Some(&named) };
                for value in values.into_iter().flatten().filter(|v| folded(v) == folded(state)) {
                    axioms.push(Formula::implies(formula.clone(), Formula::atom(Atom::Val { attr: holder.clone(), value: value.clone() })));
                }
            }
        }
        axioms.dedup();
        axioms
    };
    let owner_of_constraint = |c: &Constraint| c.refs.first().map(|r| r.id.clone());
    let mut own: BTreeMap<String, Atoms> = BTreeMap::new();
    let mut owners: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut places: BTreeMap<String, SpecRef> = BTreeMap::new();
    for c in &model.constraints {
        let Some(at) = c.refs.first() else { continue };
        places.entry(at.id.clone()).or_insert_with(|| at.clone());
        let mut visit = |a: &Atom, _: bool| {
            owners.entry(owned(a)).or_default().insert(at.id.clone());
        };
        c.assume.atoms(true, &mut visit);
        c.guarantee.atoms(true, &mut visit);
    }
    // The atom of a stated inclusion is held by the statement of the inclusion.
    for s in &all {
        places.entry(s.origin.id.clone()).or_insert_with(|| s.origin.clone());
        if let Some(atom) = &s.atom {
            owners.entry(owned(atom)).or_default().insert(s.origin.id.clone());
        }
    }
    let mut groups: Vec<(SpecRef, Vec<Formula>)> = Vec::new();
    let mut carried: Vec<(SpecRef, Vec<Formula>)> = Vec::new();
    for (position, s) in all.iter().enumerate() {
        let full = derive(s, &atoms, true);
        let local = if derived.contains(&position) {
            Vec::new()
        } else {
            let alone = own.entry(s.origin.id.clone()).or_insert_with(|| atoms_of_constraints(model.constraints.iter().filter(|c| owner_of_constraint(c).as_deref() == Some(s.origin.id.as_str()))));
            derive(s, alone, false)
        };
        let rest: Vec<Formula> = full.into_iter().filter(|f| !local.contains(f)).collect();
        for (list, axioms) in [(&mut groups, local), (&mut carried, rest)] {
            if !axioms.is_empty() {
                match list.iter_mut().find(|(origin, _)| *origin == s.origin) {
                    Some((_, known)) => known.extend(axioms),
                    None => list.push((s.origin.clone(), axioms)),
                }
            }
        }
    }
    for (origin, axioms) in &carried {
        let mut rests_on: BTreeSet<String> = BTreeSet::new();
        for axiom in axioms {
            axiom.atoms(true, &mut |a: &Atom, _: bool| {
                if let Some(ids) = owners.get(&owned(a)) {
                    rests_on.extend(ids.iter().filter(|id| **id != origin.id).cloned());
                }
            });
        }
        let rests_on: Vec<SpecRef> = rests_on.iter().filter_map(|id| places.get(id).cloned()).collect();
        match model.applied.iter_mut().find(|a| a.kind == "applied" && a.subject.id == origin.id) {
            Some(known) => {
                for r in rests_on {
                    if !known.rests_on.iter().any(|k| k.id == r.id) {
                        known.rests_on.push(r);
                    }
                }
                known.rests_on.sort_by(|a, b| a.id.cmp(&b.id));
            }
            None => model.applied.push(crate::reading::model::Applied { kind: "applied".to_string(), subject: origin.clone(), rests_on }),
        }
    }
    // A statement holds exactly when the statements that detail it hold.
    let mut refined: Vec<(SpecRef, Formula)> = Vec::new();
    for (origin, details) in refinements {
        let contract = |id: &str| -> Vec<Formula> { model.constraints.iter().filter(|c| matches!(c.kind, ConstraintKind::Spec | ConstraintKind::Permission) && c.refs.first().is_some_and(|r| r.id == id || r.id.starts_with(&format!("{id}/")))).map(Constraint::formula).collect() };
        let own = contract(&origin.id);
        let parts: Vec<Formula> = details.iter().filter(|id| **id != origin.id).flat_map(|id| contract(id)).collect();
        if own.is_empty() || parts.is_empty() {
            continue;
        }
        for detail in details.iter().filter(|id| **id != origin.id) {
            let abstracts = model.refined.entry(detail.clone()).or_default();
            if !abstracts.contains(&origin) {
                abstracts.push(origin.clone());
            }
        }
        let (own, parts) = (Formula::And(own), Formula::And(parts));
        refined.push((origin, Formula::And(vec![Formula::implies(own.clone(), parts.clone()), Formula::implies(parts, own)])));
    }
    for (origin, guarantee) in refined {
        model.constraints.push(Constraint { kind: ConstraintKind::Refinement, assume: Formula::True, guarantee, refs: vec![origin] });
    }
    for (kind, list) in [(ConstraintKind::Axiom, groups), (ConstraintKind::Carried, carried)] {
        for (origin, mut axioms) in list {
            axioms.dedup();
            let guarantee = if axioms.len() == 1 { axioms.remove(0) } else { Formula::And(axioms) };
            model.constraints.push(Constraint { kind, assume: Formula::True, guarantee, refs: vec![origin] });
        }
    }
}

/// Reports a refinement that names no statement, itself, or a cycle.
pub fn check(set: &SpecSet) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let specs: Vec<&Spec> = set.packages.iter().filter(|p| p.is_root).flat_map(|p| &p.documents).flat_map(|d| &d.specs).collect();
    let known: BTreeSet<String> = specs.iter().flat_map(|s| s.id.iter().cloned().chain(s.parts.iter().cloned())).collect();
    let details: BTreeMap<String, &Spec> = specs.iter().filter(|s| !s.details.is_empty()).map(|s| (s.display_id(), *s)).collect();
    for (id, spec) in &details {
        let at = SpecRef { id: id.clone(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
        for detail in &spec.details {
            if detail == id {
                out.push(Diagnostic::error("CYCLIC_REFINEMENT", format!("the statement `{id}` cannot detail itself"), vec![at.clone()]));
            } else if !known.contains(detail) && !known.iter().any(|id| id.starts_with(&format!("{detail}/"))) {
                out.push(Diagnostic::error("UNRESOLVED_REFERENCE", format!("`detailed by [{detail}]` names no statement of this package"), vec![at.clone()]));
            }
        }
        // A statement that is detailed by its own abstraction has no meaning of its own.
        let mut seen = BTreeSet::new();
        let mut stack: Vec<&String> = spec.details.iter().filter(|detail| *detail != id).collect();
        while let Some(next) = stack.pop() {
            if next == id {
                out.push(Diagnostic::error("CYCLIC_REFINEMENT", format!("the statement `{id}` is detailed by a statement that it details"), vec![at.clone()]));
                break;
            }
            if seen.insert(next.clone()) {
                stack.extend(details.get(next).into_iter().flat_map(|s| &s.details));
            }
        }
    }
    out
}
