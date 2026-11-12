//! Individuals of a type, and the relations between them.
//!
//! The contracts speak about one representative of each type. This layer
//! reads the statements that relate individuals over a bounded domain: each
//! carrier holds `scope` individuals, a type is a property of an individual
//! and a relation holds between two individuals. A result that rests on this
//! layer holds for domains of that size.
//!
//! - `Each room has exactly one owner.` counts the owners of each room.
//! - `The owner of each room is a member of the room.` and `The owner of a
//!   room is one of its members.` include one relation in another.
//! - `No two rooms have the same name.` gives two rooms different names.
//! - `Some accepted sentence denotes no expression.` speaks about one
//!   individual, not about all of them.
//! - `There is a room.` and `There are at least two rooms.` populate a type.
//! - `The number of members of each room is at most 1.` counts.
//! - `The total size of all attachments is at most 10 MB.` adds the sizes of
//!   the attachments that exist.
//! - `Each guest is a user.` makes each guest a user, individual by individual.
//! - `The formal interpretation of a statement means the expression that the
//!   statement denotes.` makes two relations one.
//! - A condition `a construct has no interpretation` occurs only when some
//!   construct has none.

use crate::document::SpecSet;
use crate::diagnostic::SpecRef;
use crate::reading::model::{base_verb, comparison_bound, subject_key, Constraint, ConstraintKind, Model};
use crate::reading::lexicon::Lexicon;
use trion_solver::{Atom, Cmp, Formula};
use crate::syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};

/// The number of individuals of each carrier, when no bound is given.
pub const DEFAULT_SCOPE: usize = 3;
/// A counted bound above this is left to the representative reading.
const LARGEST_COUNT: u32 = 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Quantifier {
    All,
    Some,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Count {
    AtLeast(u32),
    AtMost(u32),
    Exactly(u32),
}

#[derive(Debug, Clone)]
enum Form {
    /// `<Each|Some> T <relation> <count> U`
    Related { quantifier: Quantifier, kind: String, relation: String, target: String, count: Count },
    /// `The R1 of each T is a R2 of the T`; `never` denies it.
    Included { narrow: String, wide: String, owner: String, denied: bool },
    /// `No two Ts have the same U.`
    Distinct { relation: String, target: String, kind: String },
    /// `There is a T.`
    Populated { kind: String, count: Count },
    /// `The number of Rs of each T <cmp> n`
    Counted { kind: String, relation: String, target: String, count: Count },
    /// `Each A is a B.`; `No A is a B.`
    Kind { narrow: String, wide: String, both: bool, denied: bool },
    /// `The R1 of a T means the U that the T <verb>s.`
    Same { first: String, first_target: String, second: String, second_target: String, owner: String },
    /// `A T means a G that <verb>s <count> U.`: each G with that count is a T.
    Defined { narrow: String, wide: String, relation: String, target: String, count: Count },
    /// `The total Q of all Ts <cmp> v`
    Total { kind: String, total: String, part: String },
    /// `The Q of each T <cmp> v`
    Part { kind: String, part: String, comparison: Comparison },
    /// A condition `a T has [no] U` with the atom of its event.
    Condition { event: Formula, kind: String, relation: String, target: String, denied: bool },
}

struct Stated {
    form: Form,
    origin: SpecRef,
}

fn plain(np: &Np) -> bool {
    np.of.is_none() && np.relative.is_none()
}

/// A word of a name is an open-class word. A closed-class word before a noun
/// was read by the form that holds it, as are `same` (one thing shared) and
/// `total` (a sum), which the forms of this layer read.
fn names(word: &str) -> bool {
    matches!(crate::syntax::words::classify(word), crate::syntax::words::WordClass::Open) && !word.eq_ignore_ascii_case("total") && !word.eq_ignore_ascii_case("same")
}

/// The key of the type or relation that a noun phrase names, in the singular.
fn noun(np: &Np, lex: &Lexicon) -> String {
    let mut words: Vec<String> = np.modifiers.iter().filter(|w| names(w)).map(|w| w.to_lowercase()).collect();
    words.push(base_verb(&np.head.to_lowercase()));
    lex.resolve(&lex.canon(&words.join(" ")))
}

fn noun_of_words(words: &[String], lex: &Lexicon) -> String {
    let mut words: Vec<String> = words.iter().filter(|w| names(w)).map(|w| w.to_lowercase()).collect();
    if let Some(last) = words.last_mut() {
        *last = base_verb(last);
    }
    lex.resolve(&lex.canon(&words.join(" ")))
}

fn count_of(det: &Option<Det>) -> Option<Count> {
    let within = |n: u64| u32::try_from(n).ok().filter(|n| *n <= LARGEST_COUNT);
    match det {
        Some(Det::A | Det::An | Det::OneOrMore) => Some(Count::AtLeast(1)),
        Some(Det::No) => Some(Count::Exactly(0)),
        Some(Det::Exactly { n }) => within(*n).map(Count::Exactly),
        Some(Det::AtLeast { n } | Det::Cardinal { n, .. }) => within(*n).map(Count::AtLeast),
        Some(Det::AtMost { n }) => within(*n).map(Count::AtMost),
        _ => None,
    }
}

fn count_of_comparison(c: &Comparison) -> Option<Count> {
    let Measure::Quantity { number, unit: None } = &c.value else { return None };
    let n: u32 = number.parse().ok().filter(|n| *n <= LARGEST_COUNT)?;
    match c.op {
        ComparisonOp::AtLeast => Some(Count::AtLeast(n)),
        ComparisonOp::AtMost => Some(Count::AtMost(n)),
        ComparisonOp::EqualTo => Some(Count::Exactly(n)),
        ComparisonOp::GreaterThan => (n < LARGEST_COUNT).then_some(Count::AtLeast(n + 1)),
        ComparisonOp::LessThan => n.checked_sub(1).map(Count::AtMost),
        ComparisonOp::Between => None,
    }
}

/// The name of the relation that a verb and its object name: `has an owner`
/// is the relation `owner`; `denotes an expression` is `denote expression`.
fn relation(verb: &str, target: &str) -> String {
    let base = base_verb(&verb.to_lowercase());
    if base == "have" {
        target.to_string()
    } else {
        format!("{base} {target}")
    }
}

fn quantifier(det: &Option<Det>) -> Option<Quantifier> {
    match det {
        Some(Det::Each | Det::Every | Det::All | Det::Any) => Some(Quantifier::All),
        Some(Det::Some) => Some(Quantifier::Some),
        _ => None,
    }
}

fn generic(det: &Option<Det>) -> bool {
    matches!(det, Some(Det::Each | Det::Every | Det::A | Det::An | Det::The | Det::Any))
}

/// `a member of the room`, `one of its members`, `one of the members of the room`.
fn member_phrase(predicate: &Predicate, lex: &Lexicon) -> Option<String> {
    let lower = |w: &String| w.to_lowercase();
    match predicate {
        Predicate::Words { words } => {
            let words: Vec<String> = words.iter().map(lower).collect();
            let rest = match words.first().map(String::as_str) {
                Some("a" | "an") => &words[1..],
                _ => return None,
            };
            let of = rest.iter().position(|w| w == "of")?;
            (of > 0).then(|| noun_of_words(&rest[..of], lex))
        }
        Predicate::Enumeration { one_of: true, values, .. } if values.len() == 1 => {
            let words: Vec<String> = values[0].split_whitespace().map(str::to_lowercase).collect();
            let rest = match words.first().map(String::as_str) {
                Some("its" | "their" | "the") => &words[1..],
                _ => return None,
            };
            let end = rest.iter().position(|w| w == "of").unwrap_or(rest.len());
            (end > 0).then(|| noun_of_words(&rest[..end], lex))
        }
        _ => None,
    }
}

/// `a user`, `a kind of user`: the wider type of an inclusion.
fn kind_phrase(predicate: &Predicate, lex: &Lexicon) -> Option<String> {
    let Predicate::Words { words } = predicate else { return None };
    let words: Vec<String> = words.iter().map(|w| w.to_lowercase()).collect();
    let rest = match words.first().map(String::as_str) {
        Some("a" | "an") => &words[1..],
        _ => return None,
    };
    let rest = if rest.len() > 2 && rest[0] == "kind" && rest[1] == "of" { &rest[2..] } else { rest };
    let simple = !rest.is_empty() && rest.iter().all(|w| w.chars().all(|c| c.is_alphanumeric() || c == '-') && matches!(crate::syntax::words::classify(w), crate::syntax::words::WordClass::Open));
    simple.then(|| noun_of_words(rest, lex))
}

fn related(subject: &Np, item: &Vp, lex: &Lexicon) -> Option<Form> {
    let quantifier = quantifier(&subject.det)?;
    if !plain(subject) || !item.roles.is_empty() || item.complement.is_some() || item.content.is_some() {
        return None;
    }
    let Some(NpGroup::Single(object)) = &item.object else { return None };
    if !plain(object) {
        return None;
    }
    let count = count_of(&object.det)?;
    let target = noun(object, lex);
    Some(Form::Related { quantifier, kind: noun(subject, lex), relation: relation(&item.verb, &target), target, count })
}

/// The count that a response states of one thing for each other thing:
/// `the same response for the same request` is at most one response for each
/// request, and `two responses for each request` is exactly two.
fn functional(item: &Vp, lex: &Lexicon) -> Option<Form> {
    let Some(NpGroup::Single(object)) = &item.object else { return None };
    let [RolePp::Other { preposition, np: NpGroup::Single(owner) }] = item.roles.as_slice() else { return None };
    if !preposition.eq_ignore_ascii_case("for") || !plain(object) || !plain(owner) || item.complement.is_some() || item.content.is_some() {
        return None;
    }
    let same = |np: &Np| np.modifiers.iter().any(|m| m.eq_ignore_ascii_case("same"));
    let number = |np: &Np| np.modifiers.iter().find_map(|m| crate::syntax::words::number_word(m)).and_then(|n| u32::try_from(n).ok()).filter(|n| (1..=LARGEST_COUNT).contains(n));
    let count = if same(object) && same(owner) {
        Count::AtMost(1)
    } else if matches!(owner.det, Some(Det::Each | Det::Every)) || number(owner) == Some(1) {
        match count_of(&object.det) {
            Some(count) => count,
            None => Count::Exactly(number(object)?),
        }
    } else {
        return None;
    };
    let strip = |np: &Np| {
        let mut bare = np.clone();
        bare.modifiers.retain(|m| names(m));
        bare
    };
    let target = noun(&strip(object), lex);
    Some(Form::Counted { kind: noun(&strip(owner), lex), relation: relation(&item.verb, &target), target, count })
}

fn of_core(core: &Core, lex: &Lexicon, out: &mut Vec<Form>) {
    match core {
        Core::Conjoined { items } => items.iter().for_each(|item| of_core(item, lex, out)),
        Core::Existence { subject } => {
            let nps: Vec<&Np> = match subject {
                NpGroup::Single(np) => vec![np],
                NpGroup::Coordinated { items, .. } => items.iter().collect(),
            };
            for np in nps.into_iter().filter(|np| plain(np)) {
                let count = match &np.det {
                    None => Some(Count::AtLeast(1)),
                    det => count_of(det),
                };
                out.extend(count.map(|count| Form::Populated { kind: noun(np, lex), count }));
            }
        }
        Core::Relation { subject: NpGroup::Single(subject), vp } => {
            // `No two rooms have the same name.`
            let two = subject.modifiers.iter().any(|m| m.eq_ignore_ascii_case("two"));
            if let (Some(Det::No), true, VpGroup::Single(item)) = (&subject.det, two, vp) {
                if let Some(NpGroup::Single(object)) = &item.object {
                    if object.modifiers.iter().any(|m| m.eq_ignore_ascii_case("same")) && plain(subject) && plain(object) {
                        let target = noun(object, lex);
                        out.push(Form::Distinct { relation: relation(&item.verb, &target), target, kind: noun(subject, lex) });
                    }
                }
                return;
            }
            out.extend(vp.items().iter().filter_map(|item| related(subject, item, lex)));
        }
        // `The API shall return the same response for the same request.`: the
        // response is a function of the request, so each request has at most
        // one. `… shall return two responses for each request.` counts them.
        Core::Deontic { modal: Modal::Shall | Modal::Must, negated: false, vp: VpGroup::Single(item), .. } => {
            out.extend(functional(item, lex));
        }
        Core::Description { subject: NpGroup::Single(subject), adverb, predicate, agent: None, roles, .. } if roles.is_empty() => {
            let denied = *adverb == Some(DescriptionAdverb::Never);
            match (&subject.of, predicate) {
                // `The number of members of each room is at most 1.`
                (Some(counted), Predicate::Comparison(c)) if subject.head.eq_ignore_ascii_case("number") && !denied => {
                    let Some(count) = count_of_comparison(c) else { return };
                    match &counted.of {
                        Some(owner) if quantifier(&owner.det) == Some(Quantifier::All) && plain(owner) => {
                            let target = noun(counted, lex);
                            out.push(Form::Counted { kind: noun(owner, lex), relation: target.clone(), target, count });
                        }
                        None if counted.relative.is_none() => out.push(Form::Populated { kind: noun(counted, lex), count }),
                        _ => {}
                    }
                }
                // `The total size of all attachments is at most 10 MB.`
                (Some(owner), Predicate::Comparison(_)) if plain(owner) && subject.relative.is_none() && !denied => {
                    let total = subject.modifiers.iter().any(|m| m.eq_ignore_ascii_case("total"));
                    let part = noun(subject, lex);
                    if total && matches!(owner.det, Some(Det::All)) {
                        out.push(Form::Total { kind: noun(owner, lex), total: subject_key(subject, lex), part });
                    } else if let (false, Some(Quantifier::All), Predicate::Comparison(c)) = (total, quantifier(&owner.det), predicate) {
                        out.push(Form::Part { kind: noun(owner, lex), part, comparison: c.clone() });
                    }
                }
                // `The owner of each room is a member of the room.`
                (Some(owner), _) if plain(owner) && generic(&owner.det) && subject.relative.is_none() => {
                    if let Some(wide) = member_phrase(predicate, lex) {
                        out.push(Form::Included { narrow: noun(subject, lex), wide, owner: noun(owner, lex), denied });
                    }
                }
                // `Each guest is a user.`; `No guest is a member.`
                (None, _) if subject.relative.is_none() => {
                    let Some(wide) = kind_phrase(predicate, lex) else { return };
                    match &subject.det {
                        Some(Det::Each | Det::Every | Det::A | Det::An) => out.push(Form::Kind { narrow: noun(subject, lex), wide, both: false, denied }),
                        Some(Det::No) => out.push(Form::Kind { narrow: noun(subject, lex), wide, both: false, denied: !denied }),
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        Core::Definition { term, definiens: Definiens::Np { np: NpGroup::Single(genus), roles } } => {
            match (&term.of, &genus.relative) {
                // `The formal interpretation of a statement means the expression that the statement denotes.`
                (Some(owner), Some(relative)) if plain(owner) && relative.and.is_none() && roles.is_empty() => {
                    if let RelativeBody::ObjectGap { subject: NpGroup::Single(doer), verb, roles, .. } = &relative.body {
                        if roles.is_empty() && noun(doer, lex) == noun(owner, lex) {
                            let first_target = noun(term, lex);
                            let mut bare = genus.clone();
                            bare.relative = None;
                            let second_target = noun(&bare, lex);
                            out.push(Form::Same { first: first_target.clone(), first_target, second: relation(verb, &second_target), second_target, owner: noun(owner, lex) });
                        }
                    }
                }
                // `A guest means a user.`; `A guest means a user without an account.`
                (None, None) if term.relative.is_none() && genus.of.is_none() => {
                    out.push(Form::Kind { narrow: noun(term, lex), wide: noun(genus, lex), both: roles.is_empty(), denied: false });
                }
                // `A guest means a user that has no account.`: each guest is a
                // user with that count, and each user with that count is a guest.
                (None, Some(relative)) if term.relative.is_none() && genus.of.is_none() && relative.and.is_none() && roles.is_empty() => {
                    let RelativeBody::Verbal { verb, particle: None, manner, object: Some(NpGroup::Single(object)), roles: inner, negation: None } = &relative.body else { return };
                    if !manner.is_empty() || !inner.is_empty() || !plain(object) {
                        return;
                    }
                    let Some(count) = count_of(&object.det) else { return };
                    let mut bare = genus.clone();
                    bare.relative = None;
                    let (narrow, wide, target) = (noun(term, lex), noun(&bare, lex), noun(object, lex));
                    let relation = relation(verb, &target);
                    out.push(Form::Kind { narrow: narrow.clone(), wide: wide.clone(), both: false, denied: false });
                    out.push(Form::Related { quantifier: Quantifier::All, kind: narrow.clone(), relation: relation.clone(), target: target.clone(), count });
                    out.push(Form::Defined { narrow, wide, relation, target, count });
                }
                _ => {}
            }
        }
        _ => {}
    }
}

/// The conditions that say whether some individual has something.
fn of_conditions(sentence: &Sentence, lex: &Lexicon, out: &mut Vec<Form>) {
    let frames = &sentence.frames;
    let groups = frames.scopes.iter().chain(&frames.states).map(|f| (f.keyword.as_str(), &f.clause)).chain(frames.trigger.iter().map(|t| (t.keyword.as_str(), &t.clause)));
    for (keyword, group) in groups {
        for clause in &group.items {
            let (NpGroup::Single(subject), ClauseBody::Verbal { verb, object: Some(NpGroup::Single(object)), roles, content: None, negation: None, particle: None, .. }) = (&clause.subject, &clause.body) else { continue };
            if !plain(subject) || !plain(object) || !roles.is_empty() || !matches!(subject.det, Some(Det::A | Det::An | Det::Some)) {
                continue;
            }
            let denied = match &object.det {
                Some(Det::No) => true,
                Some(Det::A | Det::An) => false,
                _ => continue,
            };
            let target = noun(object, lex);
            let single = ClauseGroup { conj: None, items: vec![clause.clone()] };
            let event = crate::reading::model::frame_formula(keyword, &single, lex);
            out.push(Form::Condition { event, kind: noun(subject, lex), relation: relation(verb, &target), target, denied });
        }
    }
}

/// The carriers: nouns whose individuals are the same individuals.
#[derive(Default)]
struct Carriers {
    parent: BTreeMap<String, String>,
}

impl Carriers {
    fn find(&mut self, noun: &str) -> String {
        let parent = self.parent.entry(noun.to_string()).or_insert_with(|| noun.to_string()).clone();
        if parent == noun {
            return parent;
        }
        let root = self.find(&parent);
        self.parent.insert(noun.to_string(), root.clone());
        root
    }

    fn join(&mut self, a: &str, b: &str) {
        let (a, b) = (self.find(a), self.find(b));
        if a != b {
            // The smaller name stands for the carrier, whatever the order of the statements.
            let (keep, drop) = if a < b { (a, b) } else { (b, a) };
            self.parent.insert(drop, keep);
        }
    }
}

struct Grounder {
    scope: usize,
    carriers: Carriers,
}

impl Grounder {
    fn individual(&mut self, noun: &str, index: usize) -> String {
        // An individual is named by the noun of its statement: the name is a
        // part of the reading of that statement alone. That two nouns name
        // the individuals of one carrier is a relation, stated in `apply`.
        format!("{}#{}", noun, index + 1)
    }

    fn is(&mut self, kind: &str, index: usize) -> Formula {
        Formula::atom(Atom::Rel { name: kind.to_string(), args: vec![self.individual(kind, index)] })
    }

    fn holds(&mut self, relation: &str, kind: &str, i: usize, target: &str, j: usize) -> Formula {
        Formula::atom(Atom::Rel { name: relation.to_string(), args: vec![self.individual(kind, i), self.individual(target, j)] })
    }

    /// How many of the formulas hold.
    fn counted(&self, items: &[Formula], count: Count) -> Formula {
        fn subsets(n: usize, k: usize) -> Vec<Vec<usize>> {
            if k == 0 {
                return vec![vec![]];
            }
            if n < k {
                return vec![];
            }
            let mut with: Vec<Vec<usize>> = subsets(n - 1, k - 1).into_iter().map(|mut s| { s.push(n - 1); s }).collect();
            with.extend(subsets(n - 1, k));
            with
        }
        let all = |set: &Vec<usize>| Formula::And(set.iter().map(|i| items[*i].clone()).collect());
        let at_least = |n: usize| if n == 0 { Formula::True } else { Formula::Or(subsets(items.len(), n).iter().map(all).collect()) };
        let at_most = |n: usize| Formula::And(subsets(items.len(), n + 1).iter().map(|set| Formula::not(all(set))).collect());
        match count {
            Count::AtLeast(n) => at_least(n as usize),
            Count::AtMost(n) => at_most(n as usize),
            Count::Exactly(n) => Formula::And(vec![at_least(n as usize), at_most(n as usize)]),
        }
    }

    fn related_count(&mut self, relation: &str, kind: &str, i: usize, target: &str, count: Count) -> Formula {
        let items: Vec<Formula> = (0..self.scope).map(|j| self.holds(relation, kind, i, target, j)).collect();
        self.counted(&items, count)
    }

    fn formula(&mut self, form: &Form, lex: &Lexicon) -> Option<Formula> {
        let scope = self.scope;
        Some(match form {
            Form::Related { quantifier, kind, relation, target, count } => {
                let each: Vec<(Formula, Formula)> = (0..scope).map(|i| (self.is(kind, i), self.related_count(relation, kind, i, target, *count))).collect();
                match quantifier {
                    Quantifier::All => Formula::And(each.into_iter().map(|(is, body)| Formula::implies(is, body)).collect()),
                    Quantifier::Some => Formula::Or(each.into_iter().map(|(is, body)| Formula::And(vec![is, body])).collect()),
                }
            }
            Form::Counted { kind, relation, target, count } => Formula::And((0..scope).map(|i| Formula::implies(self.is(kind, i), self.related_count(relation, kind, i, target, *count))).collect()),
            Form::Defined { narrow, wide, relation, target, count } => Formula::And((0..scope).map(|i| Formula::implies(Formula::And(vec![self.is(wide, i), self.related_count(relation, wide, i, target, *count)]), self.is(narrow, i))).collect()),
            Form::Included { narrow, wide, owner, denied } => {
                let mut parts = Vec::new();
                for i in 0..scope {
                    for j in 0..scope {
                        // The owner of the relation is the same individual on both sides.
                        let a = Formula::atom(Atom::Rel { name: narrow.clone(), args: vec![self.individual(owner, i), self.individual(narrow, j)] });
                        let b = Formula::atom(Atom::Rel { name: wide.clone(), args: vec![self.individual(owner, i), self.individual(wide, j)] });
                        parts.push(if *denied { Formula::not(Formula::And(vec![a, b])) } else { Formula::implies(a, b) });
                    }
                }
                Formula::And(parts)
            }
            Form::Distinct { relation, target, kind } => {
                let mut parts = Vec::new();
                for i in 0..scope {
                    for k in i + 1..scope {
                        for j in 0..scope {
                            parts.push(Formula::not(Formula::And(vec![self.holds(relation, kind, i, target, j), self.holds(relation, kind, k, target, j)])));
                        }
                    }
                }
                Formula::And(parts)
            }
            Form::Populated { kind, count } => {
                let items: Vec<Formula> = (0..scope).map(|i| self.is(kind, i)).collect();
                self.counted(&items, *count)
            }
            Form::Kind { narrow, wide, both, denied } => Formula::And(
                (0..scope)
                    .map(|i| {
                        let (a, b) = (self.is(narrow, i), self.is(wide, i));
                        match (denied, both) {
                            (true, _) => Formula::not(Formula::And(vec![a, b])),
                            (false, true) => Formula::And(vec![Formula::implies(a.clone(), b.clone()), Formula::implies(b, a)]),
                            (false, false) => Formula::implies(a, b),
                        }
                    })
                    .collect(),
            ),
            Form::Same { first, first_target, second, second_target, owner } => {
                let mut parts = Vec::new();
                for i in 0..scope {
                    for j in 0..scope {
                        let a = Formula::atom(Atom::Rel { name: first.clone(), args: vec![self.individual(owner, i), self.individual(first_target, j)] });
                        let b = Formula::atom(Atom::Rel { name: second.clone(), args: vec![self.individual(owner, i), self.individual(second_target, j)] });
                        parts.push(Formula::implies(a.clone(), b.clone()));
                        parts.push(Formula::implies(b, a));
                    }
                }
                Formula::And(parts)
            }
            Form::Part { kind, part, comparison } => {
                let mut parts = Vec::new();
                for i in 0..scope {
                    let quantity = format!("{part} of {}", self.individual(kind, i));
                    parts.push(Formula::implies(self.is(kind, i), comparison_bound(&quantity, comparison, lex)?));
                }
                Formula::And(parts)
            }
            Form::Condition { event, kind, relation, target, denied } => {
                let some = Formula::Or(
                    (0..scope)
                        .map(|i| {
                            let has = self.related_count(relation, kind, i, target, Count::AtLeast(1));
                            Formula::And(vec![self.is(kind, i), if *denied { Formula::not(has) } else { has }])
                        })
                        .collect(),
                );
                Formula::implies(event.clone(), some)
            }
            Form::Total { .. } => return None,
        })
    }
}

fn unit_of(formula: &Formula) -> Option<String> {
    match formula {
        Formula::Atom(Atom::Num { unit, .. }) | Formula::Atom(Atom::Lin { unit, .. }) => Some(unit.clone()),
        Formula::Not(inner) => unit_of(inner),
        Formula::And(items) | Formula::Or(items) => items.iter().find_map(unit_of),
        Formula::Implies(a, b) => unit_of(a).or_else(|| unit_of(b)),
        _ => None,
    }
}

/// Reads the statements about individuals and adds what they say to the model.
pub(super) fn apply(set: &SpecSet, lex: &Lexicon, model: &mut Model, scope: usize) {
    // A scope of zero reads no statement over individuals.
    if scope == 0 {
        return;
    }
    let mut all: Vec<Stated> = Vec::new();
    for pkg in &set.packages {
        for doc in &pkg.documents {
            let scoped = lex.in_document(doc);
            for spec in &doc.specs {
                let display = if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) };
                let origin = SpecRef { id: display, file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
                let mut forms = Vec::new();
                // A statement under a condition speaks about a moment, not about the domain.
                let unconditional = spec.sentence.frames.scopes.is_empty() && spec.sentence.frames.states.is_empty() && spec.sentence.frames.trigger.is_none() && spec.sentence.exception.is_none() && !spec.otherwise;
                if unconditional {
                    of_core(&spec.sentence.core, &scoped, &mut forms);
                }
                of_conditions(&spec.sentence, &scoped, &mut forms);
                all.extend(forms.into_iter().map(|form| Stated { form, origin: origin.clone() }));
            }
        }
    }
    // Only a statement that distinguishes individuals needs them: a statement
    // about some individual, two individuals compared, a relation included in
    // another or made one with another, a count of what is related, a total,
    // a population other than "at least one", or a condition that some
    // individual lacks something. `Each room has exactly one owner.` alone is
    // read in full by the representative of the room; it is read over
    // individuals only when such a statement speaks about the same relation.
    // The representative reading stays for every statement and is the whole
    // reading of the statements that are left out here.
    let seed = |form: &Form| match form {
        Form::Related { quantifier, .. } => *quantifier == Quantifier::Some,
        Form::Populated { count, .. } => !matches!(count, Count::AtLeast(1)),
        Form::Condition { denied, .. } => *denied,
        Form::Kind { .. } | Form::Part { .. } | Form::Defined { .. } => false,
        _ => true,
    };
    let mut relations: BTreeSet<String> = BTreeSet::new();
    let mut kinds: BTreeSet<String> = BTreeSet::new();
    let mut quantities: BTreeSet<String> = BTreeSet::new();
    let mut chosen = vec![false; all.len()];
    loop {
        let mut grew = false;
        for (index, stated) in all.iter().enumerate() {
            if chosen[index] {
                continue;
            }
            let take = seed(&stated.form)
                || match &stated.form {
                    Form::Related { relation, .. } | Form::Counted { relation, .. } | Form::Distinct { relation, .. } | Form::Condition { relation, .. } => relations.contains(relation),
                    Form::Defined { relation, .. } => relations.contains(relation),
                    Form::Included { narrow, wide, .. } => relations.contains(narrow) || relations.contains(wide),
                    Form::Same { first, second, .. } => relations.contains(first) || relations.contains(second),
                    Form::Populated { kind, .. } => kinds.contains(kind),
                    Form::Kind { narrow, wide, .. } => kinds.contains(narrow) || kinds.contains(wide),
                    Form::Total { part, .. } | Form::Part { part, .. } => quantities.contains(part),
                };
            if !take {
                continue;
            }
            chosen[index] = true;
            grew = true;
            match &stated.form {
                Form::Related { kind, relation, target, .. } | Form::Counted { kind, relation, target, .. } | Form::Distinct { kind, relation, target } | Form::Condition { kind, relation, target, .. } => {
                    relations.insert(relation.clone());
                    kinds.insert(kind.clone());
                    kinds.insert(target.clone());
                }
                Form::Defined { narrow, wide, relation, target, .. } => {
                    relations.insert(relation.clone());
                    kinds.insert(narrow.clone());
                    kinds.insert(wide.clone());
                    kinds.insert(target.clone());
                }
                Form::Included { narrow, wide, .. } => {
                    relations.insert(narrow.clone());
                    relations.insert(wide.clone());
                }
                Form::Same { first, first_target, second, second_target, .. } => {
                    relations.insert(first.clone());
                    relations.insert(second.clone());
                    kinds.insert(first_target.clone());
                    kinds.insert(second_target.clone());
                }
                Form::Populated { kind, .. } => {
                    kinds.insert(kind.clone());
                }
                Form::Kind { narrow, wide, .. } => {
                    kinds.insert(narrow.clone());
                    kinds.insert(wide.clone());
                }
                Form::Total { kind, part, .. } | Form::Part { kind, part, .. } => {
                    quantities.insert(part.clone());
                    kinds.insert(kind.clone());
                }
            }
        }
        if !grew {
            break;
        }
    }
    let mut index = 0;
    all.retain(|_| {
        index += 1;
        chosen[index - 1]
    });
    if all.is_empty() {
        return;
    }
    // A statement that counts n individuals is read over at least n of them:
    // a smaller domain would refute it for want of room.
    let most = all
        .iter()
        .filter_map(|s| match &s.form {
            Form::Related { count, .. } | Form::Populated { count, .. } | Form::Counted { count, .. } => Some(*count),
            _ => None,
        })
        .map(|count| match count {
            Count::AtLeast(n) | Count::Exactly(n) | Count::AtMost(n) => n as usize,
        })
        .max()
        .unwrap_or(0);
    let mut grounder = Grounder { scope: scope.max(1).max(most), carriers: Carriers::default() };
    // Two nouns name the individuals of one carrier where a statement makes
    // one a kind of the other or makes two relations one.
    for stated in &all {
        match &stated.form {
            Form::Included { narrow, wide, .. } => grounder.carriers.join(narrow, wide),
            Form::Kind { narrow, wide, .. } | Form::Defined { narrow, wide, .. } => grounder.carriers.join(narrow, wide),
            Form::Same { first_target, second_target, .. } => grounder.carriers.join(first_target, second_target),
            _ => {}
        }
    }
    // A noun with a modifier names a kind of its head ([GROUND-HEAD]): the
    // individuals of `accepted construct` are individuals of `construct`.
    let mut owners: BTreeSet<String> = BTreeSet::new();
    for stated in &all {
        match &stated.form {
            Form::Related { kind, .. } | Form::Distinct { kind, .. } | Form::Counted { kind, .. } | Form::Condition { kind, .. } | Form::Populated { kind, .. } | Form::Part { kind, .. } | Form::Total { kind, .. } => {
                owners.insert(kind.clone());
            }
            Form::Included { owner, .. } | Form::Same { owner, .. } => {
                owners.insert(owner.clone());
            }
            Form::Kind { narrow, wide, .. } | Form::Defined { narrow, wide, .. } => {
                owners.insert(narrow.clone());
                owners.insert(wide.clone());
            }
        }
    }
    let split = |noun: &str| -> (String, String) {
        match noun.rfind("::") {
            Some(at) => (noun[..at + 2].to_string(), noun[at + 2..].to_string()),
            None => (String::new(), noun.to_string()),
        }
    };
    for narrow in &owners {
        for wide in &owners {
            let ((space, name), (other_space, head)) = (split(narrow), split(wide));
            let Some(modifiers) = name.strip_suffix(&format!(" {head}")) else { continue };
            if space == other_space && !modifiers.split(' ').any(|w| crate::syntax::words::is_privative(w) || w.starts_with("non-")) {
                grounder.carriers.join(narrow, wide);
            }
        }
    }
    let mut populated: BTreeMap<String, ()> = BTreeMap::new();
    for stated in &all {
        let Some(formula) = grounder.formula(&stated.form, lex) else { continue };
        if let Form::Related { kind, .. } | Form::Populated { kind, .. } | Form::Counted { kind, .. } | Form::Condition { kind, .. } | Form::Part { kind, .. } | Form::Distinct { kind, .. } = &stated.form {
            populated.insert(kind.clone(), ());
        }
        // A statement that distinguishes individuals says so itself: its
        // formula over the domain is a part of its own reading. A statement
        // that is read over individuals only because another statement speaks
        // about the same relation carries that reading as a relation.
        let kind = if seed(&stated.form) { ConstraintKind::Axiom } else { ConstraintKind::Carried };
        model.constraints.push(Constraint { kind, assume: Formula::True, guarantee: formula, refs: vec![stated.origin.clone()] });
    }
    // The total of a quantity is the sum over the individuals that exist.
    for stated in &all {
        let Form::Total { kind, total, part } = &stated.form else { continue };
        let unit = model.constraints.iter().filter(|c| c.refs.iter().any(|r| r.id == stated.origin.id)).find_map(|c| unit_of(&c.guarantee)).unwrap_or_default();
        let mut terms = vec![(total.clone(), 1)];
        let mut parts = Vec::new();
        for i in 0..grounder.scope {
            let individual = grounder.individual(kind, i);
            let (quantity, share) = (format!("{part} of {individual}"), format!("share of {part} of {individual}"));
            terms.push((share.clone(), -1));
            let equal = |a: &str, b: Option<&str>| {
                let terms: Vec<(String, i64)> = std::iter::once((a.to_string(), 1)).chain(b.map(|b| (b.to_string(), -1))).collect();
                Formula::And(vec![Formula::atom(Atom::Lin { terms: terms.clone(), unit: unit.clone(), cmp: Cmp::Le, n: 0 }), Formula::atom(Atom::Lin { terms, unit: unit.clone(), cmp: Cmp::Ge, n: 0 })])
            };
            let is = grounder.is(kind, i);
            parts.push(Formula::implies(is.clone(), equal(&share, Some(&quantity))));
            parts.push(Formula::implies(Formula::not(is), equal(&share, None)));
        }
        parts.push(Formula::atom(Atom::Lin { terms: terms.clone(), unit: unit.clone(), cmp: Cmp::Le, n: 0 }));
        parts.push(Formula::atom(Atom::Lin { terms, unit: unit.clone(), cmp: Cmp::Ge, n: 0 }));
        populated.insert(kind.clone(), ());
        model.constraints.push(Constraint { kind: ConstraintKind::Axiom, assume: Formula::True, guarantee: Formula::And(parts), refs: vec![stated.origin.clone()] });
    }
    // A relation holds between the individuals of two carriers. A statement
    // names it with its own nouns: `account(guest#1, account#2)` says that
    // the first individual of the carrier is a guest, that the second
    // individual of the other carrier is an account, and that the relation
    // holds between them. The third part is one atom for all nouns of the
    // carrier, so `a guest has an account` and `a user has an account` speak
    // about one relation. What a relation holds between has its types.
    let mut typed: BTreeSet<(String, String, String)> = BTreeSet::new();
    let mut untyped: BTreeSet<(String, String, String)> = BTreeSet::new();
    for stated in &all {
        match &stated.form {
            Form::Related { kind, relation, target, .. } | Form::Distinct { kind, relation, target } | Form::Counted { kind, relation, target, .. } | Form::Condition { kind, relation, target, .. } => {
                typed.insert((relation.clone(), kind.clone(), target.clone()));
            }
            Form::Defined { wide, relation, target, .. } => {
                typed.insert((relation.clone(), wide.clone(), target.clone()));
            }
            Form::Included { narrow, wide, owner, .. } => {
                untyped.insert((narrow.clone(), owner.clone(), narrow.clone()));
                untyped.insert((wide.clone(), owner.clone(), wide.clone()));
            }
            Form::Same { first, first_target, second, second_target, owner } => {
                untyped.insert((first.clone(), owner.clone(), first_target.clone()));
                untyped.insert((second.clone(), owner.clone(), second_target.clone()));
            }
            _ => {}
        }
    }
    for (relation, kind, target) in typed.iter().chain(untyped.iter().filter(|t| !typed.contains(*t))) {
        let types = typed.contains(&(relation.clone(), kind.clone(), target.clone()));
        let (owner_carrier, target_carrier) = (grounder.carriers.find(kind), grounder.carriers.find(target));
        for i in 0..grounder.scope {
            for j in 0..grounder.scope {
                let holds = grounder.holds(relation, kind, i, target, j);
                let shared = Formula::atom(Atom::Rel { name: format!("{relation} between"), args: vec![format!("{owner_carrier}#{}", i + 1), format!("{target_carrier}#{}", j + 1)] });
                // The owner's type is a part of what the statement's atom says;
                // the type of the other individual follows from the relation.
                let whole = if types { Formula::And(vec![shared, grounder.is(kind, i)]) } else { shared };
                model.background.push(Formula::implies(holds.clone(), whole.clone()));
                model.background.push(Formula::implies(whole, holds.clone()));
                if types {
                    model.background.push(Formula::implies(holds, grounder.is(target, j)));
                }
            }
        }
    }
    // A type has an individual exactly when the representative of the type exists.
    for kind in populated.keys() {
        let some = Formula::Or((0..grounder.scope).map(|i| grounder.is(kind, i)).collect());
        let exists = Formula::atom(Atom::Event { key: format!("exists {kind}") });
        model.background.push(Formula::implies(exists.clone(), some.clone()));
        model.background.push(Formula::implies(some, exists));
    }
    // A statement is read over individuals whose domain the chosen statements
    // name together: that reading is a relation between them.
    let mut subjects: Vec<SpecRef> = Vec::new();
    for stated in &all {
        if !subjects.contains(&stated.origin) {
            subjects.push(stated.origin.clone());
        }
    }
    for subject in &subjects {
        if model.constraints.iter().any(|c| c.kind == ConstraintKind::Carried && c.refs.first() == Some(subject)) {
            model.applied.push(crate::reading::model::Applied { kind: "individuals".to_string(), subject: subject.clone(), rests_on: subjects.iter().filter(|other| *other != subject).cloned().collect() });
        }
    }
    model.instance_scope = Some(grounder.scope);
}
