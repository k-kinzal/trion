//! The typed meaning of a statement about individuals.
//!
//! A package declares the types whose individuals its statements tell apart
//! (`individuals user, room, message`). A statement that names such a type
//! speaks about each individual of the type, and one noun names one
//! individual throughout the statement: `When a user posts a message, the
//! system shall store the message.` requires, for each user and each
//! message, the storing of that message.
//!
//! This module states that meaning as data: the variables of a statement
//! with their types, the conditions and the response over them, and for
//! each constituent the rule that read it. The meaning is defined over
//! concrete behaviours (individuals, relations, states, occurrences at
//! moments); `spec/semantics/core.md` states each rule. The formulas that a
//! decision is made over are produced from the instances of the statement
//! (`ground`), and a reference evaluator outside this crate evaluates the
//! meaning on a concrete behaviour without them.
//!
//! The reading rules:
//!
//! - A noun whose type is declared is a variable. Its identity within the
//!   statement is its noun with its ordinal (`message`, `second message`).
//! - A variable is universal: the statement holds for each individual.
//!   One kind is not: `a` or `an` that first names an individual in what
//!   an obligation requires is chosen by the response, and the statement
//!   holds when some individual meets it. Under `should` and `may`, and
//!   with `the`, no rule reads which individual a response
//!   introduces: the statement is outside the fragment.
//! - `the R of the T` restricts the variable of R to the individuals that
//!   stand in the relation R to the individual of T.
//! - A clause `X is [not] a R of the T` is a relation between individuals
//!   and no state; `X is [not] a K` is the kind of an individual.
//! - A noun whose type is not declared names one thing, as before.

use crate::reading::lexicon::Lexicon;
pub use super::nominal::Nominal;
use crate::syntax::ast::*;
use crate::syntax::words::{base_verb, classify, Closed, WordClass};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

/// The meaning rules that a result names (`spec/semantics`). Which of the
/// two readings applies to a package is decided by its declarations
/// (`spec/semantics/readings.md`).
/// The declared types of a set, and which nouns name individuals of one carrier.
#[derive(Debug, Clone, Default)]
pub struct Types {
    /// Each noun of a declared carrier, with the declared noun that names its individuals.
    canonical: BTreeMap<String, String>,
}

impl Types {
    pub(super) fn new(canonical: BTreeMap<String, String>) -> Types {
        Types { canonical }
    }

    /// `true` when the set declares no type.
    pub fn is_empty(&self) -> bool {
        self.canonical.is_empty()
    }

    /// The declared noun whose individuals a noun names.
    pub fn canonical(&self, noun: &str) -> Option<&str> {
        self.canonical.get(noun).map(String::as_str)
    }

    /// Every noun that names individuals, with its declared noun.
    pub fn nouns(&self) -> impl Iterator<Item = (&str, &str)> {
        self.canonical.iter().map(|(noun, declared)| (noun.as_str(), declared.as_str()))
    }
}

/// Where a variable is first named.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Site {
    Condition,
    Subject,
    Response,
    /// First named with `a` or `an` in what an obligation requires or
    /// advice advises: the response chooses the individual, and the
    /// statement holds when some individual meets it.
    Chosen,
}

/// One variable of a statement.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Variable {
    pub id: u32,
    /// The identity within the statement: the noun with its ordinal.
    pub key: String,
    /// The noun as the statement names it.
    pub noun: String,
    /// The declared noun whose individuals the variable ranges over.
    pub carrier: String,
    pub site: Site,
}

/// What a noun phrase denotes.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Term {
    /// An individual: the value of a variable.
    Variable(u32),
    /// One thing that the package names without a declared type.
    Constant(String),
    /// A property of a term: `the name of the room`.
    Attribute { name: String, of: Box<Term> },
}

/// An event or an action: a verb with what takes part.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Pattern {
    pub actor: Term,
    pub verb: String,
    pub particle: Option<String>,
    pub object: Option<Term>,
    /// Each role with its marker: `to`, `from`, `about`, `via`, a preposition.
    pub roles: Vec<(String, Term)>,
}

/// A relation between two individuals, or its denial.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Relation {
    pub relation: String,
    /// The noun that the owner is named by in the relation.
    pub owner_noun: String,
    pub owner: Term,
    pub member: Term,
    pub denied: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "form", rename_all = "snake_case")]
pub enum Condition {
    /// The event occurs, or does not occur.
    Occurs { pattern: Pattern, denied: bool },
    /// The individual is in the state.
    Holds { subject: Term, value: String, denied: bool },
    /// The individuals stand in the relation.
    Related(Relation),
    /// The individual is of the kind.
    Kind { kind: String, subject: Term, denied: bool },
    /// A Boolean classification of one individual.
    Membership { predicate: Nominal<String>, subject: Term, denied: bool },
    /// A comparison of a quantity: its terms are bound, and the reference
    /// evaluator does not evaluate it.
    Compares { text: String },
}

impl Condition {
    pub(super) fn of_domain(&self) -> bool {
        matches!(self, Self::Related(_) | Self::Kind { .. } | Self::Membership { .. })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FrameKind {
    Where,
    While,
    When,
    If,
}

/// One frame: all of its conditions hold, or one of them.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Frame {
    pub kind: FrameKind,
    pub any: bool,
    pub conditions: Vec<Condition>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Force {
    Obligation,
    Prohibition,
    Recommendation,
    RecommendationAgainst,
    Permission,
    Description,
}

/// A quantity with its unit, in thousandths.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Quantity {
    pub thousandths: i64,
    pub unit: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "form", rename_all = "snake_case")]
pub enum Response {
    /// The action completes; within the deadline, after and before the named events.
    Action { pattern: Pattern, deadline: Option<Quantity>, after: Vec<Pattern>, before: Vec<Pattern> },
    /// The individual is in the state.
    State { subject: Term, value: String, denied: bool },
    /// The individual is in one of the states, and in no other.
    Values { subject: Term, values: Vec<String> },
    /// The individuals stand in the relation.
    Related(Relation),
    /// The individual is of the kind.
    Kind { kind: String, subject: Term, denied: bool },
    /// A Boolean classification of one individual.
    Membership { predicate: Nominal<String>, subject: Term, denied: bool },
    /// A bound on a quantity: its terms are bound, and the reference
    /// evaluator does not evaluate it.
    Bound { text: String },
}

/// How a share is bounded.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Bounding {
    AtLeast,
    AtMost,
    MoreThan,
    LessThan,
    Exactly,
}

/// A bound on the share of a population: `for at least 99 percent of postings`.
///
/// The population is the set of the activations of the statement in one
/// behaviour: each assignment of its variables with each moment at which its
/// conditions hold. An activation counts for the share when the response
/// answers it as the statement requires; an activation without a response
/// stays in the population. The share of an empty population is not defined.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Share {
    pub bounding: Bounding,
    /// The bound in thousandths of a percent.
    pub thousandths: i64,
    /// The declared measure that names the population.
    pub population: String,
}

/// How the responses of a statement stand together.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Choice {
    One,
    Each,
    Either,
}

/// One step of the reading: the rule, the words that it read and what it made of them.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Step {
    pub rule: &'static str,
    pub words: String,
    pub yields: String,
}

/// The typed meaning of one statement.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Meaning {
    pub statement: String,
    pub source: String,
    pub variables: Vec<Variable>,
    /// The restrictions of the variables: `the author of the message`.
    pub restrictions: Vec<Relation>,
    pub frames: Vec<Frame>,
    /// `unless`: the statement applies where the condition fails.
    pub exception: Option<Condition>,
    pub force: Force,
    pub choice: Choice,
    pub responses: Vec<Response>,
    /// The share of the activations that the responses answer, when the
    /// statement bounds a share and not each activation.
    pub share: Option<Share>,
    pub steps: Vec<Step>,
}

impl Meaning {
    fn shown(&self, term: &Term) -> String {
        match term {
            Term::Variable(id) => format!("the {}", self.variables[*id as usize].key),
            Term::Constant(name) => format!("the {name}"),
            Term::Attribute { name, of } => format!("the {name} of {}", self.shown(of)),
        }
    }

    fn pattern(&self, pattern: &Pattern) -> String {
        let mut text = format!("{} {}", self.shown(&pattern.actor), pattern.verb);
        if let Some(particle) = &pattern.particle {
            text.push_str(&format!(" {particle}"));
        }
        if let Some(object) = &pattern.object {
            text.push_str(&format!(" {}", self.shown(object)));
        }
        for (marker, term) in &pattern.roles {
            text.push_str(&format!(" {marker} {}", self.shown(term)));
        }
        text
    }

    fn condition(&self, condition: &Condition) -> String {
        let not = |denied: bool| if denied { "not " } else { "" };
        match condition {
            Condition::Occurs { pattern, denied } => format!("{}[{}] occurs", if *denied { "no " } else { "" }, self.pattern(pattern)),
            Condition::Holds { subject, value, denied } => format!("{} is {}`{value}`", self.shown(subject), not(*denied)),
            Condition::Related(relation) => format!("{} is {}a {} of {}", self.shown(&relation.member), not(relation.denied), relation.relation, self.shown(&relation.owner)),
            Condition::Kind { kind, subject, denied } => format!("{} is {}a {kind}", self.shown(subject), not(*denied)),
            Condition::Membership { predicate, subject, denied } => format!("{} satisfies {}{predicate}", self.shown(subject), not(*denied)),
            Condition::Compares { text } => text.clone(),
        }
    }

    /// The reading of the statement as an author can check it: what it is
    /// about, where it applies and what it requires. Each line is made from
    /// the record, and no line is the source text.
    pub fn lines(&self) -> Vec<String> {
        let mut lines = Vec::new();
        let about: Vec<String> = self
            .variables
            .iter()
            .map(|v| {
                let held: Vec<String> = self.restrictions.iter().filter(|r| r.member == Term::Variable(v.id)).map(|r| format!("that is a {} of {}", r.relation, self.shown(&r.owner))).collect();
                let kind = if v.noun == v.carrier { String::new() } else { format!(" (an individual of `{}`)", v.carrier) };
                let (each, chosen) = if v.site == Site::Chosen { ("some", ", chosen by the response") } else { ("each", "") };
                format!("{each} {}{kind}{}{chosen}", v.key, if held.is_empty() { String::new() } else { format!(" {}", held.join(" and ")) })
            })
            .collect();
        lines.push(if about.is_empty() { "about: no individual of a declared type".to_string() } else { format!("about: {}", about.join("; ")) });
        for frame in &self.frames {
            let keyword = match frame.kind {
                FrameKind::Where => "where",
                FrameKind::While => "at each moment at which",
                FrameKind::When => "at each occurrence at which",
                FrameKind::If => "at each unwanted occurrence at which",
            };
            let conditions: Vec<String> = frame.conditions.iter().map(|c| self.condition(c)).collect();
            lines.push(format!("applies {keyword}: {}", conditions.join(if frame.any { ", or " } else { ", and " })));
        }
        if self.frames.is_empty() {
            lines.push("applies: to the behaviour as a whole".to_string());
        }
        if let Some(exception) = &self.exception {
            lines.push(format!("does not apply where: {}", self.condition(exception)));
        }
        let force = match self.force {
            Force::Obligation => "requires",
            Force::Prohibition => "forbids",
            Force::Recommendation => "advises",
            Force::RecommendationAgainst => "advises against",
            Force::Permission => "permits",
            Force::Description => "states",
        };
        let responses: Vec<String> = self
            .responses
            .iter()
            .map(|response| match response {
                Response::Action { pattern, deadline, after, before } => {
                    let mut text = format!("[{}]", self.pattern(pattern));
                    if let Some(deadline) = deadline {
                        text.push_str(&format!(", completed at most {} ms after the occurrence (the end included)", deadline.thousandths / 1000));
                    }
                    for event in after {
                        text.push_str(&format!(", after [{}] of the same activation", self.pattern(event)));
                    }
                    for event in before {
                        text.push_str(&format!(", before [{}] of the same activation", self.pattern(event)));
                    }
                    text
                }
                Response::State { subject, value, denied } => format!("{} is {}`{value}`", self.shown(subject), if *denied { "not " } else { "" }),
                Response::Values { subject, values } => format!("{} is in exactly one of the states {} at each moment", self.shown(subject), values.iter().map(|v| format!("`{v}`")).collect::<Vec<_>>().join(", ")),
                Response::Related(relation) => format!("{} is {}a {} of {}", self.shown(&relation.member), if relation.denied { "not " } else { "" }, relation.relation, self.shown(&relation.owner)),
                Response::Kind { kind, subject, denied } => format!("{} is {}a {kind}", self.shown(subject), if *denied { "not " } else { "" }),
                Response::Membership { predicate, subject, denied } => format!("{} satisfies {}{predicate}", self.shown(subject), if *denied { "not " } else { "" }),
                Response::Bound { text } => text.clone(),
            })
            .collect();
        let joined = match self.choice {
            Choice::Either => responses.join(", or "),
            Choice::One | Choice::Each => responses.join(", and "),
        };
        lines.push(format!("{force}: {joined}"));
        if let Some(share) = &self.share {
            let bounding = match share.bounding {
                Bounding::AtLeast => "at least",
                Bounding::AtMost => "at most",
                Bounding::MoreThan => "more than",
                Bounding::LessThan => "less than",
                Bounding::Exactly => "exactly",
            };
            lines.push(format!("of: {bounding} {}.{:03} percent of the activations of this statement in one behaviour (`{}`); an activation without a response counts, and an empty population has no share", share.thousandths / 1000, share.thousandths % 1000, share.population));
        }
        lines
    }
}

/// How a statement stands to the typed fragment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Reading {
    /// The statement names no declared type.
    Untyped,
    Typed(Box<Meaning>),
    /// The statement names a declared type in a construct that no rule of
    /// the compiler reads over individuals.
    Outside { construct: String, why: String },
}

/// The reading rules, each with what it reads.
pub const RULES: &[(&str, &str)] = &[
    ("variable", "a noun of a declared type is a variable; its identity is its noun with its ordinal"),
    ("variable-again", "a noun that the statement named before is the same variable"),
    ("variable-some", "`a` or `an` that first names an individual of a declared type in what an obligation requires or advice advises is a variable that the response chooses: the statement holds when some individual of the kind meets it"),
    ("variable-any", "`a` or `an` that first names an individual of a declared type in what a permission permits names any individual: each individual of the kind is permitted"),
    ("variable-other", "two variables of one noun that differ by an ordinal name different individuals"),
    ("variable-that", "a relative clause on a noun of a declared type is a condition of the statement about that individual: with a copula a state, a kind or a relation at the moment at which the statement applies, with a verb the event at which it applies"),
    ("variable-no", "`no T` as the subject or the object of a statement with a modal verb denies the statement of each individual"),
    ("variable-count", "a number before a noun of a declared type names so many different individuals, one by one"),
    ("variable-of", "`the R of the T` restricts the variable of R to what stands in the relation R to the individual of T"),
    ("constant", "a noun without a declared type names one thing"),
    ("attribute", "`the N of the T` with an undeclared N is a property of the individual of T"),
    ("frame-where", "`Where` restricts the statement to the configuration"),
    ("frame-while", "`While` restricts the statement to the moments at which the state holds"),
    ("frame-when", "`When` applies the statement at each occurrence of the event"),
    ("frame-if", "`If` applies the statement at each occurrence of the unwanted event"),
    ("condition-occurs", "a clause with a verb is the occurrence of an event with its participants"),
    ("condition-holds", "a clause with a copula and a value is the state of an individual"),
    ("condition-related", "`X is [not] a R of the T` is a relation between two individuals"),
    ("condition-kind", "`X is [not] a K` is the kind of an individual"),
    ("condition-compares", "a clause with a comparison bounds a quantity"),
    ("exception", "`unless` applies the statement where the condition fails"),
    ("force", "the modal verb and its negation give the force of the statement"),
    ("response-action", "the verb phrase is the action that completes, with its participants"),
    ("response-deadline", "`within` bounds the time from the occurrence to the completion, the end included"),
    ("response-after", "`after` requires the completion strictly after the named event of the same activation"),
    ("response-before", "`before` requires the completion strictly before the named event of the same activation"),
    ("response-state", "a predicate with a value is the state of an individual"),
    ("response-values", "an enumeration lists the states of an individual, and excludes every other"),
    ("response-related", "`X is [not] a R of the T` is a relation between two individuals"),
    ("response-kind", "`X is [not] a K` is the kind of an individual"),
    ("response-bound", "a comparison bounds a quantity"),
    ("response-share", "`for <bound> percent of <population>` bounds the share of the activations that the response answers"),
    ("choice-either", "`either … or` requires one of the actions"),
    ("choice-each", "a list of actions requires each of them"),
    ("choice-order", "`in order` requires each action, each strictly after the one before it"),
];

pub(super) struct Outside {
    construct: String,
    why: String,
}

pub(super) fn outside<T>(construct: impl Into<String>, why: impl Into<String>) -> Result<T, Outside> {
    Err(Outside { construct: construct.into(), why: why.into() })
}

struct Reader<'a> {
    types: &'a Types,
    lex: &'a Lexicon,
    variables: Vec<Variable>,
    restrictions: Vec<Relation>,
    steps: Vec<Step>,
    site: Site,
    typed: bool,
    share: Option<Share>,
    /// `true` while the response of an obligation or of advice is read:
    /// `a` and `an` introduce an individual that the response chooses.
    chooses: bool,
}

fn is_ordinal(word: &str) -> bool {
    ["second", "third", "fourth", "fifth", "sixth", "other"].iter().any(|w| word.eq_ignore_ascii_case(w))
}

fn open(word: &str) -> bool {
    matches!(classify(word), WordClass::Open)
}

/// The noun that the words name, in the singular.
pub(super) fn noun_of(words: &[String], lex: &Lexicon) -> String {
    let mut words: Vec<String> = words.iter().map(|w| w.to_lowercase()).collect();
    if let Some(last) = words.last_mut() {
        *last = base_verb(last);
    }
    lex.resolve(&lex.canon(&words.join(" ")))
}

/// The head noun of a noun phrase, without its modifiers.
pub(super) fn head_noun(np: &Np, lex: &Lexicon) -> String {
    noun_of(std::slice::from_ref(&np.head), lex)
}

/// A predicate `[not] a R` or `[not] a K`: the noun, and whether it is denied.
fn kind_words(words: &[String], definite: bool, lex: &Lexicon) -> Option<(String, bool)> {
    let (denied, rest) = match words.first().map(|w| w.to_lowercase()).as_deref() {
        Some("not") => (true, &words[1..]),
        _ => (false, words),
    };
    let rest = match rest.first().map(|w| w.to_lowercase()).as_deref() {
        Some("a" | "an") => &rest[1..],
        // `the author of the message`: the one that stands in the relation.
        Some("the") if definite => &rest[1..],
        _ => return None,
    };
    (!rest.is_empty() && rest.iter().all(|w| open(w))).then(|| (noun_of(rest, lex), denied))
}

/// The words of a value, and whether the predicate denies it.
fn value_words(words: &[String]) -> (String, bool) {
    match words.first().map(|w| w.to_lowercase()).as_deref() {
        Some("not") => (words[1..].join(" ").to_lowercase(), true),
        _ => (words.join(" ").to_lowercase(), false),
    }
}

/// What a copular predicate with its roles says of a subject of a declared type.
pub(super) enum Said {
    Related { relation: String, owner: Np, denied: bool },
    Kind { kind: String, denied: bool },
    Membership { predicate: Nominal<String>, denied: bool },
    Value { value: String, denied: bool },
}

pub(super) fn said(words: &[String], roles: &[RolePp], lex: &Lexicon) -> Option<Said> {
    // The predicate of a description keeps its tail as words: `the author of the message`.
    if let (Some(at), true) = (words.iter().position(|w| w.eq_ignore_ascii_case("of")), roles.is_empty()) {
        let (relation, denied) = kind_words(&words[..at], true, lex)?;
        let owner = &words[at + 1..];
        let (det, owner) = match owner.first().map(|w| w.to_lowercase()).as_deref() {
            Some("the") => (Det::The, &owner[1..]),
            Some("a") => (Det::A, &owner[1..]),
            Some("an") => (Det::An, &owner[1..]),
            Some("each") => (Det::Each, &owner[1..]),
            _ => return None,
        };
        let (head, modifiers) = owner.split_last()?;
        if !owner.iter().all(|w| open(w) || is_ordinal(w)) {
            return None;
        }
        let owner = Np { det: Some(det), modifiers: modifiers.to_vec(), head: head.clone(), of: None, relative: None, of_also: Vec::new(), of_conj: None };
        return Some(Said::Related { relation, owner, denied });
    }
    let of = matches!(roles, [RolePp::Other { preposition, np: NpGroup::Single(_) }] if preposition.eq_ignore_ascii_case("of"));
    match (kind_words(words, of, lex), roles) {
        (Some((relation, denied)), [RolePp::Other { preposition, np: NpGroup::Single(owner) }]) if preposition.eq_ignore_ascii_case("of") => Some(Said::Related { relation, owner: owner.clone(), denied }),
        (Some((kind, denied)), []) => Some(Said::Kind { kind, denied }),
        (None, []) => {
            // Each word of a value is a word of a name: a closed-class word there has no reading.
            let (value, denied) = value_words(words);
            let named = words.iter().skip(usize::from(denied)).all(|w| open(w) || w.starts_with('`') || w.starts_with('"'));
            (!value.is_empty() && named).then_some(Said::Value { value, denied })
        }
        _ => None,
    }
}

pub(super) fn said_predicate(predicate: &Predicate, roles: &[RolePp], lex: &Lexicon) -> Option<Said> {
    let Predicate::Words { words, nominal } = predicate else { return None };
    if let Some(group) = nominal.as_ref() {
        if !roles.is_empty() {
            return None;
        }
        let denied = words.first().is_some_and(|word| word.eq_ignore_ascii_case("not"));
        if let NpGroup::Single(np) = group {
            if let Some(owner) = &np.of {
                if np.relative.is_none() && np.of_also.is_empty() && matches!(np.det, Some(Det::A | Det::An | Det::The)) {
                    return Some(Said::Related { relation: super::nominal::name(np, lex), owner: *owner.clone(), denied });
                }
                return None;
            }
        }
        return match super::nominal::classes(group, lex)? {
            Nominal::Atom(kind) => Some(Said::Kind { kind, denied }),
            predicate => Some(Said::Membership { predicate, denied }),
        };
    }
    said(words, roles, lex)
}

fn role_marker(role: &RolePp) -> Option<(String, &NpGroup)> {
    Some(match role {
        RolePp::Recipient(np) => ("to".to_string(), np),
        RolePp::Topic(np) => ("about".to_string(), np),
        RolePp::Source(np) => ("from".to_string(), np),
        RolePp::Goal(np) => ("into".to_string(), np),
        RolePp::Agent(np) => ("by".to_string(), np),
        RolePp::Means { marker, np } => (marker.as_str().to_string(), np),
        RolePp::Location { preposition, np } | RolePp::Other { preposition, np } => (preposition.to_lowercase(), np),
        _ => return None,
    })
}

fn quantity(measure: &Measure) -> Option<Quantity> {
    let Measure::Quantity { number, unit: Some(unit) } = measure else { return None };
    let (whole, fraction) = number.split_once('.').unwrap_or((number, ""));
    if fraction.len() > 3 || !whole.chars().chain(fraction.chars()).all(|c| c.is_ascii_digit()) || whole.is_empty() {
        return None;
    }
    let thousandths = whole.parse::<i64>().ok()?.checked_mul(1000)?.checked_add(format!("{fraction:0<3}").parse::<i64>().ok()?)?;
    let unit = unit.to_lowercase();
    // A time is kept in milliseconds: the factor is exact.
    let (factor, unit) = match unit.as_str() {
        "ms" | "millisecond" | "milliseconds" => (1, "ms"),
        "s" | "sec" | "secs" | "second" | "seconds" => (1000, "ms"),
        "min" | "mins" | "minute" | "minutes" => (60_000, "ms"),
        "h" | "hour" | "hours" => (3_600_000, "ms"),
        other => return Some(Quantity { thousandths, unit: other.to_string() }),
    };
    Some(Quantity { thousandths: thousandths.checked_mul(factor)?, unit: unit.to_string() })
}

impl Reader<'_> {
    fn step(&mut self, rule: &'static str, words: impl Into<String>, yields: impl Into<String>) {
        debug_assert!(RULES.iter().any(|(name, _)| *name == rule));
        self.steps.push(Step { rule, words: words.into(), yields: yields.into() });
    }

    fn show(&self, term: &Term) -> String {
        match term {
            Term::Variable(id) => format!("v{id}:{}", self.variables[*id as usize].key),
            Term::Constant(name) => name.clone(),
            Term::Attribute { name, of } => format!("{name} of {}", self.show(of)),
        }
    }

    fn pattern_text(&self, p: &Pattern) -> String {
        let mut text = format!("{}({}", p.verb, self.show(&p.actor));
        if let Some(particle) = &p.particle {
            text = format!("{} {particle}({}", p.verb, self.show(&p.actor));
        }
        if let Some(object) = &p.object {
            text.push_str(&format!(", {}", self.show(object)));
        }
        for (marker, term) in &p.roles {
            text.push_str(&format!(", {marker}: {}", self.show(term)));
        }
        text.push(')');
        text
    }

    /// What a noun phrase denotes.
    fn term(&mut self, np: &Np) -> Result<Term, Outside> {
        let words = np.render();
        let head = head_noun(np, self.lex);
        let Some(carrier) = self.types.canonical(&head).map(str::to_string) else {
            // A noun without a declared type names one thing; with an owner
            // of a declared type it is a property of that individual.
            if let Some(relative) = &np.relative {
                let mut inner = false;
                relative_nps(relative, &mut |np| inner |= self.types.canonical(&head_noun(np, self.lex)).is_some());
                if inner {
                    return outside(words, "a relative clause that names a declared type is not read over individuals: state it as a condition of the statement");
                }
            }
            let name = crate::reading::model::np_key(&Np { of: None, of_also: Vec::new(), of_conj: None, ..np.clone() }, self.lex);
            return Ok(match &np.of {
                Some(owner) if np.of_also.is_empty() => {
                    let of = self.term(owner)?;
                    match of {
                        Term::Constant(_) => {
                            let whole = crate::reading::model::np_key(np, self.lex);
                            self.step("constant", words, whole.clone());
                            Term::Constant(whole)
                        }
                        of => {
                            let term = Term::Attribute { name, of: Box::new(of) };
                            self.step("attribute", words, self.show(&term));
                            term
                        }
                    }
                }
                _ => {
                    let whole = crate::reading::model::np_key(np, self.lex);
                    self.step("constant", words, whole.clone());
                    Term::Constant(whole)
                }
            });
        };
        self.typed = true;
        if np.relative.is_some() {
            return outside(words, "a relative clause on a declared type is read where it stands in a condition, on the subject or in what the statement requires: here state it as a condition, as in `While the user is a member of the room,`");
        }
        if !np.of_also.is_empty() {
            return outside(words, "a coordinated owner is not read over individuals");
        }
        let ordinals: Vec<String> = np.modifiers.iter().filter(|m| is_ordinal(m)).map(|m| m.to_lowercase()).collect();
        if np.modifiers.iter().any(|m| !is_ordinal(m) && !m.starts_with('`')) {
            return outside(words, "a modifier before a declared type is not read over individuals: state the property as a condition, as in `While the room is open,`");
        }
        match &np.det {
            Some(Det::The | Det::A | Det::An | Det::Each | Det::Every | Det::Any) => {}
            None if np.modifiers.iter().any(|m| m.starts_with('`')) => {}
            _ => return outside(words, "a declared type is named with `a`, `an`, `the`, `each`, `every` or `any`; a count is read in a `While` condition and in what an obligation requires, and `no` before the subject or the object of a statement with a modal verb: here it is read by a statement about the domain"),
        }
        let key = ordinals.iter().cloned().chain(std::iter::once(head.clone())).collect::<Vec<_>>().join(" ");
        let owner = match &np.of {
            Some(owner) => Some((self.term(owner)?, head_noun(owner, self.lex))),
            None => None,
        };
        let id = match self.variables.iter().find(|v| v.key == key) {
            Some(known) => {
                let id = known.id;
                if owner.is_none() {
                    self.step("variable-again", words.clone(), format!("v{id}:{key}"));
                }
                id
            }
            None => {
                let general = matches!(np.det, Some(Det::Each | Det::Every | Det::Any));
                // `a` or `an` that first names an individual in what an
                // obligation requires: the response chooses it.
                let introduced = self.site == Site::Response && matches!(np.det, Some(Det::A | Det::An));
                let chosen = introduced && self.chooses;
                // Under `may`, `a` or `an` names any individual: each is permitted.
                let any = introduced && !self.chooses;
                if self.site == Site::Response && owner.is_none() && !general && !introduced {
                    return outside(words, "the response names with `the` an individual that no condition names: name it in a condition, relate it to a named individual, as in `the author of the message`, or introduce it with `a`");
                }
                let id = self.variables.len() as u32;
                let others: Vec<String> = self.variables.iter().filter(|v| v.noun == head).map(|v| format!("v{}:{}", v.id, v.key)).collect();
                self.variables.push(Variable { id, key: key.clone(), noun: head.clone(), carrier, site: if chosen { Site::Chosen } else { self.site } });
                if !others.is_empty() {
                    self.step("variable-other", words.clone(), format!("v{id}:{key} is another individual than {}", others.join(", ")));
                }
                if chosen {
                    self.step("variable-some", words.clone(), format!("v{id}:{key}, some individual of `{}`", self.variables[id as usize].carrier));
                } else if any {
                    self.step("variable-any", words.clone(), format!("v{id}:{key}, each individual of `{}`", self.variables[id as usize].carrier));
                } else {
                    self.step("variable", words.clone(), format!("v{id}:{key}, each individual of `{}`", self.variables[id as usize].carrier));
                }
                id
            }
        };
        if let Some((owner, owner_noun)) = owner {
            if !matches!(owner, Term::Variable(_)) {
                return outside(words, "the owner of a relation is an individual of a declared type");
            }
            let relation = Relation { relation: head.clone(), owner_noun, owner, member: Term::Variable(id), denied: false };
            self.step("variable-of", words, format!("{}({}, v{id}:{key})", relation.relation, self.show(&relation.owner)));
            if !self.restrictions.contains(&relation) {
                self.restrictions.push(relation);
            }
        }
        Ok(Term::Variable(id))
    }

    fn single(&mut self, group: &NpGroup) -> Result<Term, Outside> {
        match group {
            NpGroup::Single(np) => self.term(np),
            NpGroup::Coordinated { items, .. } => {
                let typed = items.iter().any(|np| self.types.canonical(&head_noun(np, self.lex)).is_some());
                if typed {
                    self.typed = true;
                    return outside(group.render(), "coordinated noun phrases of a declared type are not read over individuals: write one statement for each");
                }
                Ok(Term::Constant(group.render().to_lowercase()))
            }
        }
    }

    fn roles(&mut self, roles: &[RolePp], out: &mut Vec<(String, Term)>) -> Result<(), Outside> {
        for role in roles {
            if let Some((marker, group)) = role_marker(role) {
                let term = self.single(group)?;
                out.push((marker, term));
            }
        }
        Ok(())
    }

    fn pattern(&mut self, actor: Term, verb: &str, particle: &Option<String>, object: &Option<NpGroup>, roles: &[RolePp]) -> Result<Pattern, Outside> {
        let object = match object {
            Some(group) => Some(self.single(group)?),
            None => None,
        };
        let mut read = Vec::new();
        self.roles(roles, &mut read)?;
        let lemma = base_verb(&verb.to_lowercase());
        let verb = self.lex.predicate_identity(&lemma).unwrap_or(lemma);
        Ok(Pattern { actor, verb, particle: particle.as_ref().map(|p| p.to_lowercase()), object, roles: read })
    }

    fn clause(&mut self, clause: &Clause) -> Result<Condition, Outside> {
        let text = clause.render();
        let subject = self.single(&clause.subject)?;
        match &clause.body {
            ClauseBody::Verbal { verb, particle, object, roles, content, negation, manner } => {
                if base_verb(verb) == "exist"
                    && particle.is_none() && object.is_none() && roles.is_empty()
                    && content.is_none() && manner.is_empty()
                {
                    return outside(text, "this existence condition needs a population rule over individuals. State a population requirement separately or bind an individual in the condition that uses it");
                }
                if content.is_some() {
                    let before = self.typed;
                    let object_typed = self.typed_inside_clause(clause);
                    self.typed = before || object_typed;
                    if object_typed {
                        return outside(text, "a content clause is not read over individuals");
                    }
                }
                if roles.iter().any(|r| matches!(r, RolePp::Before(_) | RolePp::After(_) | RolePp::Until(_) | RolePp::Deadline(_) | RolePp::Duration(_) | RolePp::Rate { .. })) && self.typed {
                    return outside(text, "a condition with a time role is not read over individuals");
                }
                let _ = manner;
                let pattern = self.pattern(subject, verb, particle, object, roles)?;
                let denied = negation.is_some();
                self.step("condition-occurs", text, format!("{}{}", if denied { "not " } else { "" }, self.pattern_text(&pattern)));
                Ok(Condition::Occurs { pattern, denied })
            }
            ClauseBody::Copular { predicate, agent, roles, .. } => {
                if agent.is_some() {
                    if self.typed {
                        return outside(text, "a passive condition with an agent is not read over individuals: state it in the active voice");
                    }
                    return Ok(Condition::Compares { text });
                }
                match predicate {
                    Predicate::Words { .. } => match said_predicate(predicate, roles, self.lex) {
                        Some(Said::Related { relation, owner, denied }) => {
                            let owner_noun = head_noun(&owner, self.lex);
                            let owner = self.term(&owner)?;
                            if !matches!((&owner, &subject), (Term::Variable(_), Term::Variable(_))) {
                                if self.typed {
                                    return outside(text, "a relation holds between two individuals of declared types");
                                }
                                return Ok(Condition::Compares { text });
                            }
                            let relation = Relation { relation, owner_noun, owner, member: subject, denied };
                            self.step("condition-related", text, format!("{}{}({}, {})", if denied { "not " } else { "" }, relation.relation, self.show(&relation.owner), self.show(&relation.member)));
                            Ok(Condition::Related(relation))
                        }
                        Some(Said::Kind { kind, denied }) => {
                            self.step("condition-kind", text, format!("{}{kind}({})", if denied { "not " } else { "" }, self.show(&subject)));
                            Ok(Condition::Kind { kind, subject, denied })
                        }
                        Some(Said::Membership { predicate, denied }) if matches!(subject, Term::Variable(_)) => {
                            self.step("condition-kind", text, format!("{}{predicate}({})", if denied { "not " } else { "" }, self.show(&subject)));
                            Ok(Condition::Membership { predicate, subject, denied })
                        }
                        Some(Said::Value { value, denied }) => {
                            self.step("condition-holds", text, format!("{} is {}{value}", self.show(&subject), if denied { "not " } else { "" }));
                            Ok(Condition::Holds { subject, value, denied })
                        }
                        _ if self.typed => outside(text, "this predicate with its roles is not read over individuals"),
                        _ => Ok(Condition::Compares { text }),
                    },
                    Predicate::Comparison(_) => {
                        self.step("condition-compares", text.clone(), text.clone());
                        Ok(Condition::Compares { text })
                    }
                    _ if self.typed => outside(text, "this predicate is not read over individuals"),
                    _ => Ok(Condition::Compares { text }),
                }
            }
        }
    }

    fn typed_inside_clause(&self, clause: &Clause) -> bool {
        let mut any = false;
        clause_nps(clause, &mut |np| any |= self.types.canonical(&head_noun(np, self.lex)).is_some());
        any
    }

    fn frame(&mut self, kind: FrameKind, group: &ClauseGroup) -> Result<Frame, Outside> {
        let rule = match kind {
            FrameKind::Where => "frame-where",
            FrameKind::While => "frame-while",
            FrameKind::When => "frame-when",
            FrameKind::If => "frame-if",
        };
        let mut conditions = Vec::new();
        for clause in &group.items {
            conditions.push(self.clause(clause)?);
        }
        let any = group.conj == Some(Conj::Or);
        if any && self.typed && conditions.iter().any(Condition::of_domain) {
            return outside(group.render(), "an alternative between a relation and another condition is not read over individuals: write one statement for each");
        }
        self.step(rule, group.render(), format!("{} condition(s), {}", conditions.len(), if any { "one of them" } else { "all of them" }));
        Ok(Frame { kind, any, conditions })
    }

    fn response(&mut self, subject: &Term, vp: &Vp) -> Result<Response, Outside> {
        let text = vp.render();
        if vp.content.is_some() || vp.complement.is_some() {
            let mut any = false;
            vp_nps(vp, &mut |np| any |= self.types.canonical(&head_noun(np, self.lex)).is_some());
            if any || self.typed {
                return outside(text, "a complement or a content clause is not read over individuals");
            }
        }
        let mut deadline = None;
        let (mut after, mut before) = (Vec::new(), Vec::new());
        // `for at least 99 percent of postings`: the bound and its population.
        let share_at = vp.roles.iter().position(|role| matches!(role, RolePp::Duration(Measure::Quantity { unit: Some(u), .. } | Measure::Bounded { unit: Some(u), .. }) if u.eq_ignore_ascii_case("percent") || u == "%"));
        if let Some(at) = share_at {
            let (RolePp::Duration(measure), Some(RolePp::Other { preposition, np })) = (&vp.roles[at], vp.roles.get(at + 1)) else { return outside(text, "a share names its population, as in `for at least 99 percent of postings`") };
            if !preposition.eq_ignore_ascii_case("of") || self.share.is_some() {
                return outside(text, "a share names one population, as in `for at least 99 percent of postings`");
            }
            let (bounding, number) = match measure {
                Measure::Quantity { number, .. } | Measure::Bounded { op: ComparisonOp::AtLeast, number, upper: None, .. } => (Bounding::AtLeast, number),
                Measure::Bounded { op: ComparisonOp::AtMost, number, upper: None, .. } => (Bounding::AtMost, number),
                Measure::Bounded { op: ComparisonOp::GreaterThan, number, upper: None, .. } => (Bounding::MoreThan, number),
                Measure::Bounded { op: ComparisonOp::LessThan, number, upper: None, .. } => (Bounding::LessThan, number),
                Measure::Bounded { op: ComparisonOp::EqualTo, number, upper: None, .. } => (Bounding::Exactly, number),
                _ => return outside(text, "a share between two bounds is not read over individuals: state each bound in a statement"),
            };
            let Some(Quantity { thousandths, .. }) = quantity(&Measure::Quantity { number: number.clone(), unit: Some("percent".to_string()) }) else { return outside(text, "the bound of a share is a number of percent with at most three decimals") };
            let population = np.render();
            let population = population.strip_prefix("the ").or_else(|| population.strip_prefix("all ")).unwrap_or(&population).to_lowercase();
            self.step("response-share", format!("for {} of {population}", measure.render()), format!("{bounding:?} {thousandths} thousandths of a percent of the activations").to_lowercase());
            self.share = Some(Share { bounding, thousandths, population });
        }
        let shared = |index: usize| share_at.is_some_and(|at| index == at || index == at + 1);
        for (index, role) in vp.roles.iter().enumerate() {
            if shared(index) {
                continue;
            }
            match role {
                RolePp::Deadline(measure) => match quantity(measure) {
                    Some(q) if q.unit == "ms" => {
                        self.step("response-deadline", format!("within {}", measure.render()), format!("at most {} ms after the occurrence", q.thousandths / 1000));
                        deadline = Some(q);
                    }
                    _ if self.typed => return outside(text, "this deadline is not read over individuals: state a number with a unit of time"),
                    _ => {}
                },
                RolePp::After(clause) | RolePp::Before(clause) => {
                    let actor = self.single(&clause.subject)?;
                    let ClauseBody::Verbal { verb, particle, object, roles, content: None, negation: None, .. } = &clause.body else {
                        if self.typed {
                            return outside(text, "an order is read against an event with a verb");
                        }
                        continue;
                    };
                    let pattern = self.pattern(actor, verb, particle, object, roles)?;
                    let is_after = matches!(role, RolePp::After(_));
                    self.step(if is_after { "response-after" } else { "response-before" }, clause.render(), self.pattern_text(&pattern));
                    if is_after { after.push(pattern) } else { before.push(pattern) }
                }
                RolePp::Until(_) | RolePp::Duration(_) | RolePp::Rate { .. } if self.typed => return outside(text, "this time role is not read over individuals"),
                _ => {}
            }
        }
        let named: Vec<RolePp> = vp.roles.iter().enumerate().filter(|(index, _)| !shared(*index)).map(|(_, role)| role.clone()).collect();
        let pattern = self.pattern(subject.clone(), &vp.verb, &vp.particle, &vp.object, &named)?;
        self.step("response-action", text, self.pattern_text(&pattern));
        Ok(Response::Action { pattern, deadline, after, before })
    }

    fn described(&mut self, subject: Term, predicate: &Predicate, roles: &[RolePp], text: String) -> Result<Response, Outside> {
        match predicate {
            Predicate::Words { .. } => match said_predicate(predicate, roles, self.lex) {
                Some(Said::Related { relation, owner, denied }) => {
                    let owner_noun = head_noun(&owner, self.lex);
                    let owner = self.term(&owner)?;
                    if !matches!((&owner, &subject), (Term::Variable(_), Term::Variable(_))) {
                        return outside(text, "a relation holds between two individuals of declared types");
                    }
                    let relation = Relation { relation, owner_noun, owner, member: subject, denied };
                    self.step("response-related", text, format!("{}{}({}, {})", if denied { "not " } else { "" }, relation.relation, self.show(&relation.owner), self.show(&relation.member)));
                    Ok(Response::Related(relation))
                }
                Some(Said::Kind { kind, denied }) => {
                    self.step("response-kind", text, format!("{}{kind}({})", if denied { "not " } else { "" }, self.show(&subject)));
                    Ok(Response::Kind { kind, subject, denied })
                }
                Some(Said::Membership { predicate, denied }) if matches!(subject, Term::Variable(_)) => {
                    self.step("response-kind", text, format!("{}{predicate}({})", if denied { "not " } else { "" }, self.show(&subject)));
                    Ok(Response::Membership { predicate, subject, denied })
                }
                Some(Said::Value { value, denied }) => {
                    self.step("response-state", text, format!("{} is {}{value}", self.show(&subject), if denied { "not " } else { "" }));
                    Ok(Response::State { subject, value, denied })
                }
                _ => outside(text, "this predicate with its roles is not read over individuals"),
            },
            Predicate::Enumeration { values, conj: Conj::Or, .. } => {
                let values: Vec<String> = values.iter().map(|v| v.to_lowercase()).collect();
                self.step("response-values", text, format!("{} is one of {}", self.show(&subject), values.join(", ")));
                Ok(Response::Values { subject, values })
            }
            Predicate::Comparison(_) => {
                self.step("response-bound", text.clone(), text.clone());
                Ok(Response::Bound { text })
            }
            _ => outside(text, "this predicate is not read over individuals"),
        }
    }
}

/// Visits each noun phrase of a relative clause.
fn relative_nps(relative: &Relative, visit: &mut dyn FnMut(&Np)) {
    match &relative.body {
        RelativeBody::Content { clause } => clause_nps(clause, visit),
        RelativeBody::Copular { agent, roles, predicate, .. } => {
            agent.iter().for_each(|g| group_nps(g, visit));
            roles_nps(roles, visit);
            predicate_nps(predicate, visit);
        }
        RelativeBody::Verbal { object, roles, .. } => {
            object.iter().for_each(|g| group_nps(g, visit));
            roles_nps(roles, visit);
        }
        RelativeBody::ObjectGap { subject, roles, .. } => {
            group_nps(subject, visit);
            roles_nps(roles, visit);
        }
    }
    if let Some(and) = &relative.and {
        relative_nps(and, visit);
    }
}

fn np_nps(np: &Np, visit: &mut dyn FnMut(&Np)) {
    visit(np);
    if let Some(of) = &np.of {
        np_nps(of, visit);
    }
    np.of_also.iter().for_each(|o| np_nps(o, visit));
    if let Some(relative) = &np.relative {
        relative_nps(relative, visit);
    }
}

fn group_nps(group: &NpGroup, visit: &mut dyn FnMut(&Np)) {
    match group {
        NpGroup::Single(np) => np_nps(np, visit),
        NpGroup::Coordinated { items, .. } => items.iter().for_each(|np| np_nps(np, visit)),
    }
}

fn measure_nps(measure: &Measure, visit: &mut dyn FnMut(&Np)) {
    if let Measure::Np { np } = measure {
        group_nps(np, visit);
    }
}

fn predicate_nps(predicate: &Predicate, visit: &mut dyn FnMut(&Np)) {
    match predicate {
        Predicate::Comparison(c) => {
            measure_nps(&c.value, visit);
            c.upper.iter().for_each(|m| measure_nps(m, visit));
        }
        Predicate::AbleTo { vp } => vp_nps(vp, visit),
        Predicate::Pp { np, .. } => group_nps(np, visit),
        Predicate::Words { .. } | Predicate::Enumeration { .. } => {}
    }
}

fn roles_nps(roles: &[RolePp], visit: &mut dyn FnMut(&Np)) {
    for role in roles {
        match role {
            RolePp::Recipient(g) | RolePp::Topic(g) | RolePp::Source(g) | RolePp::Goal(g) | RolePp::Agent(g) => group_nps(g, visit),
            RolePp::Means { np, .. } | RolePp::Location { np, .. } | RolePp::Other { np, .. } => group_nps(np, visit),
            RolePp::Deadline(m) | RolePp::Duration(m) => measure_nps(m, visit),
            RolePp::Before(c) | RolePp::After(c) | RolePp::Until(c) => clause_nps(c, visit),
            RolePp::Rate { .. } => {}
        }
    }
}

pub(super) fn vp_nps(vp: &Vp, visit: &mut dyn FnMut(&Np)) {
    vp.object.iter().for_each(|g| group_nps(g, visit));
    roles_nps(&vp.roles, visit);
    vp.complement.iter().for_each(|p| predicate_nps(p, visit));
    vp.content.iter().for_each(|c| clause_nps(c, visit));
}

pub(super) fn clause_nps(clause: &Clause, visit: &mut dyn FnMut(&Np)) {
    group_nps(&clause.subject, visit);
    match &clause.body {
        ClauseBody::Copular { predicate, agent, roles, .. } => {
            predicate_nps(predicate, visit);
            agent.iter().for_each(|g| group_nps(g, visit));
            roles_nps(roles, visit);
        }
        ClauseBody::Verbal { object, roles, content, .. } => {
            object.iter().for_each(|g| group_nps(g, visit));
            roles_nps(roles, visit);
            content.iter().for_each(|c| clause_nps(c, visit));
        }
    }
}

fn comp_nps(node: &CompNode, visit: &mut dyn FnMut(&Np)) {
    match node {
        CompNode::Leaf { exception, .. } => exception.iter().for_each(|c| clause_nps(c, visit)),
        CompNode::All { items } | CompNode::Some { items } | CompNode::One { items } | CompNode::Sequence { items } => items.iter().for_each(|i| comp_nps(i, visit)),
        CompNode::Flow(flow) => {
            flow.steps.iter().for_each(|s| comp_nps(&s.node, visit));
            flow.choices.iter().flat_map(|c| &c.arms).for_each(|(group, _)| group.items.iter().for_each(|c| clause_nps(c, visit)));
        }
    }
}

fn core_nps(core: &Core, visit: &mut dyn FnMut(&Np)) {
    match core {
        Core::Definition { term, definiens } => {
            np_nps(term, visit);
            match definiens {
                Definiens::Np { np, roles } => {
                    group_nps(np, visit);
                    roles_nps(roles, visit);
                }
                Definiens::Clause(clause) => clause_nps(clause, visit),
            }
        }
        Core::Description { subject, predicate, agent, roles, .. } => {
            group_nps(subject, visit);
            predicate_nps(predicate, visit);
            agent.iter().for_each(|g| group_nps(g, visit));
            roles_nps(roles, visit);
        }
        Core::Deontic { subject, vp, .. } | Core::Relation { subject, vp } => {
            group_nps(subject, visit);
            match vp {
                VpGroup::Single(vp) => vp_nps(vp, visit),
                VpGroup::Alternatives { items } | VpGroup::All { items, .. } => items.iter().for_each(|vp| vp_nps(vp, visit)),
                VpGroup::Composite(composition) => {
                    composition.leaves.iter().for_each(|vp| vp_nps(vp, visit));
                    comp_nps(&composition.root, visit);
                }
            }
        }
        Core::Existence { subject } => group_nps(subject, visit),
        Core::Conjoined { items } => items.iter().for_each(|c| core_nps(c, visit)),
    }
}

/// Visits each noun phrase of a sentence.
pub(super) fn sentence_nps(sentence: &Sentence, visit: &mut dyn FnMut(&Np)) {
    let frames = &sentence.frames;
    for group in frames.scopes.iter().chain(&frames.states).map(|f| &f.clause).chain(frames.trigger.iter().map(|t| &t.clause)).chain(&sentence.necessary).chain(&sentence.iff) {
        group.items.iter().for_each(|c| clause_nps(c, visit));
    }
    core_nps(&sentence.core, visit);
    sentence.exception.iter().for_each(|c| clause_nps(c, visit));
    match &sentence.purpose {
        Some(Purpose::SoThat(clause)) => clause_nps(clause, visit),
        Some(Purpose::InOrderTo(vp)) => vp_nps(vp, visit),
        None => {}
    }
}

/// `true` when a sentence names a declared type anywhere.
pub(super) fn names_a_type(sentence: &Sentence, types: &Types, lex: &Lexicon) -> bool {
    let mut any = false;
    sentence_nps(sentence, &mut |np| any |= types.canonical(&head_noun(np, lex)).is_some());
    any
}

/// The words that the classes of the language reserve and that a typed
/// statement cannot hold in a name.
fn reserved(word: &str) -> bool {
    matches!(classify(word), WordClass::Closed(Closed::Quantifier | Closed::Distinction))
}

/// Reads one statement against the declared types.
pub fn read(statement: &str, sentence: &Sentence, types: &Types, lex: &Lexicon) -> Reading {
    if types.is_empty() || !names_a_type(sentence, types, lex) {
        return Reading::Untyped;
    }
    let plain = match crate::reading::normal::normal(sentence, types, lex) {
        Ok(plain) => plain,
        Err(Outside { construct, why }) => return Reading::Outside { construct, why },
    };
    let mut reader = Reader { types, lex, variables: Vec::new(), restrictions: Vec::new(), steps: plain.steps, site: Site::Condition, typed: true, share: None, chooses: false };
    match meaning(&mut reader, statement, &plain.sentence) {
        Ok(meaning) => Reading::Typed(Box::new(meaning)),
        Err(Outside { construct, why }) => Reading::Outside { construct, why },
    }
}

/// The plain form of a statement that names a declared type: the sentence
/// that its instances are instances of (`crate::reading::normal`).
pub(super) fn plain(sentence: &Sentence, types: &Types, lex: &Lexicon) -> Option<Sentence> {
    if types.is_empty() || !names_a_type(sentence, types, lex) {
        return None;
    }
    crate::reading::normal::normal(sentence, types, lex).ok().map(|plain| plain.sentence)
}

fn meaning(reader: &mut Reader, statement: &str, sentence: &Sentence) -> Result<Meaning, Outside> {
    if sentence.necessary.is_some() || sentence.iff.is_some() {
        return outside("only when / exactly when", "a necessary condition is not read over individuals");
    }
    if sentence.concession.is_some() {
        return outside("even when", "a concession is not read over individuals: state the obligation without it");
    }
    let mut frames = Vec::new();
    for frame in &sentence.frames.scopes {
        frames.push(reader.frame(FrameKind::Where, &frame.clause)?);
    }
    for frame in &sentence.frames.states {
        frames.push(reader.frame(FrameKind::While, &frame.clause)?);
    }
    if let Some(trigger) = &sentence.frames.trigger {
        let kind = if trigger.kind == TriggerKind::Contingency { FrameKind::If } else { FrameKind::When };
        frames.push(reader.frame(kind, &trigger.clause)?);
    }
    // An exception is read before the response: what it names is named by a condition.
    let exception = match &sentence.exception {
        Some(clause) => {
            let condition = reader.clause(clause)?;
            reader.step("exception", clause.render(), "the statement applies where this fails");
            Some(condition)
        }
        None => None,
    };
    let (force, choice, responses) = match &sentence.core {
        Core::Deontic { subject, modal, negated, vp } => {
            reader.site = Site::Subject;
            let actor = reader.single(subject)?;
            let force = match (modal, negated) {
                (Modal::Shall | Modal::Must, false) => Force::Obligation,
                (Modal::Shall | Modal::Must, true) => Force::Prohibition,
                (Modal::Should, false) => Force::Recommendation,
                (Modal::Should, true) => Force::RecommendationAgainst,
                (Modal::May, _) => Force::Permission,
            };
            reader.step("force", format!("{}{}", modal.as_str(), if *negated { " not" } else { "" }), format!("{force:?}").to_lowercase());
            // What a prohibition names, it names in general: no individual is excepted.
            reader.site = if matches!(force, Force::Prohibition | Force::RecommendationAgainst) { Site::Condition } else { Site::Response };
            reader.chooses = matches!(force, Force::Obligation | Force::Recommendation);
            let (choice, items): (Choice, Vec<&Vp>) = match vp {
                VpGroup::Single(vp) => (Choice::One, vec![vp]),
                VpGroup::Alternatives { items } => (Choice::Either, items.iter().collect()),
                VpGroup::All { items, negated } if negated.iter().all(|n| !n) => (Choice::Each, items.iter().collect()),
                VpGroup::All { .. } => return outside("a list with a denied action", "a list of actions with a denied one is not read over individuals: write one statement for each"),
                // A composition of plain actions was written as a list (`crate::reading::normal`).
                VpGroup::Composite(_) => return outside("composition", "of the compositions, `all of`, `one or more of` and `in order` are read over individuals: `exactly one of` and a flow are not, so write one statement for each action"),
            };
            match choice {
                Choice::Either => reader.step("choice-either", vp.render(), format!("one of {} actions", items.len())),
                Choice::Each => reader.step("choice-each", vp.render(), format!("each of {} actions", items.len())),
                Choice::One => {}
            }
            let mut responses = Vec::new();
            for item in items {
                responses.push(reader.response(&actor, item)?);
            }
            let chooses = reader.variables.iter().any(|v| v.site == Site::Chosen);
            if chooses && choice == Choice::Either {
                return outside(vp.render(), "an individual that the response chooses among alternative actions is not read over individuals: write one statement for each action");
            }
            (force, choice, responses)
        }
        Core::Description { subject, predicate, agent: None, roles, adverb, .. } => {
            reader.site = Site::Subject;
            let subject_term = reader.single(subject)?;
            reader.site = Site::Condition;
            let text = sentence.core.render();
            let mut response = reader.described(subject_term, predicate, roles, text)?;
            if *adverb == Some(DescriptionAdverb::Never) {
                response = match response {
                    Response::State { subject, value, denied } => Response::State { subject, value, denied: !denied },
                    Response::Related(relation) => Response::Related(Relation { denied: !relation.denied, ..relation }),
                    Response::Kind { kind, subject, denied } => Response::Kind { kind, subject, denied: !denied },
                    Response::Membership { predicate, subject, denied } => Response::Membership { predicate, subject, denied: !denied },
                    _ => return outside("never", "`never` before this predicate is not read over individuals"),
                };
            }
            (Force::Description, Choice::One, vec![response])
        }
        other => {
            let construct = match other {
                Core::Definition { .. } => "definition",
                Core::Relation { .. } => "relation",
                Core::Existence { .. } => "existence",
                Core::Conjoined { .. } => "conjoined clauses",
                _ => "passive description",
            };
            return outside(construct, "this form names a declared type and is neither a statement about the domain nor a statement that a rule reads over individuals");
        }
    };
    let _ = reserved;
    if reader.share.is_some() && !(force == Force::Obligation && choice == Choice::One) {
        return outside("a share", "a share bounds how many activations a required action answers: it stands with `shall` and one action");
    }
    if reader.share.is_some() && reader.variables.iter().any(|v| v.site == Site::Chosen) {
        return outside("a share", "a share of activations whose response chooses an individual is not read: name the individual in a condition");
    }
    Ok(Meaning {
        statement: statement.to_string(),
        source: sentence.source.clone(),
        variables: std::mem::take(&mut reader.variables),
        restrictions: std::mem::take(&mut reader.restrictions),
        frames,
        exception,
        force,
        choice,
        responses,
        share: reader.share.take(),
        steps: std::mem::take(&mut reader.steps),
    })
}

/// The carriers of a meaning: each variable with its declared noun.
pub fn carriers(meaning: &Meaning) -> BTreeSet<String> {
    meaning.variables.iter().map(|v| v.carrier.clone()).collect()
}

/// A bound on a number of individuals.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Count {
    AtLeast(u32),
    AtMost(u32),
    Exactly(u32),
}

/// What a statement about the domain says.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "form", rename_all = "snake_case")]
pub enum DomainFact {
    /// `Each T has <count> U.` (`each`), or `Some T has <count> U.`
    Related { each: bool, kind: String, relation: String, target: String, count: Count },
    /// `The R1 of each T is a R2 of the T.`; `never` denies it.
    Included { narrow: String, wide: String, owner: String, denied: bool },
    /// `No two Ts have the same U.`
    Distinct { relation: String, target: String, kind: String },
    /// `There is a T.`, `There are at least two Ts.`
    Populated { kind: String, count: Count },
    /// `The number of Rs of each T is <count>.`
    Counted { kind: String, relation: String, target: String, count: Count },
    /// `Each A is a B.`; `No A is a B.`; a definition makes both the same.
    Kind { narrow: String, wide: String, both: bool, denied: bool },
    /// A Boolean classification of each or some member of a bounded type.
    Membership { narrow: String, predicate: Nominal<String>, each: bool, denied: bool },
    /// `The R1 of a T means the U that the T <verb>s.`
    Same { first: String, second: String, owner: String },
    /// `A T means a G that <verb>s <count> U.`
    Defined { narrow: String, wide: String, relation: String, target: String, count: Count },
    /// A total or a part of a quantity, or a condition on an individual:
    /// the reference evaluator does not evaluate it.
    Unevaluated,
}

/// One statement about the domain with what it says.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DomainStatement {
    pub statement: String,
    pub source: String,
    pub fact: DomainFact,
}
