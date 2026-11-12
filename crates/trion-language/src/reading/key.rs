//! Structured keys: the names of atoms, built from the nodes of the syntax tree.
//!
//! The key of an action, of an event or of a value is a sequence of parts.
//! Each part is one of these:
//!
//! - a word of a name: an open-class word in an open place of the tree (a
//!   modifier, a head, a word of a predicate, a manner, a verb);
//! - a declared term: a run of words that a definition, a declaration or an
//!   alias names, whatever words it holds;
//! - a literal: a quoted string, a code span, a number, a variable;
//! - a mark: what one node of the tree contributes, written by the arm of the
//!   match that reads that node (a determiner, a count, a role, a copula, a
//!   relative marker, a comparison).
//!
//! A part of the class `Word` can be made in one place only, and that place
//! asks the lexer for the class of the word. A closed-class word therefore
//! cannot become a word of a name: it either reaches the key as the mark of
//! the node that the parser built for it, or it is reported as unread and the
//! statement has no formal reading. The text of a key is derived from its
//! parts, never the other way round.

use crate::reading::lexicon::Lexicon;
use trion_solver::Cmp;
use crate::syntax::ast::*;
use crate::syntax::words::{classify, Closed, WordClass};
use std::cell::RefCell;
use std::collections::BTreeMap;

/// Where a word of a name stands in the tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Place {
    Modifier,
    Head,
    Predicate,
    Manner,
    Verb,
    Value,
}

impl Place {
    pub(super) fn describe(self) -> &'static str {
        match self {
            Place::Modifier => "before the head of a noun phrase",
            Place::Head => "as the head of a noun phrase",
            Place::Predicate => "inside a predicate",
            Place::Manner => "as the manner of a verb",
            Place::Verb => "as a verb",
            Place::Value => "as a value",
        }
    }
}

/// What a node of the tree contributes to a key.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Mark {
    /// `each`, `every`, `all`, `any`, `both`, `same`: how many things the
    /// action reaches, not which action it is.
    General,
    /// `no` before a noun: the denial of the noun phrase.
    Denial,
    /// `exactly 1`, `at least 2`, `one or more`: a bound on a number of things.
    Count,
    /// `its`, `this`, `that`: a noun phrase that points back.
    Reference,
    /// `both … and`, `either … or`.
    Group,
    /// `and`, `or` between noun phrases or clauses.
    Coordination,
    /// The preposition of a role.
    Role,
    /// The preposition of a role that orders the action: `before`, `after`, `during`, `until`.
    Order,
    /// `is`, `are`, `remains`.
    Copula,
    /// `not`, `does not`, `never`.
    Negation,
    /// `that`, `who`, `whose`, `where` of a relative clause.
    Relative,
    /// `that` of a content clause.
    Content,
    /// `at most`, `greater than`, `between`.
    Comparison,
    /// `able to`.
    Ability,
    /// `only` before the phrase that an action is restricted to.
    Focus,
    /// A unit, a rate, the `per` of a rate.
    Measure,
    /// `one of` before an enumeration.
    Enumeration,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Class {
    Word,
    Term,
    Literal,
    Mark(Mark),
    Unread,
}

/// One part of a key.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Part {
    text: String,
    class: Class,
    count: Option<(Cmp, i64)>,
    /// `true` for a word of order, time or number that stands in a declared
    /// term before its noun: the term names a kind of that noun.
    kind: bool,
}

impl Part {
    /// `true` for the word of a declared term that names a kind of the noun after it.
    pub fn names_kind(&self) -> bool {
        self.kind
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn mark(&self) -> Option<Mark> {
        match self.class {
            Class::Mark(mark) => Some(mark),
            _ => None,
        }
    }

    /// The bound of a count.
    pub fn count(&self) -> Option<(Cmp, i64)> {
        self.count
    }

    /// `true` for a word of a name that is no declared term and no literal.
    pub fn is_word(&self) -> bool {
        self.class == Class::Word
    }

    /// `true` for a part that no reading rule read.
    pub fn is_unread(&self) -> bool {
        self.class == Class::Unread
    }

    /// `true` for a word of a name or a declared term.
    pub fn is_name(&self) -> bool {
        matches!(self.class, Class::Word | Class::Term | Class::Literal)
    }
}

/// The text of a run of parts.
pub(super) fn text(parts: &[Part]) -> String {
    parts.iter().map(|p| p.text.as_str()).collect::<Vec<_>>().join(" ")
}

/// `assembled`: the `-ed` form of a verb that the lexicon knows.
fn past_participle_of_known_verb(word: &str, lex: &Lexicon) -> bool {
    let word = word.to_lowercase();
    let Some(stem) = word.strip_suffix("ed") else { return false };
    if stem.len() < 3 {
        return false;
    }
    let mut candidates = vec![stem.to_string(), format!("{stem}e")];
    let bytes = stem.as_bytes();
    if bytes[bytes.len() - 1] == bytes[bytes.len() - 2] {
        candidates.push(stem[..stem.len() - 1].to_string());
    }
    if let Some(y) = stem.strip_suffix('i') {
        candidates.push(format!("{y}y"));
    }
    candidates.iter().any(|candidate| lex.verbs.contains(candidate))
}

/// A part of a sentence that no reading rule read.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Unread {
    pub part: String,
    pub kind: &'static str,
    pub place: &'static str,
    pub phrase: String,
}

/// What the keys of one statement leave behind: the parts that were not
/// read, and the parts of each key by its text.
#[derive(Debug, Default)]
pub(crate) struct Sink {
    pub unread: Vec<Unread>,
    pub keys: BTreeMap<String, Vec<Part>>,
}

thread_local! {
    static SINK: RefCell<Option<Sink>> = const { RefCell::new(None) };
}

/// Runs a part of the formalizer and returns what its keys left behind.
pub(super) fn collect<T>(run: impl FnOnce() -> T) -> (T, Sink) {
    let outer = SINK.with(|s| s.borrow_mut().replace(Sink::default()));
    let out = run();
    let sink = SINK.with(|s| std::mem::replace(&mut *s.borrow_mut(), outer)).unwrap_or_default();
    (out, sink)
}

/// Opens the account of one statement.
pub(super) fn begin() {
    SINK.with(|s| *s.borrow_mut() = Some(Sink::default()));
}

/// Closes the account of one statement and returns it.
pub(super) fn end() -> Sink {
    SINK.with(|s| s.borrow_mut().take()).unwrap_or_default()
}

fn report(unread: Unread) {
    SINK.with(|s| {
        if let Some(sink) = s.borrow_mut().as_mut() {
            if !sink.unread.contains(&unread) {
                sink.unread.push(unread);
            }
        }
    });
}

/// Hands the account of an inner run to the account of the statement.
pub(crate) fn forward(sink: Sink) {
    for unread in sink.unread {
        report(unread);
    }
    for (name, parts) in sink.keys {
        register(&name, &parts);
    }
}

/// Reports a node that has no reading.
pub(super) fn unread_node(part: &str, kind: &'static str, place: &'static str) {
    report(Unread { part: part.to_string(), kind, place, phrase: String::new() });
}

fn register(name: &str, parts: &[Part]) {
    SINK.with(|s| {
        if let Some(sink) = s.borrow_mut().as_mut() {
            sink.keys.entry(name.to_string()).or_insert_with(|| parts.to_vec());
        }
    });
}

/// What a token is meant to be before the lexicon has seen it.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Intent {
    Open(Place),
    /// A word of a code span: no word of the sentence.
    Quoted,
    Mark(Mark),
    Unread(&'static str),
}

#[derive(Debug, Clone)]
struct Tok {
    text: String,
    intent: Intent,
    count: Option<(Cmp, i64)>,
    /// The index of the open run that the token belongs to.
    run: usize,
}

/// Where a noun phrase stands, for the reading of its determiner.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Position {
    /// The subject of a clause or the argument of a verb.
    Argument,
    /// The owner after `of`.
    Owner,
}

/// Builds the parts of one key from nodes of the tree.
pub(super) struct Emit<'a> {
    lex: &'a Lexicon,
    toks: Vec<Tok>,
    runs: usize,
    /// `true` while the key of an action is built: `only` restricts an action.
    action: bool,
}

impl<'a> Emit<'a> {
    pub(super) fn new(lex: &'a Lexicon) -> Self {
        Emit { lex, toks: Vec::new(), runs: 0, action: false }
    }

    fn push(&mut self, text: &str, intent: Intent) {
        for (_, word) in crate::syntax::parse::raw_words(text) {
            self.toks.push(Tok { text: word.to_string(), intent, count: None, run: self.runs });
        }
    }

    /// A word of the name of a noun phrase. A code span names what it
    /// spells: its words are no words of the sentence.
    fn name_word(&mut self, word: &str, place: Place) {
        // `each statement the`: an article names nothing.
        if place == Place::Head && matches!(word, "the" | "a" | "an") {
            unread_node(word, "an article", "at the end of a noun phrase, where its noun is expected");
            return;
        }
        if word.len() >= 3 && word.starts_with('`') && word.ends_with('`') {
            self.push(&word[1..word.len() - 1], Intent::Quoted);
        } else {
            self.push(word, Intent::Open(place));
        }
    }

    fn mark(&mut self, mark: Mark, text: &str) {
        self.runs += 1;
        self.push(text, Intent::Mark(mark));
        self.runs += 1;
    }

    fn counted(&mut self, text: &str, cmp: Cmp, n: i64) {
        self.runs += 1;
        let from = self.toks.len();
        self.push(text, Intent::Mark(Mark::Count));
        if let Some(first) = self.toks.get_mut(from) {
            first.count = Some((cmp, n));
        }
        self.runs += 1;
    }

    fn rejected(&mut self, text: &str, kind: &'static str, place: &'static str) {
        self.runs += 1;
        self.push(text, Intent::Unread(kind));
        self.runs += 1;
        unread_node(text, kind, place);
    }

    /// The words of one open place. A run of open places that follow each
    /// other without a mark between them is one phrase: a declared term may
    /// span it.
    fn open(&mut self, words: &[String], place: Place) {
        for word in words {
            self.push(word, Intent::Open(place));
        }
    }

    fn comma(&mut self) {
        if let Some(last) = self.toks.last_mut() {
            last.text.push(',');
        }
    }

    /// The determiner of a noun phrase, in the place where it stands.
    fn det(&mut self, det: &Option<Det>, position: Position) {
        let Some(det) = det else { return };
        match (det, position) {
            // An article says nothing that a key holds.
            (Det::The | Det::A | Det::An, _) => {}
            (Det::Each | Det::Every | Det::All | Det::Any | Det::Both, _) => self.mark(Mark::General, &det.render()),
            (Det::No, _) => self.mark(Mark::Denial, "no"),
            (Det::AtLeast { n } | Det::Cardinal { n, .. }, Position::Argument) => self.counted(&det.render(), Cmp::Ge, *n as i64),
            (Det::AtMost { n }, Position::Argument) => self.counted(&det.render(), Cmp::Le, *n as i64),
            (Det::Exactly { n }, Position::Argument) => self.counted(&det.render(), Cmp::Eq, *n as i64),
            (Det::OneOrMore, Position::Argument) => self.counted(&det.render(), Cmp::Ge, 1),
            (Det::ZeroOrMore, Position::Argument) => self.counted(&det.render(), Cmp::Ge, 0),
            // The owner of a thing is one thing: a count of owners bounds nothing that the key names.
            // `the choices of one response`: at least one owner is an owner.
            (Det::AtLeast { n: 1 } | Det::Cardinal { n: 1, .. } | Det::OneOrMore, Position::Owner) => {}
            // A count of owners bounds nothing that the key names: it has no reading there.
            (Det::AtLeast { .. } | Det::Cardinal { .. } | Det::AtMost { .. } | Det::Exactly { .. } | Det::ZeroOrMore, Position::Owner) => self.rejected(&det.render(), "a count", "before the owner of a thing"),
            // `some request`: one thing that is not named. A key names a kind, not one of its members.
            (Det::Some, _) => self.rejected("some", "a quantifier", "before a noun phrase inside a name"),
            // `its`, `their`, `this`, `that`: the parser replaced each with what it names.
            // One that is left stands where no rule resolves a reference.
            (Det::Reference { word }, _) if word != "another" => self.rejected(word, "a pronoun", "that names no thing of its sentence"),
            (Det::Reference { word }, _) => self.mark(Mark::Reference, word),
        }
    }

    /// A noun phrase as a sentence writes it: determiner, modifiers, head,
    /// owner, relative clause.
    fn np(&mut self, np: &Np, position: Position) {
        let Np { det, modifiers, head, of, relative, of_also, of_conj } = np;
        self.det(det, position);
        self.name_words(det, modifiers, head);
        if let Some(owner) = of {
            self.mark(Mark::Role, "of");
            self.np(owner, Position::Owner);
        }
        for (i, owner) in of_also.iter().enumerate() {
            if i + 1 == of_also.len() {
                self.mark(Mark::Coordination, if *of_conj == Some(Conj::And) { "and" } else { "or" });
            } else {
                self.comma();
            }
            self.mark(Mark::Role, "of");
            self.np(owner, Position::Owner);
        }
        if let Some(relative) = relative {
            self.relative(relative);
        }
    }

    /// The modifiers and the head of a noun phrase: one phrase of a name.
    fn name_words(&mut self, det: &Option<Det>, modifiers: &[String], head: &str) {
        self.runs += 1;
        for (i, word) in modifiers.iter().enumerate() {
            if misplaced_article(det, i, word) {
                continue;
            }
            // `the same block` is the block: `same` says how many things the action reaches.
            if i == 0 && word.eq_ignore_ascii_case("same") {
                self.mark(Mark::General, "same");
                self.runs -= 1;
                continue;
            }
            // `only inactive users`: the phrase that an action is restricted to.
            // `only one` counts and restricts nothing.
            let counts = modifiers.get(i + 1).map_or(head, |next| next.as_str());
            if word.eq_ignore_ascii_case("only") && self.action && !matches!(counts, "one" | "1") {
                self.mark(Mark::Focus, "only");
                self.runs -= 1;
                continue;
            }
            self.push(word, Intent::Open(Place::Modifier));
        }
        // `rename a term only in the namespace`: `only` after the noun
        // restricts the action to what follows.
        if head.eq_ignore_ascii_case("only") && self.action {
            if let Some(last) = self.toks.last_mut().filter(|t| t.run == self.runs && matches!(t.intent, Intent::Open(_))) {
                last.intent = Intent::Open(Place::Head);
            }
            self.mark(Mark::Focus, "only");
            return;
        }
        self.name_word(head, Place::Head);
        self.runs += 1;
    }

    /// The words that name a noun phrase, owner first: `the X of the API`
    /// reads as `API X`, the same as `the API X`. The determiner is not
    /// part of the name.
    fn np_name(&mut self, np: &Np) {
        let Np { det, modifiers, head, of, relative, of_also, of_conj } = np;
        self.runs += 1;
        self.owner_first(of, of_also, of_conj);
        for (i, word) in modifiers.iter().enumerate() {
            if !misplaced_article(det, i, word) {
                self.name_word(word, Place::Modifier);
            }
        }
        self.name_word(head, Place::Head);
        self.runs += 1;
        if let Some(relative) = relative {
            self.relative(relative);
        }
    }

    fn owner_first(&mut self, of: &Option<Box<Np>>, of_also: &[Np], of_conj: &Option<Conj>) {
        let Some(owner) = of else { return };
        self.owner_words(owner);
        for owner in of_also {
            let run = self.runs;
            self.mark(Mark::Coordination, if *of_conj == Some(Conj::And) { "and" } else { "or" });
            self.runs = run;
            self.owner_words(owner);
        }
    }

    fn owner_words(&mut self, owner: &Np) {
        let Np { det, modifiers, head, of, relative, of_also, of_conj } = owner;
        match det {
            // The thing of each owner, of the owner, of an owner: the kind of thing that owners have.
            Some(Det::Reference { word }) if word != "another" => unread_node(word, "a pronoun", "that names no thing of its sentence"),
            None | Some(Det::The | Det::A | Det::An | Det::Each | Det::Every | Det::All | Det::Any | Det::Both | Det::Reference { .. }) => {}
            // `the choices of one response`: at least one owner is an owner.
            Some(Det::AtLeast { n: 1 } | Det::Cardinal { n: 1, .. } | Det::OneOrMore) => {}
            Some(Det::No) => unread_node("no", "a negation", "before the owner of a thing"),
            Some(Det::Some) => unread_node("some", "a quantifier", "before the owner of a thing"),
            Some(Det::AtLeast { .. } | Det::Cardinal { .. } | Det::AtMost { .. } | Det::Exactly { .. } | Det::ZeroOrMore) => unread_node(&det.as_ref().map(Det::render).unwrap_or_default(), "a count", "before the owner of a thing"),
        }
        self.owner_first(of, of_also, of_conj);
        for (i, word) in modifiers.iter().enumerate() {
            if !misplaced_article(det, i, word) {
                self.name_word(word, Place::Modifier);
            }
        }
        self.name_word(head, Place::Head);
        if let Some(relative) = relative {
            let run = self.runs;
            self.relative(relative);
            self.runs = run;
        }
    }

    fn group(&mut self, group: &NpGroup, position: Position) {
        match group {
            NpGroup::Single(np) => self.np(np, position),
            NpGroup::Coordinated { conj, marker, items } => {
                match marker {
                    Some(GroupMarker::Both) => self.mark(Mark::Group, "both"),
                    // A list that reaches a key is one name: the choice that `either` states is not read there.
                    Some(GroupMarker::Either) => self.rejected("either", "a quantifier", "before a list inside a name"),
                    None => {}
                }
                for (i, np) in items.iter().enumerate() {
                    if i > 0 && i + 1 == items.len() {
                        if items.len() > 2 {
                            self.comma();
                        }
                        self.mark(Mark::Coordination, conj.as_str());
                    } else if i > 0 {
                        self.comma();
                    }
                    self.np(np, position);
                }
            }
        }
    }

    fn relative(&mut self, relative: &Relative) {
        let Relative { marker, body, and } = relative;
        // The readings of a relative clause: a verbal or copular clause is
        // the difference of a restricted class; `whose` describes a part of
        // each member; `where` holds of each member; an object gap makes one
        // actor act on each member; `that` after a noun opens its content.
        let read = match (body, marker) {
            (RelativeBody::Verbal { .. } | RelativeBody::Copular { .. }, RelMarker::That | RelMarker::Who | RelMarker::Whose | RelMarker::Where) => true,
            (RelativeBody::ObjectGap { subject, .. }, RelMarker::That | RelMarker::Who | RelMarker::Where) => matches!(subject, NpGroup::Single(_)),
            (RelativeBody::ObjectGap { .. }, RelMarker::Whose) => false,
            (RelativeBody::Content { clause }, RelMarker::Whose) => matches!(&clause.subject, NpGroup::Single(part) if part.of.is_none()),
            (RelativeBody::Content { .. }, RelMarker::Where | RelMarker::That | RelMarker::Who) => true,
        };
        if read {
            self.mark(Mark::Relative, marker.as_str());
        } else {
            self.rejected(marker.as_str(), "a clause", "after a noun, in a form that no reading rule reads");
        }
        match body {
            RelativeBody::Content { clause } => self.clause(clause),
            RelativeBody::Copular { copula, predicate, agent, roles } => {
                self.mark(Mark::Copula, copula.as_str());
                self.predicate(predicate);
                if let Some(agent) = agent {
                    self.mark(Mark::Role, "by");
                    self.group(agent, Position::Argument);
                }
                roles.iter().for_each(|role| self.role(role));
            }
            RelativeBody::Verbal { verb, particle, manner, object, roles, negation } => {
                if let Some(negation) = negation {
                    self.mark(Mark::Negation, negation);
                }
                self.verb(verb, particle, manner);
                if let Some(object) = object {
                    self.group(object, Position::Argument);
                }
                roles.iter().for_each(|role| self.role(role));
            }
            RelativeBody::ObjectGap { subject, verb, particle, manner, roles } => {
                self.group(subject, Position::Argument);
                self.verb(verb, particle, manner);
                roles.iter().for_each(|role| self.role(role));
            }
        }
        if let Some(next) = and {
            self.mark(Mark::Coordination, "and");
            self.relative(next);
        }
    }

    fn verb(&mut self, verb: &str, particle: &Option<String>, manner: &[String]) {
        self.runs += 1;
        self.push(verb, Intent::Open(Place::Verb));
        if let Some(particle) = particle {
            self.push(particle, Intent::Mark(Mark::Role));
        }
        self.runs += 1;
        for word in manner {
            // `apply only to that item`: the phrase that an action is restricted to.
            if word.eq_ignore_ascii_case("only") && self.action {
                self.mark(Mark::Focus, "only");
            } else {
                self.push(word, Intent::Open(Place::Manner));
            }
        }
        self.runs += 1;
    }

    fn clause(&mut self, clause: &Clause) {
        let Clause { subject, body } = clause;
        let action = std::mem::replace(&mut self.action, false);
        self.group(subject, Position::Argument);
        match body {
            ClauseBody::Copular { copula, predicate, agent, roles } => {
                self.mark(Mark::Copula, copula.as_str());
                self.predicate(predicate);
                if let Some(agent) = agent {
                    self.mark(Mark::Role, "by");
                    self.group(agent, Position::Argument);
                }
                roles.iter().for_each(|role| self.role(role));
            }
            ClauseBody::Verbal { verb, particle, manner, object, roles, content, negation } => {
                if let Some(negation) = negation {
                    self.mark(Mark::Negation, negation);
                }
                self.verb(verb, particle, manner);
                if let Some(object) = object {
                    self.group(object, Position::Argument);
                }
                roles.iter().for_each(|role| self.role(role));
                if let Some(content) = content {
                    self.content(verb, content);
                }
            }
        }
        self.action = action;
    }

    fn predicate(&mut self, predicate: &Predicate) {
        match predicate {
            Predicate::Comparison(comparison) => self.comparison(comparison),
            Predicate::AbleTo { vp } => {
                self.mark(Mark::Ability, "able to");
                self.vp(vp);
            }
            Predicate::Pp { preposition, np } => {
                self.mark(Mark::Role, preposition);
                self.group(np, Position::Argument);
            }
            Predicate::Words { words } => self.predicate_words(words),
            Predicate::Enumeration { one_of, conj, values } => {
                if *one_of {
                    self.mark(Mark::Enumeration, "one of");
                }
                for (i, value) in values.iter().enumerate() {
                    if i > 0 {
                        self.mark(Mark::Coordination, conj.as_str());
                    }
                    self.runs += 1;
                    self.push(value, Intent::Open(Place::Value));
                    self.runs += 1;
                }
            }
        }
    }

    /// The words of a predicate. `not` and `never` deny it; `a`, `an`, `of`,
    /// `and` and `or` build the names of the classes that a nominal
    /// predicate lists.
    fn predicate_words(&mut self, words: &[String]) {
        let nominal = words.first().is_some_and(|w| matches!(w.to_lowercase().as_str(), "a" | "an" | "the"));
        self.runs += 1;
        for (i, word) in words.iter().enumerate() {
            let lower = word.to_lowercase();
            match lower.as_str() {
                "not" | "never" if i == 0 => {
                    let run = self.runs;
                    self.mark(Mark::Negation, word);
                    self.runs = run;
                }
                "of" if nominal => {
                    let run = self.runs;
                    self.mark(Mark::Role, word);
                    self.runs = run;
                }
                "and" | "or" if nominal => {
                    let run = self.runs;
                    self.mark(Mark::Coordination, word);
                    self.runs = run;
                }
                // `is a the user`: one article opens a noun phrase.
                "a" | "an" | "the" if i > 0 && crate::syntax::words::is_article(&words[i - 1]) => unread_node(word, "an article", "after the article of a noun phrase"),
                _ => self.push(word, Intent::Open(Place::Predicate)),
            }
        }
        self.runs += 1;
    }

    fn comparison(&mut self, comparison: &Comparison) {
        let Comparison { op, value, upper } = comparison;
        match (op, upper) {
            (ComparisonOp::Between, Some(upper)) => {
                self.mark(Mark::Comparison, "between");
                self.measure(value);
                self.mark(Mark::Comparison, "and");
                self.measure(upper);
            }
            (op, _) => {
                self.mark(Mark::Comparison, op.render());
                self.measure(value);
            }
        }
    }

    fn measure(&mut self, measure: &Measure) {
        match measure {
            Measure::Quantity { number, unit } => {
                self.mark(Mark::Measure, number);
                if let Some(unit) = unit {
                    self.mark(Mark::Measure, unit);
                }
            }
            Measure::Bounded { op, number, unit, upper } => {
                match (op, upper) {
                    (ComparisonOp::Between, Some(upper)) => {
                        self.mark(Mark::Comparison, "between");
                        self.mark(Mark::Measure, number);
                        self.mark(Mark::Comparison, "and");
                        self.mark(Mark::Measure, upper);
                    }
                    _ => {
                        self.mark(Mark::Comparison, op.render());
                        self.mark(Mark::Measure, number);
                    }
                }
                if let Some(unit) = unit {
                    self.mark(Mark::Measure, unit);
                }
            }
            Measure::Np { np } => self.group(np, Position::Argument),
        }
    }

    fn role(&mut self, role: &RolePp) {
        // `send a report to no user` denies the action: `no` in a role names no thing.
        let group = match role {
            RolePp::Recipient(np) | RolePp::Topic(np) | RolePp::Source(np) | RolePp::Goal(np) | RolePp::Agent(np) | RolePp::Means { np, .. } | RolePp::Location { np, .. } | RolePp::Other { np, .. } => Some(np),
            _ => None,
        };
        let denied = group.is_some_and(|group| match group {
            NpGroup::Single(np) => matches!(np.det, Some(Det::No)),
            NpGroup::Coordinated { items, .. } => items.iter().any(|np| matches!(np.det, Some(Det::No))),
        });
        if denied {
            unread_node("no", "a negation", "in a role of an action or of a state: deny the action before its verb, as in `shall not send a report to a user`");
        }
        match role {
            RolePp::Recipient(np) => {
                self.mark(Mark::Role, "to");
                self.group(np, Position::Argument);
            }
            RolePp::Means { marker, np } => {
                self.mark(Mark::Role, marker.as_str());
                self.group(np, Position::Argument);
            }
            RolePp::Topic(np) => {
                self.mark(Mark::Role, "about");
                self.group(np, Position::Argument);
            }
            RolePp::Deadline(measure) => {
                self.mark(Mark::Role, "within");
                self.measure(measure);
            }
            RolePp::Duration(measure) => {
                self.mark(Mark::Role, "for");
                self.measure(measure);
            }
            RolePp::Rate { unit } => {
                self.mark(Mark::Measure, "per");
                self.mark(Mark::Measure, unit);
            }
            RolePp::Before(clause) => {
                self.mark(Mark::Order, "before");
                self.clause(clause);
            }
            RolePp::After(clause) => {
                self.mark(Mark::Order, "after");
                self.clause(clause);
            }
            RolePp::Until(clause) => {
                self.mark(Mark::Order, "until");
                self.clause(clause);
            }
            RolePp::Source(np) => {
                self.mark(Mark::Role, "from");
                self.group(np, Position::Argument);
            }
            RolePp::Goal(np) => {
                self.mark(Mark::Role, "into");
                self.group(np, Position::Argument);
            }
            RolePp::Location { preposition, np } | RolePp::Other { preposition, np } => {
                let order = crate::syntax::words::is_order(preposition);
                self.mark(if order { Mark::Order } else { Mark::Role }, preposition);
                self.group(np, Position::Argument);
            }
            RolePp::Agent(np) => {
                self.mark(Mark::Role, "by");
                self.group(np, Position::Argument);
            }
        }
    }

    fn vp(&mut self, vp: &Vp) {
        let Vp { verb, particle, manner, object, roles, complement, content } = vp;
        self.verb(verb, particle, manner);
        if let Some(object) = object {
            self.group(object, Position::Argument);
        }
        if let Some(complement) = complement {
            self.predicate(complement);
        }
        roles.iter().for_each(|role| self.role(role));
        if let Some(content) = content {
            self.content(verb, content);
        }
    }

    /// The clause after `that`: the proposition that the action of a verb
    /// establishes or is about. A verb of neither class takes no clause.
    fn content(&mut self, verb: &str, content: &Clause) {
        if crate::syntax::words::content_class(&crate::reading::model::base_verb(&verb.to_lowercase())).is_some() {
            self.mark(Mark::Content, "that");
        } else {
            self.rejected("that", "a clause", "after a verb that takes no content clause");
        }
        self.clause(content);
    }

    /// The parts of the key: the lexicon names the declared terms, and each
    /// other word of an open place is a word of a name only when the lexer
    /// classes it as open.
    fn finish(self) -> Vec<Part> {
        let Emit { lex, toks, .. } = self;
        let phrases = phrases(&toks);
        // An article is no part of a key. A word standing alone is never dropped.
        let count = toks.len();
        let toks: Vec<Tok> = toks
            .into_iter()
            .enumerate()
            .filter(|(i, tok)| {
                let has_next = i + 1 < count;
                let open = matches!(tok.intent, Intent::Open(_) | Intent::Quoted);
                !(open && has_next && (matches!(tok.text.as_str(), "the" | "a" | "an") || (*i == 0 && matches!(tok.text.as_str(), "The" | "A" | "An"))))
            })
            .map(|(_, tok)| tok)
            .collect();
        let words: Vec<String> = toks.iter().map(|tok| tok.text.clone()).collect();
        let mut parts = Vec::new();
        let mut quoted = false;
        let mut last_run = usize::MAX;
        for (text, range, declared) in lex.canon_words(&words) {
            let first = &toks[range.start];
            if first.run != last_run {
                quoted = false;
                last_run = first.run;
            }
            let all_marks = toks[range.clone()].iter().all(|t| matches!(t.intent, Intent::Mark(_)));
            if declared && !all_marks {
                parts.push(Part { text, class: Class::Term, count: None, kind: false });
                continue;
            }
            match first.intent {
                Intent::Mark(mark) => parts.push(Part { text, class: Class::Mark(mark), count: first.count, kind: false }),
                Intent::Unread(_) => parts.push(Part { text, class: Class::Unread, count: None, kind: false }),
                Intent::Quoted => parts.push(Part { text, class: Class::Literal, count: None, kind: false }),
                Intent::Open(place) => {
                    // What stands between two quotes is no word of the sentence.
                    let quotes = first.text.matches(['"', '`']).count();
                    let inside = quoted;
                    if quotes % 2 == 1 {
                        quoted = !quoted;
                    }
                    if inside || quotes > 0 {
                        parts.push(Part { text, class: Class::Literal, count: None, kind: false });
                        continue;
                    }
                    let bare = first.text.trim_end_matches(',');
                    let phrase = &phrases[first.run.min(phrases.len().saturating_sub(1))];
                    // `the head's modal force`: the clitic names an owner, which a name does not hold.
                    if bare.ends_with("'s") || bare.ends_with("s'") {
                        report(Unread { part: bare.to_lowercase(), kind: "a possessive", place: "inside a name: write the owner after `of`, as in `the modal force of the head`", phrase: phrase.join(" ") });
                        parts.push(Part { text, class: Class::Unread, count: None, kind: false });
                        continue;
                    }
                    // `references available for the user`: a plural noun ends its noun
                    // phrase, so the words after it are no words of its name.
                    let continues = toks.get(range.end).is_some_and(|next| next.run == first.run && matches!(next.intent, Intent::Open(Place::Modifier | Place::Head)));
                    if place == Place::Modifier && continues && range.len() == 1 && classify(bare) == WordClass::Open && !bare.contains('\'') && crate::reading::lexicon::singular_by_ending(bare) != bare && !lex.in_declared_term(bare, phrase) {
                        report(Unread { part: bare.to_lowercase(), kind: "a plural noun", place: "before further words of a name: a noun phrase ends at its plural noun, so write what follows as a relative clause, as in `references that are available`", phrase: phrase.join(" ") });
                        parts.push(Part { text, class: Class::Unread, count: None, kind: false });
                        continue;
                    }
                    // `a specification assembled from files`: the head of a name is a noun,
                    // and the past participle of a known verb after a word of the name is
                    // a relative clause without its marker.
                    let follows = range.start > 0 && toks.get(range.start - 1).is_some_and(|before| before.run == first.run && matches!(before.intent, Intent::Open(Place::Modifier)));
                    if place == Place::Head && follows && !continues && range.len() == 1 && classify(bare) == WordClass::Open && past_participle_of_known_verb(bare, lex) && !lex.in_declared_term(bare, phrase) && !phrase.iter().any(|w| matches!(classify(w), WordClass::Closed(kind) if kind != Closed::Article)) {
                        report(Unread { part: bare.to_lowercase(), kind: "a past participle", place: "at the end of a name, where it is a relative clause without its marker: write `that is` before it, as in `a specification that is assembled from files`, or declare the phrase as a term", phrase: phrase.join(" ") });
                        parts.push(Part { text, class: Class::Unread, count: None, kind: false });
                        continue;
                    }
                    match classify(bare) {
                        WordClass::Open => parts.push(Part { text, class: Class::Word, count: None, kind: false }),
                        WordClass::Literal => parts.push(Part { text, class: Class::Literal, count: None, kind: false }),
                        // An article that nothing follows is a value by that name.
                        WordClass::Closed(Closed::Article) => parts.push(Part { text, class: Class::Literal, count: None, kind: false }),
                        WordClass::Closed(kind) if lex.in_declared_term(bare, phrase) => {
                            parts.push(Part { text, class: Class::Term, count: None, kind: kind == Closed::Adverb && place == Place::Modifier });
                        }
                        // A verb that the parser placed is the name of an action even where its spelling is an auxiliary.
                        WordClass::Closed(Closed::Auxiliary) if place == Place::Verb => parts.push(Part { text, class: Class::Mark(Mark::Copula), count: None, kind: false }),
                        WordClass::Closed(kind) => {
                            report(Unread { part: bare.to_lowercase(), kind: kind.describe(), place: place.describe(), phrase: phrase.join(" ") });
                            parts.push(Part { text, class: Class::Unread, count: None, kind: false });
                        }
                    }
                }
            }
        }
        parts
    }
}

/// `true` for an article among the modifiers of a noun phrase: it is no
/// word of the name. `all the files` and `both the files` are the files;
/// any other article directly after a determiner has no reading and is
/// reported.
fn misplaced_article(det: &Option<Det>, at: usize, word: &str) -> bool {
    // `no two steps`: the denial of a pair, which the reading of the subject counts.
    // A bare `two` is a determiner, so `two` as the first modifier is what `no two` left.
    if at == 0 && matches!(det, Some(Det::No) | None) && word.eq_ignore_ascii_case("two") {
        return true;
    }
    let article = matches!(word, "the" | "a" | "an" | "The" | "An");
    if article && at == 0 && !matches!(det, Some(Det::All | Det::Both)) {
        unread_node(word, "an article", "after the determiner of a noun phrase");
    } else if article && at > 0 {
        unread_node(word, "an article", "between two words of a name: the words before it are a phrase of their own, which the sentence must join with a verb, a preposition or a relative clause");
    }
    article
}

/// The words of each open run, by the index of the run.
fn phrases(toks: &[Tok]) -> Vec<Vec<String>> {
    let runs = toks.iter().map(|t| t.run).max().map_or(0, |m| m + 1);
    let mut out = vec![Vec::new(); runs];
    for tok in toks.iter().filter(|t| matches!(t.intent, Intent::Open(_))) {
        out[tok.run].push(tok.text.trim_end_matches(',').to_string());
    }
    out
}

fn named(lex: &Lexicon, build: impl FnOnce(&mut Emit)) -> Vec<Part> {
    let mut emit = Emit::new(lex);
    build(&mut emit);
    emit.finish()
}

/// The parts of the name of a noun phrase, owner first and without its determiner.
pub(super) fn np_parts(np: &Np, lex: &Lexicon) -> Vec<Part> {
    named(lex, |e| e.np_name(np))
}

/// The parts of an action: what a verb phrase names.
pub(super) fn action_parts(vp: &Vp, lex: &Lexicon) -> Vec<Part> {
    named(lex, |e| {
        e.action = true;
        e.vp(vp);
    })
}

/// The key of an action of a subject, registered with its parts.
pub(super) fn action(subject: &str, vp: &Vp, lex: &Lexicon) -> String {
    let parts = action_parts(vp, lex);
    let name = format!("{subject}|{}", text(&parts));
    register(&name, &parts);
    name
}

/// The parts of a clause: the key of an event or of a condition.
pub(super) fn clause_parts(clause: &Clause, lex: &Lexicon) -> Vec<Part> {
    named(lex, |e| e.clause(clause))
}

/// Registers the parts of an event under the text that the model keys it by.
pub(super) fn register_event(name: &str, parts: &[Part]) {
    register(name, parts);
}

/// The parts of a predicate with its agent and its roles: the value that a description states.
pub(super) fn value_parts(predicate: &Predicate, agent: Option<&NpGroup>, roles: &[RolePp], lex: &Lexicon) -> Vec<Part> {
    named(lex, |e| {
        // A comparison that reaches a value was not read as arithmetic: its
        // right side is no number and no quantity.
        if let Predicate::Comparison(comparison) = predicate {
            let op = match (&comparison.op, &comparison.upper) {
                (ComparisonOp::Between, Some(_)) => "between",
                (op, _) => op.render(),
            };
            unread_node(op, "a comparison", "that is no bound of one quantity");
        }
        e.predicate(predicate);
        if let Some(agent) = agent {
            e.mark(Mark::Role, "by");
            e.group(agent, Position::Argument);
        }
        roles.iter().for_each(|role| e.role(role));
    })
}

/// The parts of a relative clause, as a restricted class is keyed by it.
pub(super) fn relative_parts(relative: &Relative, lex: &Lexicon) -> Vec<Part> {
    named(lex, |e| e.relative(relative))
}

/// The parts of a noun phrase or of a list of them, as a sentence writes it.
pub(super) fn group_parts(group: &NpGroup, lex: &Lexicon) -> Vec<Part> {
    named(lex, |e| e.group(group, Position::Argument))
}

/// The parts of one declared value or of the words of one open place.
pub(super) fn word_parts(words: &[String], place: Place, lex: &Lexicon) -> Vec<Part> {
    named(lex, |e| {
        e.runs += 1;
        e.open(words, place);
    })
}

/// The parts of the words of a predicate.
pub(super) fn predicate_word_parts(words: &[String], lex: &Lexicon) -> Vec<Part> {
    named(lex, |e| e.predicate_words(words))
}

/// The parts of a value with the mark of its denial removed, and whether it was denied.
pub(super) fn denied_value(parts: Vec<Part>) -> (Vec<Part>, bool) {
    match parts.first() {
        Some(first) if first.mark() == Some(Mark::Negation) => (parts[1..].to_vec(), true),
        _ => (parts, false),
    }
}

/// The parts of an event whose subject the lexicon resolved to its owner:
/// the first `count` parts are the name of the subject.
pub(super) fn with_resolved_subject(parts: &[Part], count: usize, resolved: &str) -> Vec<Part> {
    let mut out = vec![Part { text: resolved.to_string(), class: Class::Term, count: None, kind: false }];
    out.extend(parts.iter().skip(count).cloned());
    out
}

/// The parts of a content clause: `that` and the clause that it opens.
pub(super) fn content_parts(clause: &Clause, lex: &Lexicon) -> Vec<Part> {
    named(lex, |e| {
        e.mark(Mark::Content, "that");
        e.clause(clause);
    })
}

/// The key of a composed response as one action of its subject: the kind of
/// the composition and the keys of its parts.
pub(super) fn composed(subject: &str, kind: &'static str, items: &[String]) -> String {
    let mut parts = vec![Part { text: kind.to_string(), class: Class::Mark(Mark::Group), count: None, kind: false }];
    parts.extend(items.iter().map(|item| Part { text: format!("({item})"), class: Class::Term, count: None, kind: false }));
    let name = format!("{subject}|{}", text(&parts));
    register(&name, &parts);
    name
}
