//! The account of a reading: which reading rules read a sentence, and which
//! words of it no rule read.
//!
//! The parser gives a sentence a tree. Some places of that tree are open:
//! the modifiers and the head of a noun phrase, the words of a predicate,
//! the manner of a verb. A word of an open place is a content word: it is
//! part of a name. A function word (a quantifier, a pronoun, a conjunction,
//! a preposition, an auxiliary, a negation, an adverb of time or of degree)
//! is never part of a name, so one that stands in an open place and reaches
//! the name of an atom was not read. Such a statement has no formal
//! interpretation as a whole and is rejected.

use crate::syntax::ast::*;
use std::collections::BTreeSet;

/// Where an open word stands.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Place {
    Modifier,
    Head,
    Predicate,
    Manner,
    Verb,
}

impl Place {
    pub(super) fn describe(self) -> &'static str {
        match self {
            Place::Modifier => "before the head of a noun phrase",
            Place::Head => "as the head of a noun phrase",
            Place::Predicate => "inside a predicate",
            Place::Manner => "as the manner of a verb",
            Place::Verb => "as a verb",
        }
    }
}

/// One word of an open place, with the phrase that it stands in.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Open {
    pub word: String,
    pub place: Place,
    pub phrase: String,
}

use crate::syntax::words::{classify, is_literal as literal, Closed, WordClass};

struct Walk {
    open: Vec<Open>,
    rules: BTreeSet<&'static str>,
}

impl Walk {
    fn words(&mut self, words: &[String], place: Place) {
        let phrase = words.join(" ");
        // A quoted literal may span several words: what stands between two quotes is no word.
        let mut inside = false;
        for raw in words {
            for w in raw.split_whitespace() {
                let quotes = w.matches(['"', '`']).count();
                let was_inside = inside;
                if quotes % 2 == 1 {
                    inside = !inside;
                }
                if was_inside || quotes > 0 || literal(w) {
                    continue;
                }
                self.open.push(Open { word: w.to_lowercase(), place, phrase: phrase.clone() });
            }
        }
    }

    /// A verb is a name of an action; a function word in its place was no verb.
    fn verb(&mut self, verb: &str) {
        if matches!(classify(verb), WordClass::Closed(kind) if kind != Closed::Auxiliary) {
            self.open.push(Open { word: verb.to_lowercase(), place: Place::Verb, phrase: verb.to_string() });
        }
    }

    fn np(&mut self, np: &Np) {
        self.rules.insert(match &np.det {
            None => "noun-phrase-bare",
            Some(Det::The | Det::A | Det::An) => "noun-phrase-article",
            Some(Det::Each | Det::Every | Det::All | Det::Any) => "noun-phrase-universal",
            Some(Det::No) => "noun-phrase-none",
            Some(Det::Some) => "noun-phrase-existential",
            Some(Det::AtLeast { .. } | Det::Cardinal { .. } | Det::AtMost { .. } | Det::Exactly { .. } | Det::ZeroOrMore | Det::OneOrMore | Det::Both) => "noun-phrase-counted",
            Some(Det::Reference { .. }) => "noun-phrase-reference",
        });
        if !np.modifiers.is_empty() {
            self.rules.insert("noun-phrase-modified");
            if np.modifiers.iter().any(|m| matches!(classify(m), WordClass::Closed(Closed::Adverb))) {
                self.rules.insert("noun-phrase-kind-word");
            }
        }
        // The modifiers and the head are one phrase: a declared term may hold any word.
        let from = self.open.len();
        // `no two steps`: the denial of a pair, which the reading of the subject counts.
        let pair = matches!(np.det, Some(Det::No) | None) && np.modifiers.first().is_some_and(|m| m.eq_ignore_ascii_case("two"));
        self.words(&np.modifiers[usize::from(pair)..], Place::Modifier);
        self.words(std::slice::from_ref(&np.head), Place::Head);
        let phrase = np.modifiers.iter().chain(std::iter::once(&np.head)).cloned().collect::<Vec<_>>().join(" ");
        // `another room` tells this room from one that was named: the
        // determiner is no article and no count.
        if let Some(Det::Reference { word }) = &np.det {
            if word.eq_ignore_ascii_case("another") {
                self.open.push(Open { word: "another".to_string(), place: Place::Modifier, phrase: String::new() });
            }
        }
        self.open[from..].iter_mut().for_each(|open| open.phrase = phrase.clone());
        if let Some(of) = &np.of {
            self.rules.insert("noun-phrase-of");
            self.np(of);
        }
        np.of_also.iter().for_each(|n| self.np(n));
        let mut relative = np.relative.as_deref();
        while let Some(r) = relative {
            match &r.body {
                RelativeBody::Content { clause } => {
                    self.rules.insert(match r.marker {
                        RelMarker::Whose => "relative-whose",
                        RelMarker::Where => "relative-where",
                        RelMarker::That | RelMarker::Who => "content-of-noun",
                    });
                    self.clause(clause);
                }
                RelativeBody::Copular { predicate, agent, roles, .. } => {
                    self.rules.insert("relative-copular");
                    self.predicate(predicate);
                    agent.iter().for_each(|g| self.group(g));
                    self.roles(roles);
                }
                RelativeBody::Verbal { verb, manner, object, roles, negation, .. } => {
                    self.verb(verb);
                    self.rules.insert(if negation.is_some() { "relative-verbal-denied" } else { "relative-verbal" });
                    self.words(manner, Place::Manner);
                    object.iter().for_each(|g| self.group(g));
                    self.roles(roles);
                }
                RelativeBody::ObjectGap { subject, verb, manner, roles, .. } => {
                    self.verb(verb);
                    self.rules.insert("relative-object-gap");
                    self.group(subject);
                    self.words(manner, Place::Manner);
                    self.roles(roles);
                }
            }
            relative = r.and.as_deref();
        }
    }

    fn group(&mut self, g: &NpGroup) {
        match g {
            NpGroup::Single(n) => self.np(n),
            NpGroup::Coordinated { items, conj, .. } => {
                self.rules.insert(if *conj == Conj::And { "noun-phrases-and" } else { "noun-phrases-or" });
                items.iter().for_each(|n| self.np(n));
            }
        }
    }

    fn measure(&mut self, m: &Measure) {
        match m {
            Measure::Quantity { .. } => {
                self.rules.insert("measure-quantity");
            }
            Measure::Bounded { .. } => {
                self.rules.insert("measure-bounded");
            }
            Measure::Np { np } => {
                self.rules.insert("measure-named");
                self.group(np);
            }
        }
    }

    fn predicate(&mut self, p: &Predicate) {
        match p {
            Predicate::Comparison(c) => {
                self.rules.insert("predicate-comparison");
                self.measure(&c.value);
                c.upper.iter().for_each(|m| self.measure(m));
            }
            Predicate::AbleTo { vp } => {
                self.rules.insert("predicate-able-to");
                self.vp(vp);
            }
            Predicate::Pp { np, .. } => {
                self.rules.insert("predicate-prepositional");
                self.group(np);
            }
            // `is a part of a qualified name`, `is a verb phrase or a nested
            // action list`: the predicate names classes; `of`, `or` and
            // `and` build those names and join them.
            Predicate::Words { words } if words.first().is_some_and(|w| crate::syntax::words::is_article(w)) => {
                self.rules.insert("predicate-nominal");
                let content: Vec<String> = words.iter().filter(|w| !crate::syntax::words::builds_nominal(w)).cloned().collect();
                self.words(&content, Place::Predicate);
            }
            Predicate::Words { words } => {
                self.rules.insert("predicate-words");
                self.words(words, Place::Predicate);
            }
            Predicate::Enumeration { .. } => {
                self.rules.insert("predicate-enumeration");
            }
        }
    }

    /// The roles of one verb or predicate. `within 5 seconds of the last
    /// retry`: the phrase after a deadline names its origin, and `last`
    /// there selects the last occurrence of the event.
    fn roles(&mut self, roles: &[RolePp]) {
        let mut deadline = false;
        for role in roles {
            match role {
                RolePp::Deadline(_) => deadline = true,
                RolePp::Other { preposition, np: NpGroup::Single(np) } if deadline && preposition.eq_ignore_ascii_case("of") => {
                    self.rules.insert("deadline-origin");
                    let mut origin = np.clone();
                    origin.modifiers.retain(|w| !crate::syntax::words::selects_last(w));
                    self.np(&origin);
                    continue;
                }
                RolePp::Recipient(_) | RolePp::Means { .. } | RolePp::Topic(_) | RolePp::Duration(_) | RolePp::Rate { .. } | RolePp::Before(_) | RolePp::After(_) | RolePp::Until(_) | RolePp::Source(_) | RolePp::Goal(_) | RolePp::Location { .. } | RolePp::Other { .. } | RolePp::Agent(_) => {}
            }
            self.role(role);
        }
    }

    fn role(&mut self, r: &RolePp) {
        match r {
            RolePp::Before(c) | RolePp::After(c) | RolePp::Until(c) => {
                self.rules.insert(if matches!(r, RolePp::Before(_)) {
                    "role-before"
                } else if matches!(r, RolePp::After(_)) {
                    "role-after"
                } else {
                    "role-until"
                });
                self.clause(c);
            }
            RolePp::Deadline(m) => {
                self.rules.insert("role-deadline");
                self.measure(m);
            }
            RolePp::Duration(m) => {
                self.rules.insert("role-duration");
                self.measure(m);
            }
            RolePp::Rate { .. } => {
                self.rules.insert("role-rate");
            }
            // `twice in a row` says that the occurrences follow each other;
            // a place named `row` does not say it.
            RolePp::Location { np: NpGroup::Single(np), .. } if np.head.eq_ignore_ascii_case("row") && np.modifiers.is_empty() && np.of.is_none() => {
                self.rules.insert("occurrences-in-a-row");
                self.open.push(Open { word: "consecutively".to_string(), place: Place::Manner, phrase: "in a row".to_string() });
            }
            // `at least 2 seconds after …`, `before the first retry`: the
            // temporal shape reads the bound and the order of the occurrence.
            RolePp::Other { preposition, np } if crate::reading::temporal::is_time_role(r) => {
                self.rules.insert(if ["before", "after"].contains(&preposition.as_str()) { "order-of-occurrence" } else { "role-delay" });
                if ["before", "after"].contains(&preposition.as_str()) {
                    self.group(np);
                }
            }
            other => {
                self.rules.insert(match other {
                    RolePp::Recipient(_) => "role-recipient",
                    RolePp::Means { .. } => "role-means",
                    RolePp::Topic(_) => "role-topic",
                    RolePp::Source(_) => "role-source",
                    RolePp::Goal(_) => "role-goal",
                    RolePp::Location { .. } => "role-location",
                    RolePp::Agent(_) => "role-agent",
                    RolePp::Other { .. } => "role-other",
                    RolePp::Deadline(_) | RolePp::Duration(_) | RolePp::Rate { .. } | RolePp::Before(_) | RolePp::After(_) | RolePp::Until(_) => "role-other",
                });
                crate::reading::model::role_nps(other).into_iter().for_each(|n| self.np(n));
            }
        }
    }

    fn clause(&mut self, c: &Clause) {
        self.group(&c.subject);
        match &c.body {
            ClauseBody::Copular { predicate, agent, roles, .. } => {
                self.rules.insert("clause-copular");
                self.predicate(predicate);
                agent.iter().for_each(|g| self.group(g));
                self.roles(roles);
            }
            ClauseBody::Verbal { verb, manner, object, roles, content, negation, .. } => {
                self.verb(verb);
                self.rules.insert(if negation.is_some() { "clause-verbal-denied" } else { "clause-verbal" });
                self.words(manner, Place::Manner);
                object.iter().for_each(|g| self.group(g));
                self.roles(roles);
                if let Some(c) = content {
                    self.rules.insert("content-of-verb");
                    self.clause(c);
                }
            }
        }
    }

    fn clauses(&mut self, g: &ClauseGroup) {
        if let Some(conj) = g.conj {
            self.rules.insert(if conj == Conj::And { "clauses-and" } else { "clauses-or" });
        }
        g.items.iter().for_each(|c| self.clause(c));
    }

    fn vp(&mut self, v: &Vp) {
        self.verb(&v.verb);
        self.rules.insert(if v.verb.eq_ignore_ascii_case("be") { "action-passive-or-state" } else { "action" });
        self.words(&v.manner, Place::Manner);
        for word in &v.manner {
            match word.to_ascii_lowercase().as_str() {
                "immediately" => self.rules.insert("timing-immediately"),
                "always" => self.rules.insert("timing-always"),
                "eventually" => self.rules.insert("timing-eventually"),
                _ => false,
            };
        }
        v.object.iter().for_each(|g| self.group(g));
        self.roles(&v.roles);
        v.complement.iter().for_each(|p| self.predicate(p));
        if let Some(c) = &v.content {
            use crate::syntax::words::{content_class, ContentClass};
            self.rules.insert(match content_class(&crate::reading::model::base_verb(&v.verb.to_lowercase())) {
                Some(ContentClass::Establishing) => "content-established",
                Some(ContentClass::Permitting) => "content-permitted",
                Some(ContentClass::Requiring) => "content-required",
                Some(ContentClass::Reporting) | None => "content-of-verb",
            });
            self.clause(c);
        }
    }

    fn node(&mut self, node: &CompNode) {
        match node {
            CompNode::Leaf { exception, .. } => {
                if let Some(c) = exception {
                    self.rules.insert("exception-unless");
                    self.clause(c);
                }
            }
            CompNode::All { items } => {
                self.rules.insert("composition-all");
                items.iter().for_each(|n| self.node(n));
            }
            CompNode::Some { items } => {
                self.rules.insert("composition-some");
                items.iter().for_each(|n| self.node(n));
            }
            CompNode::One { items } => {
                self.rules.insert("composition-one");
                items.iter().for_each(|n| self.node(n));
            }
            CompNode::Sequence { items } => {
                self.rules.insert("composition-sequence");
                items.iter().for_each(|n| self.node(n));
            }
            CompNode::Flow(flow) => {
                self.rules.insert("composition-flow");
                flow.steps.iter().for_each(|s| self.node(&s.node));
                for choice in &flow.choices {
                    self.rules.insert("flow-choice");
                    choice.arms.iter().for_each(|(guard, _)| self.clauses(guard));
                }
            }
        }
    }

    fn vps(&mut self, vp: &VpGroup) {
        match vp {
            VpGroup::Single(_) => {}
            VpGroup::Alternatives { .. } => {
                self.rules.insert("actions-either");
            }
            VpGroup::All { .. } => {
                self.rules.insert("actions-and");
            }
            VpGroup::Composite(c) => self.node(&c.root),
        }
        vp.items().iter().for_each(|v| self.vp(v));
    }

    fn core(&mut self, core: &Core) {
        match core {
            Core::Definition { term, definiens } => {
                self.rules.insert("definition");
                self.np(term);
                match definiens {
                    Definiens::Np { np, roles } => {
                        self.group(np);
                        self.roles(roles);
                    }
                    Definiens::Clause(c) => self.clause(c),
                }
            }
            Core::Description { subject, adverb, predicate, agent, roles, .. } => {
                self.rules.insert(if adverb.is_some() { "description-adverb" } else { "description" });
                self.group(subject);
                self.predicate(predicate);
                agent.iter().for_each(|g| self.group(g));
                self.roles(roles);
            }
            Core::Deontic { subject, modal, negated, vp } => {
                self.rules.insert(match (modal.as_str(), negated) {
                    ("shall" | "must", false) => "obligation",
                    ("shall" | "must", true) => "prohibition",
                    ("should", false) => "recommendation",
                    ("should", true) => "recommendation-against",
                    (_, false) => "permission",
                    (_, true) => "permission-denied",
                });
                self.group(subject);
                self.vps(vp);
            }
            Core::Relation { subject, vp } => {
                self.rules.insert("relation");
                self.group(subject);
                self.vps(vp);
            }
            Core::Existence { subject } => {
                self.rules.insert("existence");
                self.group(subject);
            }
            Core::Conjoined { items } => {
                self.rules.insert("statements-and");
                items.iter().for_each(|c| self.core(c));
            }
        }
    }

    fn sentence(&mut self, s: &Sentence) {
        for frame in &s.frames.scopes {
            self.rules.insert("frame-where");
            self.clauses(&frame.clause);
        }
        for frame in &s.frames.states {
            self.rules.insert("frame-while");
            self.clauses(&frame.clause);
        }
        if let Some(trigger) = &s.frames.trigger {
            self.rules.insert(match trigger.kind {
                TriggerKind::Event => "frame-when",
                TriggerKind::Contingency => "frame-if",
            });
            self.clauses(&trigger.clause);
        }
        if let Some(c) = &s.exception {
            self.rules.insert("exception-unless");
            self.clause(c);
        }
        if let Some(g) = &s.necessary {
            self.rules.insert("condition-only-if");
            self.clauses(g);
        }
        if let Some(g) = &s.iff {
            self.rules.insert("condition-if-and-only-if");
            self.clauses(g);
        }
        match &s.purpose {
            Some(Purpose::SoThat(c)) => {
                self.rules.insert("purpose");
                self.clause(c);
            }
            Some(Purpose::InOrderTo(v)) => {
                self.rules.insert("purpose");
                self.vp(v);
            }
            None => {}
        }
        self.core(&s.core);
    }
}

/// The names of the reading rules that read a sentence.
pub fn rules(sentence: &Sentence) -> Vec<&'static str> {
    let mut walk = Walk { open: Vec::new(), rules: BTreeSet::new() };
    walk.sentence(sentence);
    walk.rules.into_iter().collect()
}

/// The words of the open places of a sentence.
pub(super) fn open_words(sentence: &Sentence) -> Vec<Open> {
    let mut walk = Walk { open: Vec::new(), rules: BTreeSet::new() };
    walk.sentence(sentence);
    walk.open.sort();
    walk.open.dedup();
    walk.open
}

/// The entry that a reading example compares: the contract and the temporal
/// shape of each statement of the input, and the background axioms that the
/// input gives rise to beside those of the package (`baseline`).
pub fn entry_lines(model: &crate::reading::model::Model, baseline: &crate::reading::model::Model, ids: &BTreeSet<String>) -> Vec<String> {
    let mut lines = Vec::new();
    for constraint in &model.constraints {
        let Some(at) = constraint.refs.first() else { continue };
        if !ids.contains(&at.id) {
            continue;
        }
        lines.push(format!("assume: {}", constraint.assume));
        lines.push(format!("guarantee: {}", constraint.guarantee));
        if matches!(constraint.kind, crate::reading::model::ConstraintKind::Spec | crate::reading::model::ConstraintKind::Permission) {
            for obligation in model.temporal.iter().filter(|o| o.statement.id == at.id) {
                lines.extend(obligation.lines().into_iter().map(|line| format!("temporal: {line}")));
            }
        }
    }
    let known: BTreeSet<String> = baseline.background.iter().map(|f| f.to_string()).collect();
    let mut seen = BTreeSet::new();
    for axiom in &model.background {
        let text = axiom.to_string();
        if !known.contains(&text) && seen.insert(text.clone()) {
            lines.push(format!("axiom: {text}"));
        }
    }
    lines
}
