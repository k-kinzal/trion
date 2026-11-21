//! The text of a statement against the tree that the parser made of it.
//!
//! The reading of a statement starts from its tree, and the tree is the
//! work of the parser. This module reads the text of a statement a second
//! time, by a small grammar of its own that knows the closed words of the
//! language and the nouns that the package declares, and compares what it
//! finds with the tree: which words are the noun phrases, which word is the
//! verb, where a condition ends and what belongs to a relative clause.
//!
//! The grammar covers the plain statements about individuals: frames,
//! clauses with a copula or a verb, a subject with a modal verb and its
//! actions with their roles, a description, `has` with a count, and
//! `unless`. Where the text is outside this grammar the statement is not
//! read here ([`Read::NotRead`]), and the result says so; where the grammar
//! reads the text and the tree says something else, the tree is refused
//! ([`Read::Differs`]).
//!
//! The two sides meet in one written form: a noun phrase is `<det ordinals
//! head of <owner>>`, a clause `(subject is predicate)` or `(subject verb
//! object roles)`, a frame `while{clause and clause}`.

use std::collections::BTreeSet;
use trion_language::reading::typed::{DomainFact, Nominal};
use trion_language::syntax::ast::*;

/// What the second reading of the text of a statement found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Read {
    /// The grammar reads the text as the tree says.
    Agrees,
    /// The grammar reads the text, and the tree says something else.
    Differs { text: String, tree: String },
    /// The text or the tree holds a form outside this grammar.
    NotRead(String),
}

const ARTICLES: [&str; 3] = ["a", "an", "the"];
const DETERMINERS: [&str; 8] = ["a", "an", "the", "each", "every", "any", "no", "all"];
const ORDINALS: [&str; 6] = ["second", "third", "fourth", "fifth", "sixth", "other"];
const MODALS: [&str; 4] = ["shall", "must", "should", "may"];
const FRAMES: [&str; 8] = ["where", "while", "when", "if", "after", "once", "upon", "on"];
const PREPOSITIONS: [&str; 11] = ["to", "from", "about", "into", "by", "via", "with", "in", "at", "on", "of"];
const NUMBERS: [&str; 12] = ["one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve"];

fn singular(word: &str) -> String {
    if let Some(stem) = word.strip_suffix("ies") {
        return format!("{stem}y");
    }
    if ["sses", "shes", "ches", "xes", "zes"].iter().any(|ending| word.ends_with(ending)) {
        return word[..word.len() - 2].to_string();
    }
    if word.ends_with("ss") || word.ends_with("us") || word.ends_with("is") {
        return word.to_string();
    }
    word.strip_suffix('s').unwrap_or(word).to_string()
}

// ---- the tree, written out -------------------------------------------------

fn det_of(det: &Det) -> Option<String> {
    Some(match det {
        Det::The => "the".to_string(),
        Det::A => "a".to_string(),
        Det::An => "an".to_string(),
        Det::Each => "each".to_string(),
        Det::Every => "every".to_string(),
        Det::Any => "any".to_string(),
        Det::No => "no".to_string(),
        Det::All => "all".to_string(),
        Det::Cardinal { n, .. } => n.to_string(),
        Det::AtLeast { n } => format!("at least {n}"),
        Det::AtMost { n } => format!("at most {n}"),
        Det::Exactly { n } => format!("exactly {n}"),
        _ => return None,
    })
}

fn np_of(np: &Np) -> Option<String> {
    if !np.of_also.is_empty() {
        return None;
    }
    let mut words: Vec<String> = Vec::new();
    if let Some(det) = &np.det {
        words.push(det_of(det)?);
    }
    words.extend(np.modifiers.iter().map(|m| m.to_lowercase()));
    words.push(np.head.to_lowercase());
    let mut out = format!("<{}", words.join(" "));
    if let Some(owner) = &np.of {
        out.push_str(&format!(" of {}", np_of(owner)?));
    }
    if let Some(relative) = &np.relative {
        if relative.and.is_some() {
            return None;
        }
        let body = match &relative.body {
            RelativeBody::Copular { copula, predicate, agent: None, roles } => format!("{} {}", copula.as_str(), predicate_of(predicate, roles)?),
            RelativeBody::Verbal { verb, particle: None, manner, object, roles, negation } if manner.is_empty() => verbal_of(None, negation.as_deref(), verb, object.as_ref(), roles)?,
            RelativeBody::ObjectGap { subject, verb, particle: None, manner, roles } if manner.is_empty() => verbal_of(Some(subject), None, verb, None, roles)?,
            RelativeBody::Content { clause } if relative.marker == RelMarker::Whose => clause_of(clause)?,
            _ => return None,
        };
        out.push_str(&format!(" {}({body})", relative.marker.as_str()));
    }
    out.push('>');
    Some(out)
}

fn group_of(group: &NpGroup) -> Option<String> {
    match group {
        NpGroup::Single(np) => np_of(np),
        NpGroup::Coordinated { .. } => None,
    }
}

/// The words of a noun phrase without brackets, as a predicate holds them.
fn flat_np(np: &Np) -> Option<String> {
    if np.relative.is_some() || !np.of_also.is_empty() {
        return None;
    }
    let mut words: Vec<String> = Vec::new();
    if let Some(det) = &np.det {
        words.push(det_of(det)?);
    }
    words.extend(np.modifiers.iter().map(|m| m.to_lowercase()));
    words.push(np.head.to_lowercase());
    if let Some(owner) = &np.of {
        words.push("of".to_string());
        words.push(flat_np(owner)?);
    }
    Some(words.join(" "))
}

fn predicate_of(predicate: &Predicate, roles: &[RolePp]) -> Option<String> {
    let mut words: Vec<String> = match predicate {
        Predicate::Words { words, .. } => words.iter().map(|w| number(&w.to_lowercase())).collect(),
        Predicate::Enumeration { values, conj, .. } => vec![values.iter().map(|v| v.to_lowercase()).collect::<Vec<_>>().join(if *conj == Conj::Or { " or " } else { " and " })],
        _ => return None,
    };
    for role in roles {
        let RolePp::Other { preposition, np: NpGroup::Single(np) } = role else { return None };
        words.push(preposition.to_lowercase());
        words.push(flat_np(np)?);
    }
    Some(words.join(" "))
}

fn role_of(role: &RolePp) -> Option<String> {
    let named = |marker: &str, group: &NpGroup| Some(format!("{marker} {}", group_of(group)?));
    match role {
        RolePp::Recipient(g) => named("to", g),
        RolePp::Topic(g) => named("about", g),
        RolePp::Source(g) => named("from", g),
        RolePp::Goal(g) => named("into", g),
        RolePp::Agent(g) => named("by", g),
        RolePp::Means { marker, np } => named(marker.as_str(), np),
        RolePp::Location { preposition, np } | RolePp::Other { preposition, np } => named(&preposition.to_lowercase(), np),
        RolePp::Deadline(measure) => Some(format!("within {}", measure_of(measure)?)),
        RolePp::Duration(measure) => Some(format!("for {}", measure_of(measure)?)),
        RolePp::Before(clause) => Some(format!("before {}", clause_of(clause)?)),
        RolePp::After(clause) => Some(format!("after {}", clause_of(clause)?)),
        RolePp::Until(_) | RolePp::Rate { .. } => None,
    }
}

fn measure_of(measure: &Measure) -> Option<String> {
    match measure {
        Measure::Quantity { number, unit: Some(unit) } => Some(format!("{number} {}", unit.to_lowercase())),
        Measure::Bounded { op, number, unit: Some(unit), upper: None } => {
            let bound = match op {
                ComparisonOp::AtLeast => "at least",
                ComparisonOp::AtMost => "at most",
                ComparisonOp::GreaterThan => "more than",
                ComparisonOp::LessThan => "less than",
                _ => return None,
            };
            Some(format!("{bound} {number} {}", unit.to_lowercase()))
        }
        _ => None,
    }
}

fn verbal_of(subject: Option<&NpGroup>, negation: Option<&str>, verb: &str, object: Option<&NpGroup>, roles: &[RolePp]) -> Option<String> {
    let mut parts: Vec<String> = Vec::new();
    if let Some(subject) = subject {
        parts.push(group_of(subject)?);
    }
    if let Some(negation) = negation {
        parts.push(negation.to_lowercase());
    }
    parts.push(verb.to_lowercase());
    if let Some(object) = object {
        parts.push(group_of(object)?);
    }
    for role in roles {
        parts.push(role_of(role)?);
    }
    Some(parts.join(" "))
}

fn clause_of(clause: &Clause) -> Option<String> {
    Some(match &clause.body {
        ClauseBody::Copular { copula, predicate, agent: None, roles } => format!("({} {} {})", group_of(&clause.subject)?, copula.as_str(), predicate_of(predicate, roles)?),
        ClauseBody::Verbal { verb, particle: None, manner, object, roles, content: None, negation } if manner.is_empty() => format!("({})", verbal_of(Some(&clause.subject), negation.as_deref(), verb, object.as_ref(), roles)?),
        _ => return None,
    })
}

fn clauses_of(keyword: &str, group: &ClauseGroup) -> Option<String> {
    let clauses = group.items.iter().map(clause_of).collect::<Option<Vec<_>>>()?;
    Some(format!("{}{{{}}}", keyword.to_lowercase(), clauses.join(if group.conj == Some(Conj::Or) { " or " } else { " and " })))
}

fn vp_of(vp: &Vp) -> Option<String> {
    if vp.particle.is_some() || !vp.manner.is_empty() || vp.complement.is_some() || vp.content.is_some() {
        return None;
    }
    verbal_of(None, None, &vp.verb, vp.object.as_ref(), &vp.roles)
}

/// The tree of a sentence in the written form of this module; `None` for a
/// tree with a form outside the grammar.
fn tree(sentence: &Sentence) -> Option<String> {
    if sentence.purpose.is_some() || sentence.necessary.is_some() || sentence.iff.is_some() || sentence.concession.is_some() {
        return None;
    }
    let mut parts: Vec<String> = Vec::new();
    for frame in sentence.frames.scopes.iter().chain(&sentence.frames.states) {
        parts.push(clauses_of(&frame.keyword, &frame.clause)?);
    }
    if let Some(trigger) = &sentence.frames.trigger {
        parts.push(clauses_of(&trigger.keyword, &trigger.clause)?);
    }
    parts.push(match &sentence.core {
        Core::Deontic { subject, modal, negated, vp } => {
            let actions = match vp {
                VpGroup::Single(vp) => vp_of(vp)?,
                VpGroup::Alternatives { items } => format!("either {}", items.iter().map(vp_of).collect::<Option<Vec<_>>>()?.join(" or ")),
                VpGroup::All { items, negated } if negated.iter().all(|n| !n) => items.iter().map(vp_of).collect::<Option<Vec<_>>>()?.join(" and "),
                _ => return None,
            };
            format!("{} {}{} {actions}", group_of(subject)?, modal.as_str(), if *negated { " not" } else { "" })
        }
        Core::Description { subject, copula, adverb, predicate, agent: None, roles } => {
            let adverb = match adverb {
                Some(DescriptionAdverb::Never) => " never",
                Some(DescriptionAdverb::Always) => " always",
                None => "",
            };
            format!("{} {}{adverb} {}", group_of(subject)?, copula.as_str(), predicate_of(predicate, roles)?)
        }
        Core::Relation { subject, vp: VpGroup::Single(vp) } => format!("{} {}", group_of(subject)?, vp_of(vp)?),
        _ => return None,
    });
    if let Some(exception) = &sentence.exception {
        parts.push(format!("unless {}", clause_of(exception)?));
    }
    Some(parts.join(" "))
}

// ---- the text, read by the grammar -----------------------------------------

fn number(word: &str) -> String {
    match NUMBERS.iter().position(|n| *n == word) {
        Some(at) => (at + 1).to_string(),
        None => word.to_string(),
    }
}

struct Reader<'a> {
    words: Vec<String>,
    at: usize,
    nouns: &'a BTreeSet<String>,
}

type Found<T> = Result<T, String>;

impl Reader<'_> {
    fn peek(&self) -> &str {
        self.words.get(self.at).map_or("", String::as_str)
    }

    fn ahead(&self, by: usize) -> &str {
        self.words.get(self.at + by).map_or("", String::as_str)
    }

    fn take(&mut self) -> String {
        let word = self.peek().to_string();
        self.at += 1;
        word
    }

    fn expect(&mut self, word: &str) -> Found<()> {
        if self.peek() == word {
            self.at += 1;
            Ok(())
        } else {
            Err(format!("`{word}` is expected where `{}` stands", self.peek()))
        }
    }

    fn is_noun(&self, word: &str) -> bool {
        self.nouns.contains(word) || self.nouns.contains(&singular(word))
    }

    fn is_number(word: &str) -> bool {
        !word.is_empty() && word.chars().all(|c| c.is_ascii_digit())
    }

    /// `true` where a determiner, a count or a declared noun opens a noun phrase.
    fn opens_np(&self) -> bool {
        let word = self.peek();
        DETERMINERS.contains(&word) || Self::is_number(word) || (["at", "exactly"].contains(&word) && (["least", "most"].contains(&self.ahead(1)) || Self::is_number(self.ahead(1)))) || self.is_noun(word)
    }

    /// The words of a noun phrase: determiner or count, ordinals and noun.
    fn np_words(&mut self) -> Found<Vec<String>> {
        let mut words: Vec<String> = Vec::new();
        let first = self.peek().to_string();
        if DETERMINERS.contains(&first.as_str()) || Self::is_number(&first) {
            words.push(self.take());
        } else if first == "at" && ["least", "most"].contains(&self.ahead(1)) && Self::is_number(self.ahead(2)) {
            let bound = [self.take(), self.take(), self.take()].join(" ");
            words.push(bound);
        } else if first == "exactly" && Self::is_number(self.ahead(1)) {
            let bound = [self.take(), self.take()].join(" ");
            words.push(bound);
        }
        while ORDINALS.contains(&self.peek()) {
            words.push(self.take());
        }
        if !self.is_noun(self.peek()) {
            return Err(format!("`{}` is no noun that the package declares", self.peek()));
        }
        words.push(self.take());
        Ok(words)
    }

    fn np(&mut self) -> Found<String> {
        let words = self.np_words()?;
        let mut out = format!("<{}", words.join(" "));
        if self.peek() == "of" {
            self.at += 1;
            out.push_str(&format!(" of {}", self.np()?));
        } else if ["that", "who", "whose"].contains(&self.peek()) {
            let marker = self.take();
            let body = if marker == "whose" {
                let property = self.np()?;
                let copula = self.take();
                if !["is", "are"].contains(&copula.as_str()) {
                    return Err("`whose` without a copula".to_string());
                }
                format!("({property} {copula} {})", self.predicate(true)?)
            } else if ["is", "are"].contains(&self.peek()) {
                let copula = self.take();
                format!("{copula} {}", self.predicate(true)?)
            } else if self.opens_np() {
                // The noun is the object of the clause: `that the gateway forwards`.
                let subject = self.np()?;
                let verb = self.verb()?;
                self.joined(vec![subject, verb], false)?
            } else {
                let mut parts = Vec::new();
                if ["does", "do"].contains(&self.peek()) && self.ahead(1) == "not" {
                    parts.push([self.take(), self.take()].join(" "));
                }
                parts.push(self.verb()?);
                if self.opens_np() {
                    parts.push(self.np()?);
                }
                self.joined(parts, false)?
            };
            out.push_str(&format!(" {marker}({body})"));
        }
        out.push('>');
        Ok(out)
    }

    fn flat_np(&mut self) -> Found<String> {
        let mut words = self.np_words()?;
        if self.peek() == "of" {
            self.at += 1;
            words.push("of".to_string());
            words.push(self.flat_np()?);
        }
        Ok(words.join(" "))
    }

    fn verb(&mut self) -> Found<String> {
        let word = self.peek().to_string();
        let closed = DETERMINERS.contains(&word.as_str()) || MODALS.contains(&word.as_str()) || PREPOSITIONS.contains(&word.as_str()) || [",", ".", "and", "or", "not", "is", "are", "unless", "within", "for", "before", "after", ""].contains(&word.as_str());
        if closed || self.is_noun(&word) || Self::is_number(&word) {
            return Err(format!("`{word}` stands where a verb is expected"));
        }
        self.at += 1;
        Ok(word)
    }

    /// The roles after a verb and its object, joined to what stands before them.
    fn joined(&mut self, mut parts: Vec<String>, of_an_action: bool) -> Found<String> {
        loop {
            let word = self.peek().to_string();
            if PREPOSITIONS.contains(&word.as_str()) && (word != "of" || of_an_action) {
                self.at += 1;
                parts.push(format!("{word} {}", self.np()?));
            } else if of_an_action && ["within", "for"].contains(&word.as_str()) {
                self.at += 1;
                let mut measure = Vec::new();
                loop {
                    // `at least` and `at most` are words of a bound, and `at` alone opens a role.
                    let bound = self.peek() == "at" && ["least", "most"].contains(&self.ahead(1));
                    if (PREPOSITIONS.contains(&self.peek()) && !bound) || ["within", "for", "before", "after", "unless", ",", ".", "and", "or", ""].contains(&self.peek()) {
                        break;
                    }
                    measure.push(self.take());
                }
                if measure.is_empty() {
                    return Err(format!("`{word}` without a measure"));
                }
                parts.push(format!("{word} {}", measure.join(" ")));
            } else if of_an_action && ["before", "after"].contains(&word.as_str()) {
                self.at += 1;
                parts.push(format!("{word} {}", self.clause()?));
            } else {
                return Ok(parts.join(" "));
            }
        }
    }

    /// What a copula says of its subject, as its words.
    fn predicate(&mut self, in_relative: bool) -> Found<String> {
        let mut words: Vec<String> = Vec::new();
        if self.peek() == "not" {
            words.push(self.take());
        }
        if ARTICLES.contains(&self.peek()) {
            words.push(self.take());
            if !self.is_noun(self.peek()) {
                return Err(format!("`{}` is no noun that the package declares", self.peek()));
            }
            words.push(self.take());
            if self.peek() == "of" {
                self.at += 1;
                words.push("of".to_string());
                words.push(self.flat_np()?);
            }
            return Ok(words.join(" "));
        }
        // A value, or the values of an enumeration.
        let stops = |word: &str| [",", ".", "and", "or", "unless", "is", "are", ""].contains(&word) || MODALS.contains(&word) || PREPOSITIONS.contains(&word);
        let mut value = Vec::new();
        while !stops(self.peek()) {
            value.push(self.take());
        }
        if value.is_empty() {
            return Err("a copula without a predicate".to_string());
        }
        // In a relative clause one word is a value, and what follows is the clause around it.
        if in_relative && value.len() > 1 {
            return Err("a value of a relative clause before further words: the clause has no end that the words tell".to_string());
        }
        words.push(value.join(" "));
        while ["and", "or"].contains(&self.peek()) && !self.starts_clause(1) {
            let conj = self.take();
            let mut value = Vec::new();
            while !stops(self.peek()) {
                value.push(self.take());
            }
            if value.is_empty() {
                return Err("an enumeration without a value".to_string());
            }
            words.push(conj);
            words.push(value.join(" "));
        }
        Ok(words.join(" "))
    }

    /// `true` where a clause opens `by` words ahead: a determiner or a declared noun.
    fn starts_clause(&self, by: usize) -> bool {
        let word = self.ahead(by);
        DETERMINERS.contains(&word) || Self::is_number(word) || self.is_noun(word)
    }

    fn clause(&mut self) -> Found<String> {
        let subject = self.np()?;
        if ["is", "are", "remains"].contains(&self.peek()) {
            let copula = self.take();
            return Ok(format!("({subject} {copula} {})", self.predicate(false)?));
        }
        let mut parts = vec![subject];
        if ["does", "do"].contains(&self.peek()) && self.ahead(1) == "not" {
            parts.push([self.take(), self.take()].join(" "));
        }
        parts.push(self.verb()?);
        if self.opens_np() {
            parts.push(self.np()?);
        }
        Ok(format!("({})", self.joined(parts, false)?))
    }

    fn action(&mut self) -> Found<String> {
        let mut parts = vec![self.verb()?];
        if self.opens_np() {
            parts.push(self.np()?);
        }
        self.joined(parts, true)
    }

    fn sentence(&mut self) -> Found<String> {
        let mut frames: Vec<(usize, String)> = Vec::new();
        while FRAMES.contains(&self.peek()) {
            let keyword = self.take();
            let mut clauses = vec![self.clause()?];
            let mut conj = "and";
            while ["and", "or"].contains(&self.peek()) {
                conj = if self.take() == "or" { "or" } else { "and" };
                clauses.push(self.clause()?);
            }
            self.expect(",")?;
            if self.peek() == "then" {
                self.at += 1;
            }
            let class = match keyword.as_str() {
                "where" => 0,
                "while" => 1,
                _ => 2,
            };
            frames.push((class, format!("{keyword}{{{}}}", clauses.join(&format!(" {conj} ")))));
        }
        frames.sort_by_key(|(class, _)| *class);
        let mut parts: Vec<String> = frames.into_iter().map(|(_, frame)| frame).collect();
        let subject = self.np()?;
        let word = self.take();
        parts.push(match word.as_str() {
            modal if MODALS.contains(&modal) => {
                let negated = self.peek() == "not";
                if negated {
                    self.at += 1;
                }
                let actions = if self.peek() == "either" {
                    self.at += 1;
                    let mut items = vec![self.action()?];
                    while self.peek() == "or" {
                        self.at += 1;
                        items.push(self.action()?);
                    }
                    format!("either {}", items.join(" or "))
                } else {
                    let mut items = vec![self.action()?];
                    while self.peek() == "and" {
                        self.at += 1;
                        items.push(self.action()?);
                    }
                    items.join(" and ")
                };
                format!("{subject} {modal}{} {actions}", if negated { " not" } else { "" })
            }
            "is" | "are" => {
                let adverb = if ["never", "always"].contains(&self.peek()) { format!(" {}", self.take()) } else { String::new() };
                format!("{subject} {word}{adverb} {}", self.predicate(false)?)
            }
            "has" | "have" => format!("{subject} {word} {}", self.np()?),
            other => return Err(format!("`{other}` stands where a modal verb, a copula or `has` is expected")),
        });
        if self.peek() == "," && self.ahead(1) == "unless" {
            self.at += 2;
            parts.push(format!("unless {}", self.clause()?));
        }
        self.expect(".")?;
        if self.at != self.words.len() {
            return Err(format!("`{}` stands after the end of the sentence", self.peek()));
        }
        Ok(parts.join(" "))
    }
}

/// The words of a text: lower case, numbers as digits, and each mark of
/// punctuation by itself.
fn words_of(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for raw in text.split_whitespace() {
        let mut word = raw;
        let mut marks = Vec::new();
        while let Some(last) = word.chars().last().filter(|c| [',', '.', ':', ';'].contains(c)) {
            // `2.5` keeps its point; the point after a number at the end of a sentence is a mark.
            marks.push(last.to_string());
            word = &word[..word.len() - 1];
        }
        if !word.is_empty() {
            out.push(number(&word.to_lowercase()));
        }
        out.extend(marks.into_iter().rev());
    }
    out
}

/// Reads the text of a statement by the grammar of this module and
/// compares it with the tree. `nouns` holds the nouns that the package
/// declares, in the singular and in lower case.
pub fn check(text: &str, sentence: &Sentence, nouns: &BTreeSet<String>) -> Read {
    let Some(tree) = tree(sentence) else { return Read::NotRead("the tree holds a form outside the grammar of the second reading".to_string()) };
    let mut reader = Reader { words: words_of(text), at: 0, nouns };
    match reader.sentence() {
        Ok(text) if text == tree => Read::Agrees,
        Ok(text) => Read::Differs { text, tree },
        Err(why) => Read::NotRead(why),
    }
}

/// What a statement of the form `Each A is a B.` says, read from its text:
/// the two nouns, in the singular. `None` for a text of another form.
pub fn kind(text: &str, nouns: &BTreeSet<String>) -> Option<(String, String)> {
    let words = words_of(text);
    let [each, narrow, copula, article, wide, end] = words.as_slice() else { return None };
    let declared = |word: &str| if nouns.contains(word) { Some(word.to_string()) } else { Some(singular(word)).filter(|one| nouns.contains(one)) };
    if !["each", "every"].contains(&each.as_str()) || !["is", "are"].contains(&copula.as_str()) || !["a", "an"].contains(&article.as_str()) || end != "." {
        return None;
    }
    Some((declared(narrow)?, declared(wide)?))
}

/// Reads an unconditional Boolean classification over a declared carrier.
pub(super) fn membership(text: &str, nouns: &BTreeSet<String>) -> Option<DomainFact> {
    fn class(reader: &mut Reader<'_>) -> Option<Nominal<String>> {
        if !["a", "an"].contains(&reader.peek()) {
            return None;
        }
        reader.take();
        if !reader.is_noun(reader.peek()) {
            return None;
        }
        let word = reader.take();
        let name = if reader.nouns.contains(&word) { word } else { singular(&word) };
        let atom = Nominal::Atom(name);
        if !["that", "who"].contains(&reader.peek()) {
            return Some(atom);
        }
        reader.take();
        if !["is", "are"].contains(&reader.take().as_str()) {
            return None;
        }
        let denied = reader.peek() == "not";
        if denied { reader.take(); }
        if reader.peek() == "also" { reader.take(); }
        let relative = class(reader)?;
        let relative = if denied { Nominal::Not(Box::new(relative)) } else { relative };
        Some(Nominal::And(vec![atom, relative]))
    }

    let mut reader = Reader { words: words_of(text), at: 0, nouns };
    let each = match reader.peek() {
        "each" | "every" | "a" | "an" | "no" => true,
        "some" => false,
        _ => return None,
    };
    let subject_denied = reader.take() == "no";
    if !reader.is_noun(reader.peek()) {
        return None;
    }
    let narrow = reader.take();
    let narrow = if nouns.contains(&narrow) { narrow } else { singular(&narrow) };
    if !["is", "are"].contains(&reader.take().as_str()) {
        return None;
    }
    let denied = ["not", "never"].contains(&reader.peek());
    if denied { reader.take(); }
    let first = class(&mut reader)?;
    let predicate = match reader.peek() {
        "and" | "or" => {
            let conjunction = reader.peek().to_string();
            let mut items = vec![first];
            while reader.peek() == conjunction {
                reader.take();
                items.push(class(&mut reader)?);
            }
            if conjunction == "and" { Nominal::And(items) } else { Nominal::Or(items) }
        }
        _ => first,
    };
    (reader.peek() == "." && reader.at + 1 == reader.words.len()).then_some(DomainFact::Membership {
        narrow, predicate, each, denied: denied ^ subject_denied,
    })
}
