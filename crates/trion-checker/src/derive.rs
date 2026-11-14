//! The check of the record of a reading against the statement that it is
//! a reading of.
//!
//! The reading over individuals states, for each typed statement, a record
//! of what it read (`Meaning`), the instances of the statement over the
//! domain, the contract of each instance and the fact that each atom stands
//! for. This module derives the meaning of the statement again from the
//! parsed sentence, by an implementation of the rules of
//! `spec/semantics/core.md` that is written apart from the reading, and
//! refuses a record, an instance, a contract or an atom that differs.
//!
//! What a refusal covers:
//!
//! - the version and the rules: a record of another semantic version, or a
//!   step that names no rule of the version;
//! - the binding: a variable with another noun, carrier or place of
//!   introduction, a restriction or a condition that is missing, added,
//!   denied or bound to another variable;
//! - the units: a deadline with another number or another unit;
//! - the instances: an assignment that is missing, repeated or outside the domain;
//! - the formulas: a contract whose condition or guarantee is not the one
//!   that the meaning of its instance requires (a dropped negation, another
//!   individual, another bound, a premise that the statement does not state);
//! - the atoms: an atom that stands for two facts, or a fact with two atoms
//!   of one kind;
//! - the statements: a statement that names a declared type and has no
//!   record, is not listed as outside the fragment and is no statement
//!   about the domain.
//!
//! What it does not cover, and what a result therefore still rests on: the
//! parser, the resolution of names, the placement of a contract over the
//! moments of a trace, the statements about the domain as formulas, and the
//! search. `compare` tests the placement behaviour by behaviour.

use std::collections::{BTreeMap, BTreeSet};
use trion_language::document::{SpecSet, Spec};
use trion_language::reading::typed::{Bounding, Choice, Condition, Force, Frame, FrameKind, Meaning, Pattern, Quantity, Relation, Response, Share, Site, Term, Variable};
use trion_language::reading::{np_key, Fact, Lexicon, Model};
use trion_language::syntax::ast::*;
use trion_solver::{Atom, Cmp, Formula};

/// The meaning rules that this checker implements.
pub const VERSION: &str = "0.1.0";

/// The rules of the version, by name.
pub const RULES: [&str; 35] = [
    "variable", "variable-some", "variable-any", "variable-again", "variable-other", "variable-that", "variable-no", "variable-count", "choice-order", "variable-of", "constant", "attribute", "frame-where", "frame-while", "frame-when", "frame-if", "condition-occurs", "condition-holds", "condition-related", "condition-kind", "condition-compares", "exception", "force", "response-action", "response-deadline", "response-after", "response-before", "response-state", "response-values", "response-related", "response-kind", "response-bound", "response-share", "choice-either", "choice-each",
];

/// One refusal: the statement or the instance, and what differs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refusal {
    pub subject: String,
    pub what: String,
}

fn singular(word: &str) -> String {
    let word = word.to_lowercase();
    if word.len() < 3 || word == "has" || word == "does" {
        return match word.as_str() {
            "has" => "have".to_string(),
            "does" => "do".to_string(),
            _ => word,
        };
    }
    if let Some(stem) = word.strip_suffix("ies") {
        return format!("{stem}y");
    }
    if ["sses", "shes", "ches", "xes", "zes", "oes"].iter().any(|e| word.ends_with(e)) {
        return word[..word.len() - 2].to_string();
    }
    if word.ends_with("ss") || word.ends_with("us") || word.ends_with("is") {
        return word;
    }
    word.strip_suffix('s').map(str::to_string).unwrap_or(word)
}

const ORDINALS: [&str; 6] = ["second", "third", "fourth", "fifth", "sixth", "other"];

/// The second reading of one sentence.
struct Second<'a> {
    lex: &'a Lexicon,
    carriers: &'a BTreeMap<String, String>,
    variables: Vec<Variable>,
    restrictions: Vec<Relation>,
    site: Site,
    share: Option<Share>,
    /// `true` while what an obligation requires or advice advises is read.
    obliged: bool,
}

type Read<T> = Result<T, String>;

/// `for <bound> percent of <population>`: the two roles of a share, by their places.
fn share_of(roles: &[RolePp]) -> Read<Option<(usize, Share)>> {
    let percent = |unit: &Option<String>| unit.as_deref().is_some_and(|u| u.eq_ignore_ascii_case("percent") || u == "%");
    let Some(at) = roles.iter().position(|role| matches!(role, RolePp::Duration(Measure::Quantity { unit, .. } | Measure::Bounded { unit, .. }) if percent(unit))) else { return Ok(None) };
    let Some(RolePp::Other { preposition, np }) = roles.get(at + 1).filter(|role| matches!(role, RolePp::Other { preposition, .. } if preposition == "of")) else { return Err("a share without its population".to_string()) };
    let _ = preposition;
    let (bounding, number) = match &roles[at] {
        RolePp::Duration(Measure::Quantity { number, .. }) => (Bounding::AtLeast, number),
        RolePp::Duration(Measure::Bounded { op, number, upper: None, .. }) => (
            match op {
                ComparisonOp::AtLeast => Bounding::AtLeast,
                ComparisonOp::AtMost => Bounding::AtMost,
                ComparisonOp::GreaterThan => Bounding::MoreThan,
                ComparisonOp::LessThan => Bounding::LessThan,
                ComparisonOp::EqualTo => Bounding::Exactly,
                ComparisonOp::Between => return Err("a share between two bounds".to_string()),
            },
            number,
        ),
        _ => return Err("a share between two bounds".to_string()),
    };
    let (whole, fraction) = number.split_once('.').unwrap_or((number, ""));
    if whole.is_empty() || fraction.len() > 3 || !whole.chars().chain(fraction.chars()).all(|c| c.is_ascii_digit()) {
        return Err(format!("`{number}` is no number of percent"));
    }
    let thousandths = whole.parse::<i64>().map_err(|e| e.to_string())? * 1000 + format!("{fraction:0<3}").parse::<i64>().map_err(|e| e.to_string())?;
    let name = np.render().to_lowercase();
    let population = name.strip_prefix("the ").or_else(|| name.strip_prefix("all ")).unwrap_or(&name).to_string();
    Ok(Some((at, Share { bounding, thousandths, population })))
}

impl Second<'_> {
    fn noun(&self, words: &[String]) -> String {
        let mut words: Vec<String> = words.iter().map(|w| w.to_lowercase()).collect();
        if let Some(last) = words.pop() {
            words.push(singular(&last));
        }
        self.lex.resolve(&self.lex.canon(&words.join(" ")))
    }

    fn head(&self, np: &Np) -> String {
        self.noun(std::slice::from_ref(&np.head))
    }

    fn denote(&mut self, np: &Np) -> Read<Term> {
        let head = self.head(np);
        let Some(carrier) = self.carriers.get(&head).cloned() else {
            return Ok(match (&np.of, np.of_also.is_empty()) {
                (Some(owner), true) => match self.denote(owner)? {
                    Term::Constant(_) => Term::Constant(np_key(np, self.lex)),
                    of => Term::Attribute { name: np_key(&Np { of: None, ..np.clone() }, self.lex), of: Box::new(of) },
                },
                _ => Term::Constant(np_key(np, self.lex)),
            });
        };
        if np.relative.is_some() || !np.of_also.is_empty() {
            return Err(format!("`{}` holds a relative clause or a coordinated owner", np.render()));
        }
        let literal = |m: &String| m.starts_with('`');
        if np.modifiers.iter().any(|m| !ORDINALS.contains(&m.to_lowercase().as_str()) && !literal(m)) {
            return Err(format!("`{}` holds a modifier", np.render()));
        }
        let general = matches!(np.det, Some(Det::Each | Det::Every | Det::Any));
        if !(general || matches!(np.det, Some(Det::The | Det::A | Det::An)) || (np.det.is_none() && np.modifiers.iter().any(literal))) {
            return Err(format!("`{}` has a determiner that names no individual", np.render()));
        }
        let key: Vec<String> = np.modifiers.iter().map(|m| m.to_lowercase()).filter(|m| ORDINALS.contains(&m.as_str())).chain([head.clone()]).collect();
        let key = key.join(" ");
        // The owner is read before the head.
        let owner = match &np.of {
            Some(owner) => {
                let term = self.denote(owner)?;
                if !matches!(term, Term::Variable(_)) {
                    return Err(format!("the owner of `{}` is no individual", np.render()));
                }
                Some((term, self.head(owner)))
            }
            None => None,
        };
        let id = match self.variables.iter().find(|v| v.key == key) {
            Some(known) => known.id,
            None => {
                // What an obligation first names with `a` or `an` in its
                // response is chosen by the response; `the` names what a
                // condition named or what a relation gives.
                let named = self.site == Site::Response && matches!(np.det, Some(Det::A | Det::An));
                // Under a permission `a` and `an` name any individual.
                let introduced = named && self.obliged;
                if self.site == Site::Response && owner.is_none() && !general && !named {
                    return Err(format!("`{}` names with `the` an individual that no condition names", np.render()));
                }
                let id = self.variables.len() as u32;
                self.variables.push(Variable { id, key, noun: head.clone(), carrier, site: if introduced { Site::Chosen } else { self.site } });
                id
            }
        };
        if let Some((owner, owner_noun)) = owner {
            let relation = Relation { relation: head, owner_noun, owner, member: Term::Variable(id), denied: false };
            if !self.restrictions.contains(&relation) {
                self.restrictions.push(relation);
            }
        }
        Ok(Term::Variable(id))
    }

    fn one(&mut self, group: &NpGroup) -> Read<Term> {
        match group {
            NpGroup::Single(np) => self.denote(np),
            NpGroup::Coordinated { items, .. } if items.iter().any(|np| self.carriers.contains_key(&self.head(np))) => Err(format!("`{}` coordinates individuals", group.render())),
            NpGroup::Coordinated { .. } => Ok(Term::Constant(group.render().to_lowercase())),
        }
    }

    fn pattern(&mut self, actor: Term, verb: &str, particle: &Option<String>, object: &Option<NpGroup>, roles: &[RolePp]) -> Read<Pattern> {
        let object = object.as_ref().map(|group| self.one(group)).transpose()?;
        let mut named = Vec::new();
        for role in roles {
            let (marker, group) = match role {
                RolePp::Recipient(g) => ("to".to_string(), g),
                RolePp::Topic(g) => ("about".to_string(), g),
                RolePp::Source(g) => ("from".to_string(), g),
                RolePp::Goal(g) => ("into".to_string(), g),
                RolePp::Agent(g) => ("by".to_string(), g),
                RolePp::Means { marker, np } => (marker.as_str().to_string(), np),
                RolePp::Location { preposition, np } | RolePp::Other { preposition, np } => (preposition.to_lowercase(), np),
                RolePp::Deadline(_) | RolePp::Duration(_) | RolePp::Rate { .. } | RolePp::Before(_) | RolePp::After(_) | RolePp::Until(_) => continue,
            };
            named.push((marker, self.one(group)?));
        }
        Ok(Pattern { actor, verb: singular(verb), particle: particle.as_ref().map(|p| p.to_lowercase()), object, roles: named })
    }

    /// What `[not] a R [of the T]`, `[not] the R of the T` or `[not] <value>` says.
    fn predicate(&mut self, subject: Term, words: &[String], roles: &[RolePp]) -> Read<Said> {
        let lower: Vec<String> = words.iter().map(|w| w.to_lowercase()).collect();
        let (denied, rest) = match lower.split_first() {
            Some((first, rest)) if first == "not" => (true, rest),
            _ => (false, &lower[..]),
        };
        let tail_owner = match roles {
            [RolePp::Other { preposition, np: NpGroup::Single(owner) }] if preposition == "of" => Some(owner.clone()),
            [] => None,
            _ => return Err("a predicate with a role that is no owner".to_string()),
        };
        let inner = rest.iter().position(|w| w == "of").filter(|_| tail_owner.is_none());
        let (named, owner): (&[String], Option<Np>) = match inner {
            Some(at) => {
                let words = &rest[at + 1..];
                let (det, words) = match words.split_first() {
                    Some((d, tail)) if d == "the" => (Det::The, tail),
                    Some((d, tail)) if d == "a" => (Det::A, tail),
                    Some((d, tail)) if d == "an" => (Det::An, tail),
                    Some((d, tail)) if d == "each" => (Det::Each, tail),
                    _ => return Err("an owner without an article".to_string()),
                };
                let Some((head, modifiers)) = words.split_last() else { return Err("an owner without a noun".to_string()) };
                (&rest[..at], Some(Np { det: Some(det), modifiers: modifiers.to_vec(), head: head.clone(), of: None, relative: None, of_also: Vec::new(), of_conj: None }))
            }
            None => (rest, tail_owner),
        };
        let article = |w: &String| w == "a" || w == "an" || (w == "the" && owner.is_some());
        match named.split_first() {
            Some((first, noun)) if article(first) && !noun.is_empty() => {
                let name = self.noun(noun);
                match owner {
                    Some(owner) => {
                        let owner_noun = self.head(&owner);
                        let owner = self.denote(&owner)?;
                        if !matches!((&owner, &subject), (Term::Variable(_), Term::Variable(_))) {
                            return Err("a relation between things that are no individuals".to_string());
                        }
                        Ok(Said::Related(Relation { relation: name, owner_noun, owner, member: subject, denied }))
                    }
                    None => Ok(Said::Kind { kind: name, subject, denied }),
                }
            }
            _ if owner.is_none() && !rest.is_empty() => Ok(Said::Value { subject, value: rest.join(" "), denied }),
            _ => Err("a predicate that names no kind, no relation and no value".to_string()),
        }
    }

    fn condition(&mut self, clause: &Clause) -> Read<Condition> {
        let subject = self.one(&clause.subject)?;
        match &clause.body {
            ClauseBody::Verbal { verb, particle, object, roles, negation, .. } => Ok(Condition::Occurs { pattern: self.pattern(subject, verb, particle, object, roles)?, denied: negation.is_some() }),
            ClauseBody::Copular { predicate: Predicate::Words { words }, agent: None, roles, .. } => Ok(match self.predicate(subject, words, roles)? {
                Said::Related(relation) => Condition::Related(relation),
                Said::Kind { kind, subject, denied } => Condition::Kind { kind, subject, denied },
                Said::Value { subject, value, denied } => Condition::Holds { subject, value, denied },
            }),
            ClauseBody::Copular { predicate: Predicate::Comparison(_), agent: None, .. } => Ok(Condition::Compares { text: clause.render() }),
            ClauseBody::Copular { .. } => Err(format!("`{}` is a condition of another form", clause.render())),
        }
    }

    fn frame(&mut self, kind: FrameKind, group: &ClauseGroup) -> Read<Frame> {
        let conditions = group.items.iter().map(|clause| self.condition(clause)).collect::<Read<Vec<_>>>()?;
        Ok(Frame { kind, any: group.conj == Some(Conj::Or), conditions })
    }

    fn action(&mut self, actor: &Term, vp: &Vp) -> Read<Response> {
        if vp.content.is_some() || vp.complement.is_some() {
            return Err(format!("`{}` holds a complement", vp.render()));
        }
        let mut deadline = None;
        let (mut after, mut before) = (Vec::new(), Vec::new());
        // The two roles of a share are no roles of the action.
        let mut roles: Vec<RolePp> = vp.roles.clone();
        if let Some((at, share)) = share_of(&roles)? {
            if self.share.replace(share).is_some() {
                return Err("two shares".to_string());
            }
            roles.drain(at..at + 2);
        }
        // The events of an order are read before the action.
        for role in &roles {
            match role {
                RolePp::Deadline(Measure::Quantity { number, unit: Some(unit) }) => deadline = Some(time(number, unit)?),
                RolePp::After(clause) | RolePp::Before(clause) => {
                    let actor = self.one(&clause.subject)?;
                    let ClauseBody::Verbal { verb, particle, object, roles, content: None, negation: None, .. } = &clause.body else { return Err("an order against no event".to_string()) };
                    let pattern = self.pattern(actor, verb, particle, object, roles)?;
                    if matches!(role, RolePp::After(_)) { after.push(pattern) } else { before.push(pattern) }
                }
                RolePp::Deadline(_) | RolePp::Until(_) | RolePp::Duration(_) | RolePp::Rate { .. } => return Err("a time role without a rule".to_string()),
                _ => {}
            }
        }
        let pattern = self.pattern(actor.clone(), &vp.verb, &vp.particle, &vp.object, &roles)?;
        Ok(Response::Action { pattern, deadline, after, before })
    }
}

enum Said {
    Related(Relation),
    Kind { kind: String, subject: Term, denied: bool },
    Value { subject: Term, value: String, denied: bool },
}

/// A time in thousandths of a millisecond.
fn time(number: &str, unit: &str) -> Read<Quantity> {
    let (whole, fraction) = number.split_once('.').unwrap_or((number, ""));
    let digits = |text: &str| text.chars().all(|c| c.is_ascii_digit());
    if whole.is_empty() || fraction.len() > 3 || !digits(whole) || !digits(fraction) {
        return Err(format!("`{number}` is no number of a deadline"));
    }
    let mut thousandths: i64 = whole.parse::<i64>().map_err(|e| e.to_string())? * 1000;
    thousandths += format!("{fraction:0<3}").parse::<i64>().map_err(|e| e.to_string())?;
    let per = match unit.to_lowercase().as_str() {
        "ms" | "millisecond" | "milliseconds" => 1,
        "s" | "sec" | "secs" | "second" | "seconds" => 1_000,
        "min" | "mins" | "minute" | "minutes" => 60_000,
        "h" | "hour" | "hours" => 3_600_000,
        other => return Err(format!("`{other}` is no unit of time")),
    };
    Ok(Quantity { thousandths: thousandths * per, unit: "ms".to_string() })
}

/// The names of the further individuals of a count: `a second member`, ….
const FURTHER: [&str; 5] = ["second", "third", "fourth", "fifth", "sixth"];

/// The sentence that a statement with a relative clause, `no` or a count
/// stands for, by the second reading: the same statement with each
/// individual named by itself and each relative clause as a condition.
fn unfolded(sentence: &Sentence, reader: &Second) -> Read<Sentence> {
    let typed = |np: &Np| reader.carriers.contains_key(&reader.head(np));
    let many = |np: &Np| -> Read<usize> {
        match &np.det {
            Some(Det::Cardinal { n, .. } | Det::AtLeast { n }) if typed(np) && *n >= 2 => {
                if *n > 6 || np.modifiers.iter().any(|m| ORDINALS.contains(&m.to_lowercase().as_str())) {
                    return Err(format!("`{}` is a count that names no individuals one by one", np.render()));
                }
                Ok(*n as usize)
            }
            _ => Ok(1),
        }
    };
    let one_of = |np: &Np, at: usize| {
        let mut one = np.clone();
        one.head = singular(&np.head);
        one.det = Some(Det::A);
        if at > 0 {
            one.modifiers.insert(0, FURTHER[at - 1].to_string());
        }
        one
    };
    let mut out = sentence.clone();
    // `no`: the statement denied of each individual.
    if let Core::Deontic { subject, negated, vp, .. } = &mut out.core {
        let mut denials = 0;
        if let NpGroup::Single(np) = subject {
            if matches!(np.det, Some(Det::No)) && typed(np) {
                np.det = Some(Det::Each);
                denials += 1;
            }
        }
        if let VpGroup::Single(Vp { object: Some(NpGroup::Single(np)), .. }) = vp {
            if matches!(np.det, Some(Det::No)) && typed(np) {
                np.det = Some(Det::Each);
                denials += 1;
            }
        }
        match (denials, *negated) {
            (0, _) => {}
            (1, false) => *negated = true,
            _ => return Err("a statement that `no` denies twice, or beside a denied verb".to_string()),
        }
    }
    // A composition of plain actions about individuals: a list of them,
    // in order each after the one before it.
    if let Core::Deontic { subject, vp, .. } = &mut out.core {
        if let VpGroup::Composite(composition) = vp {
            let mut names = Vec::new();
            heads(&serde_json::to_value(&*composition).unwrap_or_default(), &mut names);
            heads(&serde_json::to_value(&*subject).unwrap_or_default(), &mut names);
            if names.iter().any(|head| typed(&Np::bare(head))) {
                let (nodes, kind) = match &composition.root {
                    CompNode::All { items } => (items, 0),
                    CompNode::Some { items } => (items, 1),
                    CompNode::Sequence { items } => (items, 2),
                    _ => return Err("a composition of another kind".to_string()),
                };
                let mut listed: Vec<Vp> = Vec::new();
                for node in nodes {
                    let CompNode::Leaf { index, exception: None } = node else { return Err("a composition within a composition".to_string()) };
                    let mut action = composition.leaves.get(*index).ok_or("a composition without its action")?.clone();
                    if let (2, Some(last)) = (kind, composition.leaves.get(*index).and_then(|_| listed.last())) {
                        // The action before, as the event that this one follows: its time roles are its own.
                        let mut roles = last.roles.clone();
                        roles.retain(|role| !matches!(role, RolePp::Deadline(_) | RolePp::Duration(_) | RolePp::Rate { .. } | RolePp::Before(_) | RolePp::After(_) | RolePp::Until(_)));
                        action.roles.push(RolePp::After(Box::new(Clause { subject: subject.clone(), body: ClauseBody::Verbal { verb: last.verb.clone(), particle: last.particle.clone(), manner: Vec::new(), object: last.object.clone(), roles, content: None, negation: None } })));
                    }
                    listed.push(action);
                }
                *vp = if kind == 1 { VpGroup::Alternatives { items: listed } } else { VpGroup::All { negated: vec![false; listed.len()], items: listed } };
            }
        }
    }
    // A count: one clause, or one action, for each individual.
    for frame in out.frames.scopes.iter_mut().chain(out.frames.states.iter_mut()) {
        let mut clauses = Vec::new();
        for clause in &frame.clause.items {
            let n = match &clause.subject {
                NpGroup::Single(np) => many(np)?,
                NpGroup::Coordinated { .. } => 1,
            };
            if n > 1 && frame.clause.conj == Some(Conj::Or) {
                return Err("a count among alternative conditions".to_string());
            }
            for at in 0..n {
                let mut one = clause.clone();
                if let (true, NpGroup::Single(np)) = (n > 1, &clause.subject) {
                    one.subject = NpGroup::Single(one_of(np, at));
                    // What is said of several is said of each: `are members of the room`.
                    if let ClauseBody::Copular { copula, predicate: Predicate::Words { words }, roles, .. } = &mut one.body {
                        *copula = ClauseCopula::Is;
                        let owner_follows = matches!(roles.as_slice(), [RolePp::Other { preposition, .. }] if preposition.to_lowercase() == "of");
                        let from = usize::from(words.first().is_some_and(|w| w.to_lowercase() == "not"));
                        if let Some(first) = words.get(from).map(|w| w.to_lowercase()) {
                            let names_kind = words.len() == from + 1 && reader.carriers.contains_key(&reader.noun(std::slice::from_ref(&first)));
                            let names_relation = words.get(from + 1).is_some_and(|w| w.to_lowercase() == "of") || (words.len() == from + 1 && owner_follows);
                            if !["a", "an", "the"].contains(&first.as_str()) && (names_kind || names_relation) {
                                let one_noun = singular(&first);
                                words[from] = one_noun.clone();
                                words.insert(from, if one_noun.starts_with(['a', 'e', 'i', 'o', 'u']) { "an" } else { "a" }.to_string());
                            }
                        }
                    }
                }
                clauses.push(one);
            }
        }
        if clauses.len() > 1 && frame.clause.conj.is_none() {
            frame.clause.conj = Some(Conj::And);
        }
        frame.clause.items = clauses;
    }
    let counted_group = |group: &NpGroup| -> Read<usize> {
        match group {
            NpGroup::Single(np) => many(np),
            NpGroup::Coordinated { .. } => Ok(1),
        }
    };
    let role_group = |role: &RolePp| -> Option<NpGroup> {
        match role {
            RolePp::Recipient(g) | RolePp::Topic(g) | RolePp::Source(g) | RolePp::Goal(g) | RolePp::Agent(g) => Some(g.clone()),
            RolePp::Means { np, .. } | RolePp::Location { np, .. } | RolePp::Other { np, .. } => Some(np.clone()),
            _ => None,
        }
    };
    if let Some(trigger) = &out.frames.trigger {
        for clause in &trigger.clause.items {
            let mut counts = vec![counted_group(&clause.subject)?];
            if let ClauseBody::Verbal { object, roles, .. } = &clause.body {
                if let Some(object) = object {
                    counts.push(counted_group(object)?);
                }
                for group in roles.iter().filter_map(role_group) {
                    counts.push(counted_group(&group)?);
                }
            }
            if counts.iter().any(|n| *n > 1) {
                return Err("a count in the event of the statement".to_string());
            }
        }
    }
    if let Core::Deontic { subject, modal, negated, vp } = &mut out.core {
        if counted_group(subject)? > 1 {
            return Err("a count before the subject".to_string());
        }
        let chooses = !*negated && matches!(modal, Modal::Shall | Modal::Must | Modal::Should);
        let mut places: Vec<(Option<usize>, Np, usize)> = Vec::new();
        for item in vp.items() {
            if let Some(NpGroup::Single(np)) = &item.object {
                if many(np)? > 1 {
                    places.push((None, np.clone(), many(np)?));
                }
            }
            for (at, role) in item.roles.iter().enumerate() {
                if let Some(NpGroup::Single(np)) = role_group(role) {
                    if many(&np)? > 1 {
                        places.push((Some(at), np.clone(), many(&np)?));
                    }
                }
            }
        }
        match (places.as_slice(), &*vp) {
            ([], _) => {}
            ([(place, np, n)], VpGroup::Single(item)) if chooses => {
                let mut items = Vec::new();
                for at in 0..*n {
                    let mut one = item.clone();
                    let named = NpGroup::Single(one_of(np, at));
                    match place {
                        None => one.object = Some(named),
                        Some(role) => match &mut one.roles[*role] {
                            RolePp::Recipient(g) | RolePp::Topic(g) | RolePp::Source(g) | RolePp::Goal(g) | RolePp::Agent(g) => *g = named,
                            RolePp::Means { np, .. } | RolePp::Location { np, .. } | RolePp::Other { np, .. } => *np = named,
                            _ => {}
                        },
                    }
                    items.push(one);
                }
                *vp = VpGroup::All { negated: vec![false; items.len()], items };
            }
            _ => return Err("a count in an action that is no single required or advised action".to_string()),
        }
    }
    // The relative clauses: each a condition about the individual of its noun.
    let mut states: Vec<Clause> = Vec::new();
    let mut event: Option<Clause> = None;
    let mut failed: Option<String> = None;
    {
        let mut take = |np: &mut Np, chosen: bool| {
            if !typed(np) {
                return;
            }
            let Some(relative) = np.relative.take() else { return };
            if chosen && matches!(np.det, Some(Det::A | Det::An)) {
                failed = Some(format!("`{}` is an individual that the response chooses, with a relative clause", np.render()));
                return;
            }
            let it = Np { det: Some(Det::The), modifiers: np.modifiers.iter().filter(|m| ORDINALS.contains(&m.to_lowercase().as_str())).cloned().collect(), head: np.head.clone(), of: None, relative: None, of_also: Vec::new(), of_conj: None };
            let mut next = Some(relative);
            while let Some(relative) = next {
                let Relative { marker, body, and } = *relative;
                next = and;
                let happens = match body {
                    RelativeBody::Copular { copula, predicate, agent, roles } => {
                        states.push(Clause { subject: NpGroup::Single(it.clone()), body: ClauseBody::Copular { copula, predicate, agent, roles } });
                        None
                    }
                    RelativeBody::Content { clause } if marker == RelMarker::Whose => {
                        let mut clause = *clause;
                        match &mut clause.subject {
                            NpGroup::Single(property) if property.of.is_none() => {
                                property.det = Some(Det::The);
                                property.of = Some(Box::new(it.clone()));
                                states.push(clause);
                            }
                            _ => failed = Some("a `whose` clause that names no single property".to_string()),
                        }
                        None
                    }
                    RelativeBody::Verbal { verb, particle, manner, object, roles, negation: None } => Some(Clause { subject: NpGroup::Single(it.clone()), body: ClauseBody::Verbal { verb, particle, manner, object, roles, content: None, negation: None } }),
                    RelativeBody::ObjectGap { subject, verb, particle, manner, roles } => Some(Clause { subject, body: ClauseBody::Verbal { verb, particle, manner, object: Some(NpGroup::Single(it.clone())), roles, content: None, negation: None } }),
                    _ => {
                        failed = Some("a relative clause that denies an event or holds a content clause".to_string());
                        None
                    }
                };
                if let Some(clause) = happens {
                    if event.replace(clause).is_some() {
                        failed = Some("two events in relative clauses".to_string());
                    }
                }
            }
        };
        fn nps(np: &mut Np, chosen: bool, take: &mut dyn FnMut(&mut Np, bool)) {
            if let Some(owner) = &mut np.of {
                nps(owner, false, take);
            }
            take(np, chosen);
        }
        fn groups(group: &mut NpGroup, chosen: bool, take: &mut dyn FnMut(&mut Np, bool)) {
            match group {
                NpGroup::Single(np) => nps(np, chosen, take),
                NpGroup::Coordinated { items, .. } => items.iter_mut().for_each(|np| nps(np, chosen, take)),
            }
        }
        fn role_nps(roles: &mut [RolePp], chosen: bool, take: &mut dyn FnMut(&mut Np, bool)) {
            for role in roles {
                match role {
                    RolePp::Recipient(g) | RolePp::Topic(g) | RolePp::Source(g) | RolePp::Goal(g) | RolePp::Agent(g) => groups(g, chosen, take),
                    RolePp::Means { np, .. } | RolePp::Location { np, .. } | RolePp::Other { np, .. } => groups(np, chosen, take),
                    _ => {}
                }
            }
        }
        let frames = &mut out.frames;
        for clause in frames.scopes.iter_mut().chain(frames.states.iter_mut()).map(|f| &mut f.clause).chain(frames.trigger.iter_mut().map(|t| &mut t.clause)).flat_map(|group| group.items.iter_mut()) {
            groups(&mut clause.subject, false, &mut take);
            match &mut clause.body {
                ClauseBody::Copular { agent, roles, .. } => {
                    agent.iter_mut().for_each(|g| groups(g, false, &mut take));
                    role_nps(roles, false, &mut take);
                }
                ClauseBody::Verbal { object, roles, .. } => {
                    object.iter_mut().for_each(|g| groups(g, false, &mut take));
                    role_nps(roles, false, &mut take);
                }
            }
        }
        match &mut out.core {
            Core::Deontic { subject, modal, negated, vp } => {
                groups(subject, false, &mut take);
                let chooses = !*negated && matches!(modal, Modal::Shall | Modal::Must | Modal::Should);
                let items: &mut [Vp] = match vp {
                    VpGroup::Single(item) => std::slice::from_mut(item),
                    VpGroup::Alternatives { items } | VpGroup::All { items, .. } => items,
                    VpGroup::Composite(composition) => &mut composition.leaves,
                };
                for item in items {
                    item.object.iter_mut().for_each(|g| groups(g, chooses, &mut take));
                    role_nps(&mut item.roles, chooses, &mut take);
                }
            }
            Core::Description { subject, roles, .. } => {
                groups(subject, false, &mut take);
                role_nps(roles, false, &mut take);
            }
            _ => {}
        }
    }
    if let Some(why) = failed {
        return Err(why);
    }
    for clause in states {
        out.frames.states.push(trion_language::syntax::ast::Frame { keyword: "While".to_string(), clause: ClauseGroup::single(clause) });
    }
    if let Some(clause) = event {
        if out.frames.trigger.is_some() {
            return Err("an event in a relative clause beside the event of the statement".to_string());
        }
        out.frames.trigger = Some(Trigger { kind: TriggerKind::Event, keyword: "When".to_string(), clause: ClauseGroup::single(clause) });
    }
    Ok(out)
}

/// The meaning of a sentence by the second reading, without its steps.
fn second(statement: &str, sentence: &Sentence, carriers: &BTreeMap<String, String>, lex: &Lexicon) -> Read<Meaning> {
    if sentence.necessary.is_some() || sentence.iff.is_some() || sentence.concession.is_some() {
        return Err("a necessary condition or a concession".to_string());
    }
    let mut reader = Second { lex, carriers, variables: Vec::new(), restrictions: Vec::new(), site: Site::Condition, share: None, obliged: false };
    let sentence = &unfolded(sentence, &reader)?;
    let mut frames = Vec::new();
    for frame in &sentence.frames.scopes {
        frames.push(reader.frame(FrameKind::Where, &frame.clause)?);
    }
    for frame in &sentence.frames.states {
        frames.push(reader.frame(FrameKind::While, &frame.clause)?);
    }
    if let Some(trigger) = &sentence.frames.trigger {
        frames.push(reader.frame(if trigger.kind == TriggerKind::Contingency { FrameKind::If } else { FrameKind::When }, &trigger.clause)?);
    }
    let exception = sentence.exception.as_ref().map(|clause| reader.condition(clause)).transpose()?;
    let (force, choice, responses) = match &sentence.core {
        Core::Deontic { subject, modal, negated, vp } => {
            reader.site = Site::Subject;
            let actor = reader.one(subject)?;
            let force = match (modal, negated) {
                (Modal::Shall | Modal::Must, false) => Force::Obligation,
                (Modal::Shall | Modal::Must, true) => Force::Prohibition,
                (Modal::Should, false) => Force::Recommendation,
                (Modal::Should, true) => Force::RecommendationAgainst,
                (Modal::May, _) => Force::Permission,
            };
            // What is forbidden or advised against is named in general.
            reader.site = if matches!(force, Force::Prohibition | Force::RecommendationAgainst) { Site::Condition } else { Site::Response };
            reader.obliged = matches!(force, Force::Obligation | Force::Recommendation);
            let (choice, items): (Choice, Vec<&Vp>) = match vp {
                VpGroup::Single(vp) => (Choice::One, vec![vp]),
                VpGroup::Alternatives { items } => (Choice::Either, items.iter().collect()),
                VpGroup::All { items, negated } if !negated.iter().any(|n| *n) => (Choice::Each, items.iter().collect()),
                _ => return Err("a composition or a list with a denied action".to_string()),
            };
            let responses = items.into_iter().map(|vp| reader.action(&actor, vp)).collect::<Read<Vec<_>>>()?;
            if choice == Choice::Either && reader.variables.iter().any(|v| v.site == Site::Chosen) {
                return Err("a chosen individual among alternative actions".to_string());
            }
            (force, choice, responses)
        }
        Core::Description { subject, predicate, agent: None, roles, adverb, .. } => {
            reader.site = Site::Subject;
            let subject = reader.one(subject)?;
            reader.site = Site::Condition;
            let never = *adverb == Some(DescriptionAdverb::Never);
            let response = match predicate {
                Predicate::Words { words } => match reader.predicate(subject, words, roles)? {
                    Said::Related(relation) => Response::Related(Relation { denied: relation.denied != never, ..relation }),
                    Said::Kind { kind, subject, denied } => Response::Kind { kind, subject, denied: denied != never },
                    Said::Value { subject, value, denied } => Response::State { subject, value, denied: denied != never },
                },
                Predicate::Enumeration { values, conj: Conj::Or, .. } if !never => Response::Values { subject, values: values.iter().map(|v| v.to_lowercase()).collect() },
                Predicate::Comparison(_) if !never => Response::Bound { text: sentence.core.render() },
                _ => return Err("a predicate of another form".to_string()),
            };
            (Force::Description, Choice::One, vec![response])
        }
        _ => return Err("a core of another form".to_string()),
    };
    if reader.share.is_some() && !(force == Force::Obligation && choice == Choice::One) {
        return Err("a share that stands with no single required action".to_string());
    }
    if reader.share.is_some() && reader.variables.iter().any(|v| v.site == Site::Chosen) {
        return Err("a share of activations whose response chooses an individual".to_string());
    }
    Ok(Meaning { statement: statement.to_string(), version: VERSION, source: sentence.source.clone(), variables: reader.variables, restrictions: reader.restrictions, frames, exception, force, choice, responses, share: reader.share, steps: Vec::new() })
}

/// The heads of the noun phrases of a sentence, read from its tree as data.
fn heads(value: &serde_json::Value, out: &mut Vec<String>) {
    match value {
        serde_json::Value::Object(map) => {
            if let (Some(serde_json::Value::String(head)), true) = (map.get("head"), map.contains_key("modifiers")) {
                out.push(head.clone());
            }
            map.values().for_each(|v| heads(v, out));
        }
        serde_json::Value::Array(items) => items.iter().for_each(|v| heads(v, out)),
        _ => {}
    }
}

fn differs<T: PartialEq + std::fmt::Debug>(name: &str, recorded: &T, derived: &T, out: &mut Vec<String>) {
    if recorded != derived {
        out.push(format!("the {name} of the record is {recorded:?}, and the statement gives {derived:?}"));
    }
}

/// The literals of a conjunction, with the polarity of each.
/// The parts of a guarantee: its literals, and each disjunction of atoms
/// that stands among them (`one of the listed states`). `false` for a
/// guarantee of another form.
fn guarantee_parts(formula: &Formula, literal: &mut BTreeSet<(Atom, bool)>, one_of: &mut Vec<BTreeSet<Atom>>) -> bool {
    let alternatives = |items: &[Formula]| -> Option<BTreeSet<Atom>> {
        items.iter().map(|item| if let Formula::Atom(atom) = item { Some(atom.clone()) } else { None }).collect()
    };
    match formula {
        Formula::Or(items) => alternatives(items).map(|atoms| one_of.push(atoms)).is_some(),
        Formula::And(items) => items.iter().all(|item| match item {
            Formula::Or(inner) => alternatives(inner).map(|atoms| one_of.push(atoms)).is_some(),
            other => literals(other, true, literal),
        }),
        other => literals(other, true, literal),
    }
}

fn literals(formula: &Formula, positive: bool, out: &mut BTreeSet<(Atom, bool)>) -> bool {
    match formula {
        Formula::True => positive,
        Formula::Atom(atom) => {
            out.insert((atom.clone(), positive));
            true
        }
        Formula::Not(inner) => match &**inner {
            Formula::Atom(atom) => {
                out.insert((atom.clone(), !positive));
                true
            }
            _ => false,
        },
        Formula::And(items) if positive => items.iter().all(|item| literals(item, true, out)),
        _ => false,
    }
}

struct Atoms<'a> {
    by_fact: BTreeMap<(&'a Fact, u8), &'a Atom>,
}

fn kind_of(atom: &Atom) -> u8 {
    match atom {
        Atom::Event { .. } => 0,
        Atom::Act { .. } => 1,
        Atom::Val { .. } => 2,
        _ => 3,
    }
}

/// The contract that the meaning of one instance requires, as literals.
struct Expected {
    assume: BTreeSet<(Atom, bool)>,
    /// What makes the individuals that the response chooses ones that it may choose.
    eligible: BTreeSet<(Atom, bool)>,
    guarantee: BTreeSet<(Atom, bool)>,
    /// The bound of each deadline: the key of its action and its thousandths.
    deadlines: Vec<(String, i64)>,
    /// The atoms of which one holds: the listed states of an enumeration.
    one_of: Vec<BTreeSet<Atom>>,
}

struct Instance<'a> {
    meaning: &'a Meaning,
    names: Vec<String>,
    index: Vec<usize>,
}

impl Instance<'_> {
    fn name(&self, term: &Term) -> String {
        match term {
            Term::Variable(id) => self.names[*id as usize].clone(),
            Term::Constant(name) => name.clone(),
            Term::Attribute { name, of } => format!("{name} of {}", self.name(of)),
        }
    }

    fn occurs(&self, pattern: &Pattern) -> Fact {
        Fact::Occurs { verb: pattern.verb.clone(), particle: pattern.particle.clone(), actor: self.name(&pattern.actor), object: pattern.object.as_ref().map(|o| self.name(o)), roles: pattern.roles.iter().map(|(marker, term)| (marker.clone(), self.name(term))).collect() }
    }

    fn number(&self, term: &Term) -> Option<usize> {
        match term {
            Term::Variable(id) => Some(self.index[*id as usize]),
            _ => None,
        }
    }

    fn related(&self, relation: &Relation) -> Option<Atom> {
        Some(Atom::Rel { name: relation.relation.clone(), args: vec![format!("{}#{}", relation.owner_noun, self.number(&relation.owner)?), format!("{}#{}", relation.relation, self.number(&relation.member)?)] })
    }

    fn kind(&self, kind: &str, subject: &Term) -> Option<Atom> {
        Some(Atom::Rel { name: kind.to_string(), args: vec![format!("{kind}#{}", self.number(subject)?)] })
    }

    fn expected(&self, atoms: &Atoms) -> Read<Expected> {
        let meaning = self.meaning;
        let mut assume = BTreeSet::new();
        let mut eligible = BTreeSet::new();
        let missing = |what: &str| format!("no atom stands for {what}");
        let chosen = |term: &Term| matches!(term, Term::Variable(id) if meaning.variables[*id as usize].site == Site::Chosen);
        for variable in &meaning.variables {
            let kind = (Atom::Rel { name: variable.noun.clone(), args: vec![format!("{}#{}", variable.noun, self.index[variable.id as usize])] }, true);
            if variable.site == Site::Chosen { eligible.insert(kind) } else { assume.insert(kind) };
        }
        for relation in &meaning.restrictions {
            let related = (self.related(relation).ok_or("a restriction without individuals")?, true);
            if chosen(&relation.owner) || chosen(&relation.member) { eligible.insert(related) } else { assume.insert(related) };
        }
        let conditional = |condition: &Condition, flip: bool, assume: &mut BTreeSet<(Atom, bool)>| -> Read<()> {
            match condition {
                Condition::Occurs { pattern, denied } => {
                    let fact = self.occurs(pattern);
                    let atom = atoms.by_fact.get(&(&fact, 0)).ok_or_else(|| missing("the event of a condition"))?;
                    assume.insert(((*atom).clone(), *denied == flip));
                }
                Condition::Holds { subject, value, denied } => {
                    let fact = Fact::State { subject: self.name(subject), value: value.clone() };
                    let atom = atoms.by_fact.get(&(&fact, 2)).ok_or_else(|| missing("the state of a condition"))?;
                    assume.insert(((*atom).clone(), *denied == flip));
                }
                Condition::Related(relation) => {
                    assume.insert((self.related(relation).ok_or("a relation without individuals")?, relation.denied == flip));
                }
                Condition::Kind { kind, subject, denied } => {
                    assume.insert((self.kind(kind, subject).ok_or("a kind without an individual")?, *denied == flip));
                }
                Condition::Compares { .. } => return Err("a comparison, which this check does not derive".to_string()),
            }
            Ok(())
        };
        for frame in &meaning.frames {
            if frame.any && frame.conditions.len() > 1 {
                return Err("an alternative of conditions, which this check does not derive".to_string());
            }
            for condition in &frame.conditions {
                conditional(condition, false, &mut assume)?;
            }
        }
        if let Some(exception) = &meaning.exception {
            conditional(exception, true, &mut assume)?;
        }
        let mut guarantee = BTreeSet::new();
        let mut deadlines = Vec::new();
        let mut one_of: Vec<BTreeSet<Atom>> = Vec::new();
        if meaning.choice == Choice::Either && meaning.responses.len() > 1 {
            return Err("a choice between actions, which this check does not derive".to_string());
        }
        for response in &meaning.responses {
            match response {
                Response::Action { pattern, deadline, after, before } => {
                    let fact = self.occurs(pattern);
                    let Atom::Act { key } = (*atoms.by_fact.get(&(&fact, 1)).ok_or_else(|| missing("the action of a response"))?).clone() else { return Err("an action without an action atom".to_string()) };
                    let act = Atom::Act { key: key.clone() };
                    let forbid = Atom::Forbid { key: key.clone() };
                    let discouraged = Atom::Discouraged { key: key.clone() };
                    // An order restricts where a prohibition forbids: the
                    // placement over the moments of a trace states it, and
                    // the contract holds the prohibition as it stands.
                    let _ = (after, before);
                    match meaning.force {
                        Force::Obligation => {
                            guarantee.extend([(act, true), (forbid, false), (discouraged, false)]);
                            // A required action with a role is also the action without its roles.
                            if let Fact::Occurs { verb, particle, actor, object, roles } = &fact {
                                if !roles.is_empty() {
                                    let base = Fact::Occurs { verb: verb.clone(), particle: particle.clone(), actor: actor.clone(), object: object.clone(), roles: Vec::new() };
                                    let Some(Atom::Act { key: base_key }) = atoms.by_fact.get(&(&base, 1)).map(|a| (*a).clone()) else { return Err(missing("the action without its roles")) };
                                    guarantee.extend([(Atom::Act { key: base_key.clone() }, true), (Atom::Forbid { key: base_key }, false)]);
                                }
                            }
                            if let Some(deadline) = deadline {
                                deadlines.push((key, deadline.thousandths));
                            }
                        }
                        Force::Prohibition => guarantee.extend([(act, false), (forbid, true)]),
                        Force::Recommendation => guarantee.extend([(forbid, false), (discouraged, false)]),
                        Force::RecommendationAgainst => {
                            guarantee.insert((discouraged, true));
                        }
                        Force::Permission => {
                            guarantee.insert((forbid, false));
                        }
                        Force::Description => return Err("an action of a statement without a modal verb".to_string()),
                    }
                }
                Response::State { subject, value, denied } => {
                    let fact = Fact::State { subject: self.name(subject), value: value.clone() };
                    let atom = atoms.by_fact.get(&(&fact, 2)).ok_or_else(|| missing("the state of a response"))?;
                    guarantee.insert(((*atom).clone(), !denied));
                }
                Response::Values { subject, values } => {
                    // Each listed state belongs to the subject, and the subject is in one of them.
                    let mut listed = BTreeSet::new();
                    for value in values {
                        let fact = Fact::State { subject: self.name(subject), value: value.clone() };
                        let Some(Atom::Val { attr, value }) = atoms.by_fact.get(&(&fact, 2)).map(|a| (*a).clone()) else { return Err(missing("a listed state")) };
                        guarantee.insert((Atom::Dom { attr: attr.clone(), value: value.clone() }, true));
                        listed.insert(Atom::Val { attr, value });
                    }
                    one_of.push(listed);
                }
                Response::Related(relation) => {
                    guarantee.insert((self.related(relation).ok_or("a relation without individuals")?, !relation.denied));
                }
                Response::Kind { kind, subject, denied } => {
                    guarantee.insert((self.kind(kind, subject).ok_or("a kind without an individual")?, !denied));
                }
                Response::Bound { .. } => return Err("a bound, which this check does not derive".to_string()),
            }
        }
        Ok(Expected { assume, eligible, guarantee, deadlines, one_of })
    }
}

/// What was checked and what was refused.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Checked {
    pub refusals: Vec<Refusal>,
    /// The statements whose record was derived again and agrees.
    pub statements: usize,
    /// The instances whose contract is the one that the meaning requires.
    pub contracts: usize,
    /// The instances whose contract holds a form that this check does not
    /// derive: each with the form.
    pub not_derived: Vec<(String, String)>,
    /// The statements about individuals whose tree was read again from
    /// their text and agrees, and the number of those statements.
    pub texts: usize,
    pub of_texts: usize,
    /// The statements whose text holds a form outside the grammar of the
    /// second reading: each with the form.
    pub not_read: Vec<(String, String)>,
}

/// Checks the typed reading of a set against its statements.
pub fn check(set: &SpecSet, model: &Model, lex: &Lexicon) -> Checked {
    let mut out = Checked::default();
    let Some(individuals) = &model.individuals else { return out };
    let refuse = |subject: &str, what: String, out: &mut Checked| out.refusals.push(Refusal { subject: subject.to_string(), what });
    if individuals.version != VERSION {
        refuse("the reading", format!("the records are of the semantic version {} and this checker implements {VERSION}", individuals.version), &mut out);
        return out;
    }
    let carriers: BTreeMap<String, String> = individuals.types.iter().cloned().collect();
    let recorded: BTreeMap<&str, &Meaning> = individuals.meanings.iter().map(|m| (m.statement.as_str(), m)).collect();
    let outside: BTreeSet<&str> = individuals.outside.iter().map(|o| o.statement.id.as_str()).collect();
    let domain: BTreeSet<&str> = individuals.domain.iter().map(|d| d.statement.as_str()).collect();
    // Each statement of the set against its record.
    let mut statements: Vec<(String, &Spec, Lexicon)> = Vec::new();
    for pkg in &set.packages {
        for doc in &pkg.documents {
            let scoped = lex.in_document(doc);
            for spec in &doc.specs {
                let id = if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) };
                statements.push((id, spec, scoped.clone()));
            }
        }
    }
    // The nouns that the package declares: the types of its individuals,
    // its primitive terms and its measures.
    let mut nouns: BTreeSet<String> = BTreeSet::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        for declared in doc.individuals.iter().chain(&doc.primitives).chain(&doc.measures) {
            nouns.insert(declared.name.to_lowercase());
        }
    }
    // The type of each noun, from the declarations and the text of the
    // statements `Each A is a B.`: the nouns that such statements join are
    // of one type, named by the first of its declared nouns.
    let declared: BTreeSet<String> = set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.individuals).map(|decl| decl.name.to_lowercase()).collect();
    let mut joined: Vec<(String, String)> = Vec::new();
    for (_, spec, _) in &statements {
        joined.extend(crate::surface::kind(&spec.sentence.source, &nouns));
    }
    for (noun, carrier) in &individuals.types {
        if !nouns.contains(noun) {
            out.not_read.push((format!("the noun `{noun}`"), "a name that no declaration of the package states in these words: its resolution is not derived again".to_string()));
            continue;
        }
        let mut reached: BTreeSet<&str> = BTreeSet::from([noun.as_str()]);
        loop {
            let more: Vec<&str> = joined.iter().flat_map(|(a, b)| [(a, b), (b, a)]).filter(|(from, to)| reached.contains(from.as_str()) && !reached.contains(to.as_str())).map(|(_, to)| to.as_str()).collect();
            if more.is_empty() {
                break;
            }
            reached.extend(more);
        }
        let first = reached.iter().copied().filter(|name| declared.contains(*name)).min();
        if first != Some(carrier.as_str()) {
            refuse(noun, format!("the reading takes `{noun}` for a noun of the type `{carrier}`, and the declarations with the statements of the form `Each A is a B.` give {}", first.map_or("no declared type".to_string(), |name| format!("`{name}`"))), &mut out);
        }
    }
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    for (id, spec, scoped) in &statements {
        let mut named = Vec::new();
        heads(&serde_json::to_value(&spec.sentence).unwrap_or_default(), &mut named);
        let second_reader = Second { lex: scoped, carriers: &carriers, variables: Vec::new(), restrictions: Vec::new(), site: Site::Condition, share: None, obliged: false };
        let typed = named.iter().any(|head| carriers.contains_key(&second_reader.head(&Np::bare(head))));
        // The tree of a statement about individuals against its text.
        if typed && (recorded.contains_key(id.as_str()) || domain.contains(id.as_str())) {
            out.of_texts += 1;
            match crate::surface::check(&spec.sentence.source, &spec.sentence, &nouns) {
                crate::surface::Read::Agrees => out.texts += 1,
                crate::surface::Read::Differs { text, tree } => refuse(id, format!("the tree of the statement differs from its text: read from the text it is `{text}`, and the tree says `{tree}`"), &mut out),
                crate::surface::Read::NotRead(why) => out.not_read.push((id.clone(), why)),
            }
        }
        match recorded.get(id.as_str()) {
            None if typed && !outside.contains(id.as_str()) && !domain.contains(id.as_str()) => refuse(id, "the statement names a declared type, and the reading holds no record of it, does not list it as outside the fragment and does not read it as a statement about the domain".to_string(), &mut out),
            None => {}
            Some(record) => {
                seen.insert(id.as_str());
                let mut found = Vec::new();
                if record.version != VERSION {
                    found.push(format!("the record is of the semantic version {}", record.version));
                }
                for step in &record.steps {
                    if !RULES.contains(&step.rule) {
                        found.push(format!("the step `{}` names no rule of the semantic version {VERSION}", step.rule));
                    }
                }
                if record.steps.iter().filter(|s| s.rule == "variable" || s.rule == "variable-some" || s.rule == "variable-any").count() != record.variables.len() || record.steps.iter().filter(|s| s.rule == "variable-some").count() != record.variables.iter().filter(|v| v.site == Site::Chosen).count() {
                    found.push("the steps do not introduce each variable once".to_string());
                }
                match second(id, &spec.sentence, &carriers, scoped) {
                    Err(why) => found.push(format!("the statement holds {why}, which no rule of the version reads over individuals, and the reading holds a record of it")),
                    Ok(derived) => {
                        differs("variables", &record.variables, &derived.variables, &mut found);
                        differs("restrictions", &record.restrictions, &derived.restrictions, &mut found);
                        differs("frames", &record.frames, &derived.frames, &mut found);
                        differs("exception", &record.exception, &derived.exception, &mut found);
                        differs("force", &record.force, &derived.force, &mut found);
                        differs("choice", &record.choice, &derived.choice, &mut found);
                        differs("responses", &record.responses, &derived.responses, &mut found);
                        differs("share", &record.share, &derived.share, &mut found);
                    }
                }
                if found.is_empty() {
                    out.statements += 1;
                }
                for what in found {
                    refuse(id, what, &mut out);
                }
            }
        }
    }
    for id in recorded.keys().filter(|id| !seen.contains(*id)) {
        refuse(id, "the reading holds a record of a statement that the set does not hold".to_string(), &mut out);
    }
    // Each atom stands for one fact, and each fact has one atom of a kind.
    let mut of_atom: BTreeMap<&Atom, &Fact> = BTreeMap::new();
    let mut atoms = Atoms { by_fact: BTreeMap::new() };
    for entry in &individuals.atoms {
        if let Some(other) = of_atom.insert(&entry.atom, &entry.fact) {
            if other != &entry.fact {
                refuse(&entry.atom.to_string(), format!("the atom stands for two facts: {other:?} and {:?}", entry.fact), &mut out);
            }
        }
        if let Some(other) = atoms.by_fact.insert((&entry.fact, kind_of(&entry.atom)), &entry.atom) {
            if other != &entry.atom {
                refuse(&entry.atom.to_string(), format!("the fact {:?} has two atoms: {other} and {}", entry.fact, entry.atom), &mut out);
            }
        }
    }
    // The instances of each statement: each assignment over the domain once.
    let scope = individuals.scope;
    let mut by_statement: BTreeMap<&str, Vec<&trion_language::reading::InstanceOf>> = BTreeMap::new();
    for instance in &individuals.instances {
        by_statement.entry(instance.statement.as_str()).or_default().push(instance);
    }
    for (id, record) in &recorded {
        let instances = by_statement.get(id).cloned().unwrap_or_default();
        // A statement that bounds a share stands for one bound on the
        // quantity of the share, and its instances are counted: none of
        // them is a contract of its own.
        if let Some(share) = &record.share {
            if model.constraints.iter().any(|c| c.refs.first().is_some_and(|r| instances.iter().any(|i| i.instance == r.id))) {
                refuse(id, "an instance of a statement that bounds a share stands as a contract of its own".to_string(), &mut out);
            }
            let quantities: Vec<&str> = individuals.shares.iter().filter(|s| s.statement == **id).map(|s| s.quantity.as_str()).collect();
            let [quantity] = quantities.as_slice() else {
                refuse(id, format!("{} quantities hold the share of the statement", quantities.len()), &mut out);
                continue;
            };
            if !quantity.ends_with(&format!(" share of {}", share.population)) {
                refuse(id, format!("the quantity `{quantity}` is no share of `{}`", share.population), &mut out);
            }
            // The bound: the comparison and the thousandths of a percent.
            let bounds: Vec<&trion_language::reading::Constraint> = model.constraints.iter().filter(|c| c.refs.first().is_some_and(|r| r.id == **id)).collect();
            let mut stated = BTreeSet::new();
            let read = match bounds.as_slice() {
                [bound] => bound.assume == Formula::True && literals(&bound.guarantee, true, &mut stated),
                _ => false,
            };
            let expected: BTreeSet<(Atom, bool)> = match share.bounding {
                Bounding::AtLeast => vec![Cmp::Ge],
                Bounding::AtMost => vec![Cmp::Le],
                Bounding::MoreThan => vec![Cmp::Gt],
                Bounding::LessThan => vec![Cmp::Lt],
                Bounding::Exactly => vec![Cmp::Eq],
            }
            .into_iter()
            .map(|cmp| (Atom::Num { attr: quantity.to_string(), unit: "percent".to_string(), cmp, n: share.thousandths }, true))
            .collect();
            if !read || stated != expected {
                refuse(id, format!("the bound of the contract is {}, and the meaning of the statement gives {}", shown(&stated), shown(&expected)), &mut out);
            }
        }
        // An instance binds each variable but those that the response chooses.
        let bound: Vec<&Variable> = record.variables.iter().filter(|v| v.site != Site::Chosen).collect();
        let chosen: Vec<&Variable> = record.variables.iter().filter(|v| v.site == Site::Chosen).collect();
        let none = vec![0; record.variables.len()];
        let assignments = tuples(&bound, &record.variables, &none, scope);
        let expected = assignments.len();
        let distinct: BTreeSet<Vec<&String>> = instances.iter().map(|i| i.binding.iter().map(|(_, name)| name).collect()).collect();
        if instances.len() != expected || distinct.len() != expected {
            refuse(id, format!("{} instances with {} distinct assignments stand for the statement, and {} variables over {scope} individuals, those of one noun different, give {expected}", instances.len(), distinct.len(), bound.len()), &mut out);
        }
        for instance in instances {
            let mut index = none.clone();
            let well = instance.binding.len() == bound.len()
                && instance.binding.iter().zip(&bound).all(|((key, name), variable)| {
                    let number = name.strip_prefix(&format!("{}#", variable.carrier)).and_then(|n| n.parse::<usize>().ok()).filter(|n| (1..=scope).contains(n));
                    index[variable.id as usize] = number.unwrap_or(0);
                    *key == variable.key && number.is_some()
                });
            if !well || !assignments.contains(&index) {
                refuse(&instance.instance, "the binding of the instance does not give each variable an individual of its carrier within the domain, those of one noun different".to_string(), &mut out);
                continue;
            }
            // An instance of a statement that bounds a share is counted: its contract stands with the counted ones.
            let contracts: Vec<&trion_language::reading::Constraint> = if record.share.is_some() {
                model.counted.iter().filter(|counted| counted.statement == **id).map(|counted| &counted.constraint).filter(|c| c.refs.first().is_some_and(|r| r.id == instance.instance)).collect()
            } else {
                model.constraints.iter().filter(|c| c.refs.first().is_some_and(|r| r.id == instance.instance)).collect()
            };
            // The contract of the instance for each choice of the response:
            // one for an instance that chooses nothing.
            let mut choices: Vec<Expected> = Vec::new();
            let mut underived = None;
            for full in tuples(&chosen, &record.variables, &index, scope) {
                let names = record.variables.iter().map(|v| format!("{}#{}", v.carrier, full[v.id as usize])).collect();
                match (Instance { meaning: record, names, index: full }).expected(&atoms) {
                    Ok(expected) => choices.push(expected),
                    Err(form) => underived = Some(form),
                }
            }
            if let Some(form) = underived {
                out.not_derived.push((instance.instance.clone(), form));
                continue;
            }
            let [contract] = contracts.as_slice() else {
                refuse(&instance.instance, format!("{} contracts stand for the instance", contracts.len()), &mut out);
                continue;
            };
            let mut assume = BTreeSet::new();
            if !literals(&contract.assume, true, &mut assume) {
                out.not_derived.push((instance.instance.clone(), "a condition that is no conjunction of literals".to_string()));
                continue;
            }
            // What the contract requires: the guarantee itself, or one of
            // the alternatives of a response that chooses an individual.
            let parts: Vec<&Formula> = match (&contract.guarantee, chosen.is_empty()) {
                (whole, true) => vec![whole],
                (Formula::Or(items), false) if choices.len() != 1 => items.iter().collect(),
                (whole, false) => vec![whole],
            };
            let mut wrong = Vec::new();
            let mut open = None;
            if parts.len() != choices.len() {
                wrong.push(format!("the contract holds {} alternatives, and the individuals that the response may choose give {}", parts.len(), choices.len()));
            }
            if choices.first().is_some_and(|expected| assume != expected.assume) {
                wrong.push(format!("the condition of the contract is {}, and the meaning of the instance gives {}", shown(&assume), shown(&choices[0].assume)));
            }
            for (part, expected) in parts.iter().zip(&choices) {
                let mut guarantee = BTreeSet::new();
                let mut one_of: Vec<BTreeSet<Atom>> = Vec::new();
                if !guarantee_parts(part, &mut guarantee, &mut one_of) {
                    open = Some("a guarantee that is no conjunction of literals".to_string());
                    break;
                }
                // The bounds of the deadlines stand beside the literals of the status.
                let bounds: Vec<(Atom, bool)> = guarantee.iter().filter(|(atom, _)| matches!(atom, Atom::Num { .. } | Atom::Lin { .. })).cloned().collect();
                guarantee.retain(|(atom, _)| !matches!(atom, Atom::Num { .. } | Atom::Lin { .. }));
                let required: BTreeSet<(Atom, bool)> = expected.guarantee.union(&expected.eligible).cloned().collect();
                if guarantee != required {
                    wrong.push(format!("the guarantee of the contract is {}, and the meaning of the instance gives {}", shown(&guarantee), shown(&required)));
                }
                one_of.sort();
                let mut listed = expected.one_of.clone();
                listed.sort();
                if one_of != listed {
                    wrong.push(format!("the contract holds one of {:?}, and the meaning of the instance gives one of {:?}", one_of.iter().map(|atoms| atoms.iter().map(Atom::to_string).collect::<Vec<_>>()).collect::<Vec<_>>(), listed.iter().map(|atoms| atoms.iter().map(Atom::to_string).collect::<Vec<_>>()).collect::<Vec<_>>()));
                }
                let stated: Vec<(String, i64)> = bounds
                    .iter()
                    .filter_map(|(atom, positive)| match atom {
                        Atom::Num { attr, unit, cmp: Cmp::Le, n } if *positive && unit == "ms" => Some((attr.clone(), *n)),
                        _ => None,
                    })
                    .collect();
                if stated.len() != bounds.len() || stated.len() != expected.deadlines.len() || !expected.deadlines.iter().all(|(key, thousandths)| stated.iter().any(|(attr, n)| attr.starts_with(key.as_str()) && n == thousandths)) {
                    wrong.push(format!("the bounds of the contract are {:?}, and the deadlines of the instance give {:?} in thousandths of a millisecond", bounds.iter().map(|(a, _)| a.to_string()).collect::<Vec<_>>(), expected.deadlines));
                }
            }
            if let Some(form) = open {
                out.not_derived.push((instance.instance.clone(), form));
                continue;
            }
            if wrong.is_empty() {
                out.contracts += 1;
            }
            for what in wrong {
                refuse(&instance.instance, what, &mut out);
            }
        }
    }
    out
}

/// Each assignment of the named variables over the individuals `1..=scope`
/// beside what `base` assigns (0 for no individual), in which the
/// variables of one noun name different individuals. The first variable
/// changes slowest.
fn tuples(variables: &[&Variable], all: &[Variable], base: &[usize], scope: usize) -> Vec<Vec<usize>> {
    let mut found = vec![base.to_vec()];
    for variable in variables {
        found = found
            .into_iter()
            .flat_map(|done| {
                (1..=scope).map(move |number| {
                    let mut next = done.clone();
                    next[variable.id as usize] = number;
                    next
                })
            })
            .collect();
    }
    found.retain(|index| all.iter().enumerate().all(|(at, first)| all[at + 1..].iter().all(|second| first.noun != second.noun || index[first.id as usize] == 0 || index[first.id as usize] != index[second.id as usize])));
    found
}

fn shown(literals: &BTreeSet<(Atom, bool)>) -> String {
    let parts: Vec<String> = literals.iter().map(|(atom, positive)| format!("{}{atom}", if *positive { "" } else { "¬" })).collect();
    format!("{{{}}}", parts.join(", "))
}
