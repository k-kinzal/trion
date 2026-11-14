//! A scenario block as a concrete behaviour.
//!
//! ```text
//! scenario STORED:
//!     given a user U1, a room R1, a message M1
//!     given U1 is a member of R1.
//!     at 0 ms: R1 is open.
//!     at 0 ms: U1 posts M1 to R1.
//!     at 1 seconds: the system stores M1.
//!     expect allowed
//! ```
//!
//! The notation, and nothing of the language: a variable names one
//! individual of the scenario; a `given` sentence states a kind (`U1 is an
//! administrator.`) or a relation (`U1 is a member of R1.`); an `at` line
//! states a state (`R1 is open.`) or an occurrence. A state that an `at`
//! line states holds from its time until another state of the same
//! individual is stated. What the block does not state does not exist, does
//! not hold and does not happen.
//!
//! This reader does not use the rules that read a statement over
//! individuals: it reads the few forms of the notation itself.

use crate::world::{Moment, Occurrence, World};
use std::collections::{BTreeMap, BTreeSet};
use trion_language::document::Scenario;
use trion_language::reading::{np_key, Individuals, Lexicon};
use trion_language::syntax::ast::*;

/// What a line of a scenario states that the notation does not read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Problem {
    pub line: usize,
    pub what: String,
}

const ORDINALS: [&str; 5] = ["second", "third", "fourth", "fifth", "sixth"];

/// The base form of a verb in the third person singular.
fn base(verb: &str) -> String {
    let verb = verb.to_lowercase();
    match verb.as_str() {
        "has" => return "have".to_string(),
        "does" => return "do".to_string(),
        _ => {}
    }
    if verb.len() < 3 {
        return verb;
    }
    if let Some(stem) = verb.strip_suffix("ies") {
        return format!("{stem}y");
    }
    if ["sses", "shes", "ches", "xes", "zes", "oes"].iter().any(|ending| verb.ends_with(ending)) {
        return verb[..verb.len() - 2].to_string();
    }
    if verb.ends_with("ss") || verb.ends_with("us") || verb.ends_with("is") {
        return verb;
    }
    verb.strip_suffix('s').unwrap_or(&verb).to_string()
}

struct Reader<'a> {
    lex: &'a Lexicon,
    /// The individual of each noun phrase that stands for a variable: `second user`.
    named: BTreeMap<String, String>,
    /// The noun phrase that each variable is written as.
    phrase: BTreeMap<String, String>,
}

impl Reader<'_> {
    fn noun(&self, words: &[String]) -> String {
        let mut words: Vec<String> = words.iter().map(|w| w.to_lowercase()).collect();
        if let Some(last) = words.last_mut() {
            *last = base(last);
        }
        self.lex.resolve(&self.lex.canon(&words.join(" ")))
    }

    /// The sentence with each variable written as its noun phrase.
    fn written(&self, text: &str) -> String {
        text.split_whitespace()
            .map(|token| {
                let core = token.trim_end_matches([',', ';', '.', ':']);
                match self.phrase.get(core) {
                    Some(phrase) => format!("{phrase}{}", &token[core.len()..]),
                    None => token.to_string(),
                }
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// The name of what a noun phrase denotes: an individual of the scenario, or a thing of the package.
    fn name(&self, np: &Np) -> String {
        let key: Vec<String> = np.modifiers.iter().map(|m| m.to_lowercase()).chain(std::iter::once(self.noun(std::slice::from_ref(&np.head)))).collect();
        if let Some(individual) = self.named.get(&key.join(" ")) {
            return individual.clone();
        }
        // `the mode of R1`: a property of an individual of the scenario.
        if let (Some(owner), true) = (&np.of, np.of_also.is_empty()) {
            let owner_name = self.name(owner);
            if self.named.values().any(|individual| *individual == owner_name) || owner_name.contains(" of ") {
                let bare = Np { of: None, ..np.clone() };
                return format!("{} of {owner_name}", np_key(&bare, self.lex));
            }
        }
        np_key(np, self.lex)
    }

    fn single(&self, group: &NpGroup) -> Option<String> {
        match group {
            NpGroup::Single(np) => Some(self.name(np)),
            NpGroup::Coordinated { .. } => None,
        }
    }

    fn occurrence(&self, clause: &Clause) -> Option<Occurrence> {
        let ClauseBody::Verbal { verb, particle, object, roles, content: None, negation: None, .. } = &clause.body else { return None };
        let mut named = Vec::new();
        for role in roles {
            let (marker, group) = match role {
                RolePp::Recipient(np) => ("to".to_string(), np),
                RolePp::Topic(np) => ("about".to_string(), np),
                RolePp::Source(np) => ("from".to_string(), np),
                RolePp::Goal(np) => ("into".to_string(), np),
                RolePp::Agent(np) => ("by".to_string(), np),
                RolePp::Means { marker, np } => (marker.as_str().to_string(), np),
                RolePp::Location { preposition, np } | RolePp::Other { preposition, np } => (preposition.to_lowercase(), np),
                _ => return None,
            };
            named.push((marker, self.single(group)?));
        }
        let object = match object {
            Some(group) => Some(self.single(group)?),
            None => None,
        };
        Some(Occurrence { verb: base(verb), particle: particle.as_ref().map(|p| p.to_lowercase()), actor: self.single(&clause.subject)?, object, roles: named })
    }
}

/// What a `given` sentence or a state line says of its subject.
enum Stated {
    Kind(String),
    Related { relation: String, owner: String },
    State(String),
}

fn stated(reader: &Reader, words: &[String]) -> Option<Stated> {
    let lower: Vec<String> = words.iter().map(|w| w.to_lowercase()).collect();
    let article = |w: &str| ["a", "an", "the"].contains(&w);
    if let Some(of) = lower.iter().position(|w| w == "of") {
        let relation = lower.get(1..of).filter(|r| !r.is_empty() && article(&lower[0]))?;
        let owner = lower.get(of + 1..)?;
        let owner = owner.strip_prefix(&["the".to_string()][..]).unwrap_or(owner);
        let (head, modifiers) = owner.split_last()?;
        let key: Vec<String> = modifiers.iter().cloned().chain(std::iter::once(reader.noun(std::slice::from_ref(head)))).collect();
        let owner = reader.named.get(&key.join(" "))?.clone();
        return Some(Stated::Related { relation: reader.noun(relation), owner });
    }
    match lower.split_first() {
        Some((first, rest)) if ["a", "an"].contains(&first.as_str()) && !rest.is_empty() => Some(Stated::Kind(reader.noun(rest))),
        Some(_) if !lower.iter().any(|w| article(w) || w == "not") => Some(Stated::State(lower.join(" "))),
        _ => None,
    }
}

/// Reads a scenario as a behaviour.
pub fn world(scenario: &Scenario, individuals: &Individuals, lex: &Lexicon) -> Result<World, Vec<Problem>> {
    let mut problems: Vec<Problem> = Vec::new();
    let mut reader = Reader { lex, named: BTreeMap::new(), phrase: BTreeMap::new() };
    let mut world = World::default();
    let mut of_noun: BTreeMap<String, usize> = BTreeMap::new();
    let mut of_carrier: BTreeMap<String, usize> = BTreeMap::new();
    for (variable, written) in &scenario.individuals {
        let words: Vec<String> = written.split_whitespace().map(str::to_string).collect();
        let noun = reader.noun(&words);
        let Some(carrier) = individuals.types.iter().find(|(known, _)| *known == noun).map(|(_, declared)| declared.clone()) else {
            problems.push(Problem { line: scenario.line, what: format!("`{written}` is no declared type of individuals") });
            continue;
        };
        let nth = of_noun.entry(noun.clone()).or_default();
        *nth += 1;
        let ordinal = match *nth {
            1 => String::new(),
            n if n - 2 < ORDINALS.len() => format!("{} ", ORDINALS[n - 2]),
            _ => {
                problems.push(Problem { line: scenario.line, what: format!("a scenario names at most six individuals of `{written}`") });
                continue;
            }
        };
        let index = of_carrier.entry(carrier.clone()).or_default();
        *index += 1;
        let name = format!("{carrier}#{index}");
        reader.named.insert(format!("{ordinal}{noun}"), name.clone());
        reader.phrase.insert(variable.clone(), format!("the {ordinal}{}", written.to_lowercase()));
        world.individuals.insert(name.clone(), carrier);
        world.kinds.insert((noun, name));
    }
    let described = |reader: &Reader, text: &str| -> Option<(String, Stated)> {
        let sentence = trion_language::parse_sentence(&reader.written(text)).ok()?;
        let Core::Description { subject: NpGroup::Single(subject), predicate: Predicate::Words { words }, agent: None, adverb: None, .. } = &sentence.core else { return None };
        if !sentence.frames.is_empty() || sentence.exception.is_some() {
            return None;
        }
        Some((reader.name(subject), stated(reader, words)?))
    };
    for (line, text) in &scenario.facts {
        match described(&reader, text) {
            Some((subject, Stated::Kind(kind))) => {
                world.kinds.insert((kind, subject));
            }
            Some((subject, Stated::Related { relation, owner })) => {
                world.relations.insert((relation, owner, subject));
            }
            _ => problems.push(Problem { line: *line, what: format!("`{text}` is no kind and no relation of the individuals of the scenario: write `U1 is an administrator.` or `U1 is a member of R1.`") }),
        }
    }
    // The moments in the order of their times; a state holds until another
    // state of the same individual is stated.
    let times: BTreeSet<i64> = scenario.at.iter().map(|(_, time, _)| *time).collect();
    let mut current: BTreeMap<String, String> = BTreeMap::new();
    for time in times {
        let mut moment = Moment { time, ..Default::default() };
        for (line, _, text) in scenario.at.iter().filter(|(_, at, _)| *at == time) {
            if let Some((subject, Stated::State(value))) = described(&reader, text) {
                current.insert(subject, value);
                continue;
            }
            // An occurrence is a clause, and a clause stands in a frame.
            let clause = text.trim_end_matches('.');
            let framed = trion_language::parse_sentence(&format!("When {}, the scenario shall hold.", reader.written(clause)));
            let occurrence = framed.ok().and_then(|sentence| {
                let trigger = sentence.frames.trigger?;
                let [clause] = trigger.clause.items.as_slice() else { return None };
                reader.occurrence(clause)
            });
            match occurrence {
                Some(occurrence) => {
                    moment.occurrences.insert(occurrence);
                }
                None => problems.push(Problem { line: *line, what: format!("`{text}` is no state and no occurrence that the notation of a scenario reads: write `R1 is open.` or `U1 posts M1 to R1.`") }),
            }
        }
        moment.states = current.iter().map(|(subject, value)| (subject.clone(), value.clone())).collect();
        world.moments.push(moment);
    }
    if problems.is_empty() {
        Ok(world)
    } else {
        Err(problems)
    }
}
