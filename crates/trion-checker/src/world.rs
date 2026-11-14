//! A concrete behaviour: individuals, the relations between them, and what
//! holds and what happens at each moment of a finite, complete trace.
//!
//! A world is complete: an individual, a relation, a state or an occurrence
//! that it does not hold does not exist, does not hold or does not happen.
//! After its last moment nothing happens.

use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

/// An event that occurs or an action that completes, with what takes part.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Occurrence {
    pub verb: String,
    pub particle: Option<String>,
    pub actor: String,
    pub object: Option<String>,
    /// Each role with its marker, in the order of the markers.
    pub roles: Vec<(String, String)>,
}

impl Occurrence {
    pub fn describe(&self) -> String {
        let mut text = format!("{} {}", self.actor, self.verb);
        if let Some(particle) = &self.particle {
            text.push_str(&format!(" {particle}"));
        }
        if let Some(object) = &self.object {
            text.push_str(&format!(" {object}"));
        }
        for (marker, name) in &self.roles {
            text.push_str(&format!(" {marker} {name}"));
        }
        text
    }
}

/// One moment: its time in milliseconds, the states that hold at it and
/// what happens at it.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct Moment {
    pub time: i64,
    /// Each state as the individual with the value that it has.
    pub states: BTreeSet<(String, String)>,
    pub occurrences: BTreeSet<Occurrence>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct World {
    /// Each individual with the declared type of its carrier.
    pub individuals: BTreeMap<String, String>,
    /// Each kind with an individual of it: `(member, user#1)`.
    pub kinds: BTreeSet<(String, String)>,
    /// Each relation with its owner and its member: `(member, room#1, user#1)`.
    pub relations: BTreeSet<(String, String, String)>,
    pub moments: Vec<Moment>,
}

impl World {
    /// The individuals of one carrier, in the order of their names.
    pub fn of_carrier(&self, carrier: &str) -> Vec<&str> {
        self.individuals.iter().filter(|(_, c)| c.as_str() == carrier).map(|(name, _)| name.as_str()).collect()
    }

    pub fn is(&self, kind: &str, individual: &str) -> bool {
        self.kinds.contains(&(kind.to_string(), individual.to_string()))
    }

    pub fn related(&self, relation: &str, owner: &str, member: &str) -> bool {
        self.relations.contains(&(relation.to_string(), owner.to_string(), member.to_string()))
    }

    pub fn holds(&self, moment: usize, subject: &str, value: &str) -> bool {
        self.moments.get(moment).is_some_and(|m| m.states.contains(&(subject.to_string(), value.to_string())))
    }

    /// `true` when something of the named kind happens at the moment: an
    /// occurrence with the same verb, actor and object that holds each named
    /// role. An occurrence with a further role is an occurrence of the
    /// same action or event: `notify U1 about M1` is a notifying of U1.
    pub fn occurs(&self, moment: usize, occurrence: &Occurrence) -> bool {
        self.moments.get(moment).is_some_and(|m| m.occurrences.iter().any(|found| found.verb == occurrence.verb && found.particle == occurrence.particle && found.actor == occurrence.actor && found.object == occurrence.object && occurrence.roles.iter().all(|role| found.roles.contains(role))))
    }

    /// The world with what its facts imply by the rules of the domain: an
    /// individual is of its declared type, and what stands in a relation as
    /// its member is of the kind that the relation names (`the owner of a
    /// room` is an owner). A world of fewer than two moments is continued
    /// by moments at which the last states hold and nothing happens.
    pub fn closed(&self) -> World {
        let mut world = self.clone();
        for (name, carrier) in &self.individuals {
            world.kinds.insert((carrier.clone(), name.clone()));
        }
        for (relation, _, member) in &self.relations {
            world.kinds.insert((relation.clone(), member.clone()));
        }
        while world.moments.len() < 2 {
            let last = world.moments.last().cloned().unwrap_or_default();
            world.moments.push(Moment { time: last.time, states: last.states, occurrences: BTreeSet::new() });
        }
        world
    }
}
