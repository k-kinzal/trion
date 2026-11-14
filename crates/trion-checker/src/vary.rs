//! Variations of a behaviour.
//!
//! A scenario states one behaviour, and the comparison of the reference
//! evaluator with the formulas of the reading judges that one. A reading
//! that differs from the meaning only on a behaviour that no scenario
//! states is not found. This module makes the behaviours next to a stated
//! one: each differs from it in one fact (an occurrence left out, moved by
//! a moment or about another individual; a relation left out; another
//! value of a state; a later time). No expectation belongs to a variation:
//! what is examined is that both judgements agree on it, whatever they say.

use crate::world::World;
use std::collections::{BTreeMap, BTreeSet};
use trion_language::reading::typed::Response;
use trion_language::reading::Individuals;

/// One behaviour next to a stated one, with what was changed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Variation {
    pub what: String,
    pub world: World,
}

/// The variations of a behaviour, at most `most` of them, taken in turn
/// from each kind of change.
pub fn variations(world: &World, individuals: &Individuals, most: usize) -> Vec<Variation> {
    let mut kinds: Vec<Vec<Variation>> = Vec::new();
    let vary = |what: String, change: &dyn Fn(&mut World)| {
        let mut next = world.clone();
        change(&mut next);
        Variation { what, world: next }
    };
    // An occurrence left out.
    let mut left_out = Vec::new();
    for (m, moment) in world.moments.iter().enumerate() {
        for occurrence in &moment.occurrences {
            left_out.push(vary(format!("without `{}` at moment {m}", occurrence.describe()), &|w| {
                w.moments[m].occurrences.remove(occurrence);
            }));
        }
    }
    kinds.push(left_out);
    // An occurrence one moment later or earlier.
    let mut moved = Vec::new();
    for (m, moment) in world.moments.iter().enumerate() {
        for occurrence in &moment.occurrences {
            for to in [m + 1, m.wrapping_sub(1)] {
                if to < world.moments.len() {
                    moved.push(vary(format!("with `{}` at moment {to} and not at moment {m}", occurrence.describe()), &|w| {
                        w.moments[m].occurrences.remove(occurrence);
                        w.moments[to].occurrences.insert(occurrence.clone());
                    }));
                }
            }
        }
    }
    kinds.push(moved);
    // An occurrence about another individual of the same carrier.
    let mut about_another = Vec::new();
    let others = |name: &str| -> Vec<&String> {
        let Some(carrier) = world.individuals.get(name) else { return Vec::new() };
        world.individuals.iter().filter(|(other, of)| *of == carrier && other.as_str() != name).map(|(other, _)| other).collect()
    };
    for (m, moment) in world.moments.iter().enumerate() {
        for occurrence in &moment.occurrences {
            let mut places: Vec<(usize, &String)> = vec![(0, &occurrence.actor)];
            places.extend(occurrence.object.iter().map(|object| (1, object)));
            places.extend(occurrence.roles.iter().enumerate().map(|(i, (_, name))| (2 + i, name)));
            for (place, name) in places {
                for other in others(name) {
                    let mut changed = occurrence.clone();
                    match place {
                        0 => changed.actor = other.clone(),
                        1 => changed.object = Some(other.clone()),
                        i => changed.roles[i - 2].1 = other.clone(),
                    }
                    about_another.push(vary(format!("with `{}` in place of `{}` at moment {m}", changed.describe(), occurrence.describe()), &|w| {
                        w.moments[m].occurrences.remove(occurrence);
                        w.moments[m].occurrences.insert(changed.clone());
                    }));
                }
            }
        }
    }
    kinds.push(about_another);
    // A relation left out.
    kinds.push(world.relations.iter().map(|relation| vary(format!("without `{}`({}, {})", relation.0, relation.1, relation.2), &|w| {
        w.relations.remove(relation);
    })).collect());
    // Another listed value of a state, from one moment on.
    let mut listed: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for values in individuals.meanings.iter().flat_map(|m| &m.responses).filter_map(|r| if let Response::Values { values, .. } = r { Some(values) } else { None }) {
        for value in values {
            listed.entry(value.as_str()).or_default().extend(values.iter().map(String::as_str));
        }
    }
    let mut other_value = Vec::new();
    for (m, moment) in world.moments.iter().enumerate() {
        for (subject, value) in &moment.states {
            for other in listed.get(value.as_str()).into_iter().flatten().filter(|other| **other != value.as_str()) {
                other_value.push(vary(format!("with `{subject}` `{other}` and not `{value}` from moment {m} on"), &|w| {
                    for later in &mut w.moments[m..] {
                        if later.states.remove(&(subject.clone(), value.clone())) {
                            later.states.insert((subject.clone(), other.to_string()));
                        }
                    }
                }));
            }
        }
    }
    kinds.push(other_value);
    // A moment, and each later one, later by a stated deadline and by one millisecond more.
    let deadlines: BTreeSet<i64> = individuals.meanings.iter().flat_map(|m| &m.responses).filter_map(|r| if let Response::Action { deadline: Some(deadline), .. } = r { Some(deadline.thousandths / 1000) } else { None }).collect();
    let mut later = Vec::new();
    for m in 1..world.moments.len() {
        for by in deadlines.iter().flat_map(|d| [*d, *d + 1]) {
            later.push(vary(format!("with moment {m} and each later moment {by} ms later"), &|w| {
                for moment in &mut w.moments[m..] {
                    moment.time += by;
                }
            }));
        }
    }
    kinds.push(later);
    // In turn from each kind, so that a small number of variations holds each kind of change.
    let mut out = Vec::new();
    let mut at = 0;
    while out.len() < most && kinds.iter().any(|kind| at < kind.len()) {
        for kind in &kinds {
            if let (Some(variation), true) = (kind.get(at), out.len() < most) {
                if variation.world != *world && !out.iter().any(|known: &Variation| known.world == variation.world) {
                    out.push(variation.clone());
                }
            }
        }
        at += 1;
    }
    out
}
