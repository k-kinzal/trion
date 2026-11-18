//! Composite vocabulary: what abbreviates several sentences in one.
//!
//! `The API shall store the message and log the message.` says what the two
//! sentences `The API shall store the message.` and `The API shall log the
//! message.` say, and nothing else. [`expand`] gives the sentences that a
//! sentence abbreviates; a sentence without composite vocabulary is *simple*
//! and expands to itself. Every reading of a sentence is the reading of its
//! expansion: composite vocabulary has no meaning of its own.
//!
//! The composite vocabulary is `and` between the parts of a requirement:
//!
//! - between whole clauses (`A shall stop, and B shall log the call`);
//! - between verb phrases (`shall store the message and log the message`),
//!   each with its own polarity (`shall notify the customer and shall not
//!   create an order`);
//! - between the subjects of a sentence (`A and B shall stop`, `A and B
//!   are open`, `There is an A and a B`);
//! - between the objects of a verb (`shall store the message and the call`);
//! - between the noun phrases of a role (`shall send it to A and B`).
//!
//! Under `not`, `or` is the same abbreviation: `shall not store or log the
//! message` denies each.
//!
//! What is no composite vocabulary, and stays one sentence with one
//! contract: `or` and `either … or` in a requirement that is not denied (a
//! choice is one requirement), every coordination inside a condition (a
//! condition is one assumption), and an action list or a flow.
//!
//! A sentence is distributed only where distribution keeps its meaning. It
//! is rejected, and not read some other way,
//!
//! - when what its parts share is counted (`Some user shall log in and log
//!   out`: the two sentences would not speak of the same user);
//! - when a clause depends on the claim as a whole (`… only when C`,
//!   `… exactly when C`: `A and B only when C` is not `A only when C` and
//!   `B only when C`);
//! - when a measure follows the last of several verb phrases (`shall
//!   validate the request and respond within 5 seconds`: the measure is
//!   written once and may bound one phrase or all of them);
//! - when `and` stands under `not` (`shall not store the message and the
//!   call`: the sentence may deny each part or the parts together; `or`
//!   denies each). Between verb phrases the parser refuses the same
//!   (`shall not store the message and log the call`), because only it
//!   sees whether the modal verb is written before each phrase;
//! - when a part names what another part introduces (`shall create a
//!   report and send the report`, `shall notify a member and notify a
//!   second member`: the sentence of the one part would not speak of the
//!   thing of the other).
//!
//! Each rule rests on a fact about contracts, and each fact is a theorem of
//! `formal/Trion/Distribution.lean`:
//!
//! - `and` between parts gives one sentence for each part, each with the
//!   conditions of the sentence: theorem `and_distributes`;
//! - a subject with `the`, `a`, `each`, `every`, `all` or `any` is repeated
//!   in each part: theorem `every_distributes`;
//! - `or` under `not` denies each part: theorem `denied_or_distributes`;
//! - a choice is one requirement: theorem `choice_is_one_requirement`;
//! - a condition is one assumption: theorem `condition_is_one_assumption`;
//! - `and` under `not` is refused: theorem `denied_and_does_not_distribute`;
//! - a counted subject (`some`, `at least two`, `exactly one`) is refused,
//!   and so is a thing that one part introduces and another part names:
//!   theorem `some_does_not_distribute`;
//! - a subject with `no` is refused: theorem `no_does_not_distribute`;
//! - `only when` about the claim as a whole is refused: theorem
//!   `only_when_does_not_distribute`;
//! - `exactly when` about the claim as a whole is refused: theorem
//!   `exactly_when_does_not_distribute`;
//! - a measure after the last of several verb phrases is refused: theorem
//!   `measure_readings_differ`.

use super::ast::*;

/// Why a sentence with composite vocabulary has no expansion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NotDistributive {
    pub reason: String,
}

fn refuse<T>(reason: impl Into<String>) -> Result<T, NotDistributive> {
    Err(NotDistributive { reason: reason.into() })
}

/// A determiner under which a noun phrase names the same things in each
/// sentence that repeats it.
fn repeats(np: &Np) -> bool {
    match &np.det {
        None | Some(Det::The | Det::A | Det::An | Det::Each | Det::Every | Det::All | Det::Any | Det::Reference { .. }) => true,
        Some(Det::No | Det::AtLeast { .. } | Det::AtMost { .. } | Det::Exactly { .. } | Det::Cardinal { .. } | Det::ZeroOrMore | Det::OneOrMore | Det::Some | Det::Both) => false,
    }
}

fn nps(group: &NpGroup) -> &[Np] {
    match group {
        NpGroup::Single(np) => std::slice::from_ref(np),
        NpGroup::Coordinated { items, .. } => items,
    }
}

/// The noun phrases of a group as the groups of the sentences that the
/// group abbreviates: `and` always, and `or` where the claim is denied.
fn parts_of(group: &NpGroup, denied: bool) -> Option<Vec<NpGroup>> {
    match group {
        NpGroup::Coordinated { conj, items, .. } if *conj == Conj::And || denied => Some(items.iter().cloned().map(NpGroup::Single).collect()),
        NpGroup::Single(_) | NpGroup::Coordinated { .. } => None,
    }
}

/// The parts of a group inside a claim that may be denied: the objects of
/// a verb, or the noun phrases of a role. Under `not`, `or` denies each
/// part; `and` under `not` is refused, because denying the parts together
/// is not denying each of them, and the text does not say which is meant.
fn denied_parts_of(group: &NpGroup, denied: bool) -> Result<Option<Vec<NpGroup>>, NotDistributive> {
    match group {
        NpGroup::Coordinated { conj: Conj::And, .. } if denied => refuse(format!("`{}` stands under `not`: the sentence may deny each of them or all of them together; write `or` to deny each, or state each denial in a sentence of its own", group.render())),
        NpGroup::Single(_) | NpGroup::Coordinated { .. } => Ok(parts_of(group, denied)),
    }
}

/// The group of a role that names things, when the role has one.
fn role_group(role: &mut RolePp) -> Option<&mut NpGroup> {
    match role {
        RolePp::Recipient(np) | RolePp::Topic(np) | RolePp::Source(np) | RolePp::Goal(np) | RolePp::Agent(np) => Some(np),
        RolePp::Means { np, .. } | RolePp::Location { np, .. } | RolePp::Other { np, .. } => Some(np),
        RolePp::Deadline(_) | RolePp::Duration(_) | RolePp::Rate { .. } | RolePp::Before(_) | RolePp::After(_) | RolePp::Until(_) => None,
    }
}

/// A role that states a measure of the verb phrase that it follows.
fn measures(role: &RolePp) -> bool {
    match role {
        RolePp::Deadline(_) | RolePp::Duration(_) | RolePp::Rate { .. } => true,
        RolePp::Recipient(_) | RolePp::Topic(_) | RolePp::Source(_) | RolePp::Goal(_) | RolePp::Agent(_) | RolePp::Means { .. } | RolePp::Location { .. } | RolePp::Other { .. } | RolePp::Before(_) | RolePp::After(_) | RolePp::Until(_) => false,
    }
}

/// The claims that one claim of a subject and its verb phrases abbreviates,
/// or nothing when it holds no composite vocabulary. Each has a subject, a
/// polarity and a verb phrase of its own, and `claim` states it: as a
/// requirement with the modal verb of the sentence, or as a relation.
fn split_claim(subject: &NpGroup, negated: bool, vp: &VpGroup, requirement: &dyn Fn(NpGroup, bool, Vp) -> Core) -> Result<Option<Vec<Core>>, NotDistributive> {
    // What the sentences of a split repeat names the same things in each.
    let shared = |what: &str| -> Result<(), NotDistributive> {
        match nps(subject).iter().find(|np| !repeats(np)) {
            Some(np) => refuse(format!("`{}` is counted, and each sentence that {what} would abbreviate counts for itself: the sentences would not speak of the same things; state each requirement in a sentence of its own", np.render())),
            None => Ok(()),
        }
    };
    match vp {
        VpGroup::All { items, negated: polarity } => {
            shared("the verb phrases")?;
            if let Some((last, earlier)) = items.split_last() {
                if let Some(measure) = last.roles.iter().find(|role| measures(role)) {
                    if earlier.iter().any(|item| !item.roles.iter().any(measures)) {
                        return refuse(format!("`{}` follows the last of several verb phrases: it is written once and may bound one phrase or all of them; state it in each verb phrase that it bounds, or state the requirements in sentences of their own", measure.render()));
                    }
                }
            }
            Ok(Some(items.iter().zip(polarity).map(|(item, not)| requirement(subject.clone(), *not, item.clone())).collect()))
        }
        VpGroup::Single(item) => {
            if let Some(subjects) = parts_of(subject, negated) {
                return Ok(Some(subjects.into_iter().map(|one| requirement(one, negated, item.clone())).collect()));
            }
            if let Some(objects) = item.object.as_ref().map(|object| denied_parts_of(object, negated)).transpose()?.flatten() {
                shared("the objects")?;
                return Ok(Some(objects.into_iter().map(|object| requirement(subject.clone(), negated, Vp { object: Some(object), ..item.clone() })).collect()));
            }
            for at in 0..item.roles.len() {
                let mut role = item.roles[at].clone();
                let Some(parts) = role_group(&mut role).map(|group| denied_parts_of(group, negated)).transpose()?.flatten() else { continue };
                shared("the phrases of a role")?;
                let mut out = Vec::new();
                for part in parts {
                    let mut one = item.clone();
                    if let Some(group) = role_group(&mut one.roles[at]) {
                        *group = part;
                    }
                    out.push(requirement(subject.clone(), negated, one));
                }
                return Ok(Some(out));
            }
            Ok(None)
        }
        // A choice is one requirement, and so is an action list or a flow.
        VpGroup::Alternatives { .. } | VpGroup::Composite(_) => Ok(None),
    }
}

/// The copula of one subject of a list: `is` for a subject that is written
/// as one thing.
fn copula_of(subject: &Np, written: Copula) -> Copula {
    let many = subject.head.ends_with('s') && !["ss", "us", "is"].iter().any(|ending| subject.head.ends_with(ending));
    if many { written } else { Copula::Is }
}

/// The cores that a core abbreviates, or nothing when it is simple.
fn split(core: &Core) -> Result<Option<Vec<Core>>, NotDistributive> {
    match core {
        Core::Conjoined { items } => Ok(Some(items.clone())),
        Core::Deontic { subject, modal, negated, vp } => split_claim(subject, *negated, vp, &|subject, negated, vp| Core::Deontic { subject, modal: *modal, negated, vp: VpGroup::Single(vp) }),
        // A relation denies nothing: a verb phrase that is denied is no part
        // of it, and such a relation is no sentence that abbreviates others.
        Core::Relation { vp: VpGroup::All { negated, .. }, .. } if negated.iter().any(|not| *not) => refuse("a relation that denies one of its verb phrases is no relation: state what is denied in a sentence of its own"),
        Core::Relation { subject, vp } => split_claim(subject, false, vp, &|subject, _, vp| Core::Relation { subject, vp: VpGroup::Single(vp) }),
        Core::Description { subject, copula, adverb, predicate, agent, roles } => Ok(parts_of(subject, false).map(|subjects| {
            subjects
                .into_iter()
                .map(|one| {
                    let copula = nps(&one).first().map_or(*copula, |np| copula_of(np, *copula));
                    Core::Description { subject: one, copula, adverb: *adverb, predicate: predicate.clone(), agent: agent.clone(), roles: roles.clone() }
                })
                .collect()
        })),
        Core::Existence { subject } => Ok(parts_of(subject, false).map(|subjects| subjects.into_iter().map(|subject| Core::Existence { subject }).collect())),
        Core::Definition { .. } => Ok(None),
    }
}

/// The words before a head that name a thing by another thing of its kind.
const AGAIN: [&str; 6] = ["second", "third", "fourth", "other", "same", "further"];

/// The things that a phrase introduces (`a report`, `two members`) and the
/// things that it names as already there (`the report`, `its owner`, `a
/// second member`), each by its head, lowercase.
#[derive(Default)]
struct Mentions {
    introduced: Vec<String>,
    named: Vec<String>,
}

impl Mentions {
    /// Reads the noun phrases of a part of the tree of a sentence.
    fn of(part: &impl serde::Serialize) -> Mentions {
        let mut mentions = Mentions::default();
        if let Ok(tree) = serde_json::to_value(part) {
            mentions.read(&tree);
        }
        mentions
    }

    fn read(&mut self, tree: &serde_json::Value) {
        match tree {
            serde_json::Value::Object(fields) => {
                // A noun phrase: a head with its determiner and its modifiers.
                if let (Some(head), Some(modifiers)) = (fields.get("head").and_then(|head| head.as_str()), fields.get("modifiers").and_then(|modifiers| modifiers.as_array())) {
                    let head = head.to_lowercase();
                    let again = modifiers.iter().filter_map(|word| word.as_str()).any(|word| AGAIN.contains(&word.to_lowercase().as_str()));
                    match fields.get("det").and_then(|det| det.get("kind")).and_then(|kind| kind.as_str()) {
                        Some("the" | "reference") => self.named.push(head),
                        _ if again => self.named.push(head),
                        Some("a" | "an" | "some" | "cardinal" | "at_least" | "at_most" | "exactly" | "zero_or_more" | "one_or_more") => self.introduced.push(head),
                        _ => {}
                    }
                }
                fields.values().for_each(|field| self.read(field));
            }
            serde_json::Value::Array(items) => items.iter().for_each(|item| self.read(item)),
            _ => {}
        }
    }
}

/// The thing that one part of a sentence introduces and another part
/// names, when there is one. What the conditions of the sentence introduce
/// stands in every part and is named in each.
fn shared_thing(sentence: &Sentence, parts: &[Core]) -> Option<String> {
    let conditions = Mentions::of(&sentence.frames);
    let mentions: Vec<Mentions> = parts.iter().map(Mentions::of).collect();
    for (at, part) in mentions.iter().enumerate() {
        for thing in part.introduced.iter().filter(|thing| !conditions.introduced.contains(thing)) {
            if mentions.iter().enumerate().any(|(other, mention)| other != at && mention.named.contains(thing)) {
                return Some(thing.clone());
            }
        }
    }
    None
}

/// The simple sentences that a sentence abbreviates, in the order of its
/// parts: the sentence itself when it holds no composite vocabulary. Each
/// sentence of the result is a sentence of the language: its text is
/// [`Sentence::render`], and reading that text gives the sentence back.
pub fn expand(sentence: &Sentence) -> Result<Vec<Sentence>, NotDistributive> {
    let mut simple = Vec::new();
    let mut pending = vec![sentence.core.clone()];
    while let Some(core) = pending.pop() {
        match split(&core)? {
            Some(parts) => pending.extend(parts.into_iter().rev()),
            None => simple.push(core),
        }
    }
    if simple.len() == 1 {
        return Ok(vec![sentence.clone()]);
    }
    // A clause that depends on the claim as a whole does not distribute.
    if let Some(clause) = sentence.necessary.as_ref().map(|c| format!("only when {}", c.render())).or_else(|| sentence.iff.as_ref().map(|c| format!("exactly when {}", c.render()))) {
        return refuse(format!("`{clause}` depends on the claim as a whole, and the claim abbreviates {} requirements: the clause of all of them together is not the clause of each; state each requirement with its clause in a sentence of its own", simple.len()));
    }
    // A part that names what another part introduces is no sentence of its own.
    if let Some(thing) = shared_thing(sentence, &simple) {
        return refuse(format!("one part introduces `{thing}` and another part names it: the sentences of the parts would not speak of the same {thing}; state the requirement about the {thing} in one sentence, as an action list does, or name the {thing} in each part"));
    }
    let mut out = Vec::new();
    for core in simple {
        let mut one = Sentence { core, ..sentence.clone() };
        let rendered = one.render();
        // A sentence begins with a capital where that keeps its words: the
        // first word of a sentence may be a name that is written small.
        let mut letters = rendered.chars();
        let capital: String = letters.next().map(|first| first.to_uppercase().chain(letters).collect()).unwrap_or_default();
        // The expansion is a sentence of the language: its text is read as itself.
        let Some(source) = [capital, rendered.clone()].into_iter().find(|text| reads_as(text, &one)) else {
            return refuse(format!("`{rendered}` is not read as the requirement that it abbreviates: state each requirement in a sentence of its own"));
        };
        one.source = source;
        out.push(one);
    }
    Ok(out)
}

/// `true` when the text is one sentence of the language and is read as the
/// given sentence.
fn reads_as(text: &str, sentence: &Sentence) -> bool {
    let read = super::parse(text).ok().map(|spec| spec.sentences);
    matches!(read.as_deref(), Some([again]) if Sentence { source: sentence.source.clone(), ..again.clone() } == *sentence)
}

/// `true` when the sentence holds no composite vocabulary.
pub fn is_simple(sentence: &Sentence) -> bool {
    matches!(split(&sentence.core), Ok(None))
}
