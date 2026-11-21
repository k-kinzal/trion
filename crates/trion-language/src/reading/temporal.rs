//! The temporal reading of a statement.
//!
//! The contracts of [`crate::reading::model`] are propositions without time. This
//! module keeps, beside each contract, what the statement says about time:
//! which configurations it selects, what opens an activation, when its
//! conditions are sampled, what its response starts and completes, where a
//! deadline is measured from and how long the obligation lives. The shape is
//! derived from the syntax tree alone, so it is the same whatever stands
//! around the statement. Where a statement leaves a time unresolved, the
//! shape says so and the formalizer reports it.

use crate::diagnostic::{Diagnostic, SpecRef};
use crate::reading::model::{self, Model};
use crate::reading::lexicon::Lexicon;
use trion_solver::{Atom, Cmp, Formula};

/// The name of the occurrence that a noun phrase of a temporal role names,
/// built from the nodes of the phrase as every key is.
fn occurrence_key(group: &crate::syntax::ast::NpGroup, lex: &Lexicon) -> String {
    crate::reading::key::text(&crate::reading::key::group_parts(group, lex))
}
use crate::syntax::ast::*;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

/// What opens the obligation of a statement.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Activation {
    /// Each occurrence of the trigger opens one activation. A state around
    /// the trigger is sampled once, at that occurrence.
    Occurrence { event: String, unwanted: bool, gate: Vec<String> },
    /// Each invocation of the operation that the response names.
    Invocation { operation: String, boundary: String },
    /// Throughout each interval in which the stated conditions hold.
    Interval { conditions: Vec<String> },
    /// Throughout the applicable system scope, with no discrete activation.
    Always,
}

/// Where a deadline is measured from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Origin {
    /// The activation of the enclosing response.
    Activation,
    /// The invocation of the declared operation.
    Invocation,
    /// The start of the interval of the state scope.
    IntervalStart,
    /// An origin that the sentence names.
    Explicit { event: String },
    /// No origin: the deadline has nothing to be measured from.
    Unresolved,
}

/// Which occurrence of a named event a phrase means.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Pick {
    /// The last occurrence before the completion: `the last retry`, `the retry`.
    #[default]
    Last,
    /// The first occurrence of the trace: `the first retry`.
    First,
    /// The first occurrence after the activation: `the next retry`.
    Next,
}

const FIRST_WORDS: [&str; 2] = ["first", "earliest"];
const NEXT_WORDS: [&str; 2] = ["next", "following"];
const LAST_WORDS: [&str; 4] = ["last", "latest", "previous", "preceding"];

fn pick_of(word: &str) -> Option<Pick> {
    let w = word.to_ascii_lowercase();
    let w = w.as_str();
    if FIRST_WORDS.contains(&w) {
        Some(Pick::First)
    } else if NEXT_WORDS.contains(&w) {
        Some(Pick::Next)
    } else if LAST_WORDS.contains(&w) {
        Some(Pick::Last)
    } else {
        None
    }
}

/// `the first failure`: an occurrence that is named by its order. Gives the
/// order word as written.
fn ordered_occurrence(group: &NpGroup) -> Option<(Pick, String)> {
    let NpGroup::Single(np) = group else { return None };
    if !matches!(np.det, Some(Det::The)) || np.of.is_some() || np.relative.is_some() {
        return None;
    }
    let word = np.modifiers.first()?;
    Some((pick_of(word)?, word.to_ascii_lowercase()))
}

/// `the retry` after `before` or `after`: an occurrence that a bare noun names.
fn bare_occurrence(group: &NpGroup) -> bool {
    matches!(group, NpGroup::Single(np) if matches!(np.det, Some(Det::The)) && np.modifiers.is_empty() && np.of.is_none() && np.relative.is_none())
}

/// `at least 2 seconds` before `after`: a bound on the time of the action.
fn delay_bound(role: &RolePp) -> bool {
    let RolePp::Other { preposition, np: NpGroup::Single(np) } = role else { return false };
    ["at least", "at most", "exactly"].contains(&preposition.as_str()) && np.det.is_none() && np.modifiers.len() == 1 && model::is_time_measure(&Measure::Quantity { number: np.modifiers[0].clone(), unit: Some(np.head.clone()) })
}

/// `in a row`: the occurrences that a count names follow each other.
fn in_a_row(role: &RolePp) -> bool {
    matches!(role, RolePp::Location { preposition, np: NpGroup::Single(np) } if preposition.eq_ignore_ascii_case("in") && matches!(np.det, Some(Det::A)) && np.head.eq_ignore_ascii_case("row") && np.modifiers.is_empty() && np.of.is_none() && np.relative.is_none())
}

/// `true` for a role that this module reads as a time and that is therefore
/// no part of the name of the action.
pub(crate) fn is_time_role(role: &RolePp) -> bool {
    delay_bound(role) || in_a_row(role) || matches!(role, RolePp::Other { preposition, np } if ["before", "after"].contains(&preposition.as_str()) && (ordered_occurrence(np).is_some() || bare_occurrence(np)))
}

/// `true` for an adverb that says when the action happens.
pub(crate) fn is_time_manner(word: &str) -> bool {
    ["eventually", "immediately", "always"].contains(&word.to_ascii_lowercase().as_str())
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Deadline {
    /// The event that the sentence names as the origin, for the trace.
    #[serde(skip)]
    pub event: Option<Formula>,
    /// Which occurrence of that event the time is measured from.
    #[serde(skip)]
    pub pick: Pick,
    pub bound: String,
    /// A deadline measures the completion of the response.
    pub measures: String,
    pub origin: Origin,
}

/// A `before`, `after` or `until` phrase of a response.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Reference {
    pub relation: String,
    /// The related event or state, as the model names it.
    pub related: String,
    /// `event` or `state`.
    pub related_kind: String,
    /// Which instants the relation compares.
    pub boundary: String,
    /// The related event or state as a formula, for the trace. `None` for an
    /// occurrence that a noun names, until an event of the package is found.
    #[serde(skip)]
    pub event: Option<Formula>,
    /// `true` when the relation orders the completion on the trace. A clause
    /// that a deadline is measured from is its origin and orders nothing.
    #[serde(skip)]
    pub orders: bool,
    /// Which occurrence a noun phrase names.
    #[serde(skip)]
    pub pick: Option<Pick>,
    /// `true` for a noun without an order word: it is read as an occurrence
    /// only where an action or an event of the package has its name.
    #[serde(skip)]
    pub if_named: bool,
}

/// An adverb of time before the verb of a response.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Timing {
    /// The action completes at the next moment after the activation.
    Immediately,
    /// The action completes at every moment after the activation.
    Always,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ResponseKind {
    /// A discrete action with a start event and a completion event.
    Action { key: String, start: String, completion: String },
    /// A state that holds over an interval.
    State { state: String, holds: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Response {
    #[serde(flatten)]
    pub kind: ResponseKind,
    pub modal: String,
    pub deadline: Option<Deadline>,
    /// A duration constrains the action from its start to its completion.
    pub duration: Option<String>,
    pub references: Vec<Reference>,
    /// The completion that an activated obligation requires eventually.
    pub liveness: Option<String>,
    /// The stated conditions that end the obligation without its completion.
    pub cancellation: Vec<String>,
    /// The `until` conditions as formulas, for the trace.
    #[serde(skip)]
    pub until: Vec<Formula>,
    /// `immediately` or `always` before the verb.
    #[serde(skip)]
    pub timing: Option<Timing>,
    /// `N times in a row`: the bound on the longest run of completions at
    /// moments that follow each other.
    #[serde(skip)]
    pub run: Option<(Cmp, usize)>,
    /// `true` for a prohibition with an order phrase, with `immediately` or
    /// with a count in a row: the action is forbidden at the moments that
    /// the phrase names, and the statement says nothing of the others.
    #[serde(skip)]
    pub restricted: bool,
}

/// An `unless` condition and the instant at which it is evaluated.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Exception {
    pub condition: String,
    pub sampled: String,
}

/// How long the obligation of one activation stays open.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Lifetime {
    pub opens: String,
    pub closes: String,
    /// A gating state is read at the occurrence and never again.
    pub gate_resampled: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ChoiceShape {
    pub after: String,
    /// The one instant at which the guards are evaluated.
    pub instant: String,
    pub guards: Vec<String>,
    pub otherwise: bool,
    pub selects: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FlowShape {
    /// Each step, with the number of its designated occurrences on a selected path.
    pub occurrences: Vec<(String, usize)>,
    pub choices: Vec<ChoiceShape>,
    /// Each finish step and what reaching it means.
    pub finishes: Vec<(String, String)>,
}

/// The temporal shape of one statement.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Obligation {
    pub statement: SpecRef,
    /// The configurations that feature scopes select. They are no events.
    pub configuration: Vec<String>,
    pub activation: Activation,
    pub exception: Option<Exception>,
    pub lifetime: Option<Lifetime>,
    pub responses: Vec<Response>,
    /// `(completion, start)`: the completion precedes the start.
    pub orders: Vec<(String, String)>,
    pub flows: Vec<FlowShape>,
    /// Why the statement has no unique activation or interval interpretation.
    pub unresolved: Vec<String>,
    /// What the statement names in other statements of the package and no
    /// statement holds: an occurrence without an event. It is a finding
    /// about the package and no part of the reading of the statement.
    #[serde(skip)]
    pub unlinked: Vec<String>,
    /// The words of time and order that this shape reads: no other reading
    /// rule has to read them.
    #[serde(skip)]
    pub read: Vec<String>,
}


const FINISH_MEANING: &str = "completion of the flow instance, with no verification verdict";

fn start_of(key: &str) -> String {
    format!("start({key})")
}

fn completion_of(key: &str) -> String {
    format!("complete({key})")
}

/// `be closed` and `become Paid` name a state. A passive participle names an action.
fn is_state(vp: &Vp) -> bool {
    if vp.verb.eq_ignore_ascii_case("become") || vp.verb.eq_ignore_ascii_case("remain") {
        return true;
    }
    if !vp.verb.eq_ignore_ascii_case("be") {
        return false;
    }
    match &vp.complement {
        Some(Predicate::Words { words, .. }) => !(words.len() == 1 && model::is_participle(&words[0]) && words[0] != "closed"),
        Some(_) => true,
        None => false,
    }
}

struct Builder<'a> {
    lex: &'a Lexicon,
    activation: &'a Activation,
    unresolved: Vec<String>,
    read: Vec<String>,
}

impl Builder<'_> {
    fn key(&self, subject: &Np, vp: &Vp) -> String {
        let (actor, item) = model::active_voice(subject, vp, self.lex).unwrap_or_else(|| (model::subject_key(subject, self.lex), vp.clone()));
        // The key names the action; when it happens is told beside it.
        model::action_key(&actor, &item, self.lex)
    }

    fn holds(&self) -> String {
        match self.activation {
            Activation::Always => "throughout the applicable system scope".to_string(),
            Activation::Interval { .. } => "throughout each interval of its state scope".to_string(),
            Activation::Occurrence { .. } => "from the activation".to_string(),
            Activation::Invocation { .. } => "during each invocation".to_string(),
        }
    }

    fn origin(&self, vp: &Vp) -> Origin {
        // `within 5 seconds after the door opens` names its origin.
        for role in &vp.roles {
            match role {
                RolePp::After(clause) => return Origin::Explicit { event: model::clause_formula(clause, self.lex).to_string() },
                RolePp::Source(np) => return Origin::Explicit { event: occurrence_key(np, self.lex) },
                // `for 99.9 percent of requests` names a population, not an origin.
                RolePp::Other { preposition, np } if preposition.eq_ignore_ascii_case("of") && model::proportion(vp).is_none() => return Origin::Explicit { event: occurrence_key(np, self.lex) },
                // `at least 2 seconds after the first failure`.
                RolePp::Other { preposition, np } if preposition == "after" && (ordered_occurrence(np).is_some() || bare_occurrence(np)) => return Origin::Explicit { event: occurrence_key(np, self.lex) },
                _ => {}
            }
        }
        match self.activation {
            Activation::Occurrence { .. } => Origin::Activation,
            // A response without a trigger is measured from the invocation
            // of its action, whatever the package declares: the reading of a
            // sentence follows from the sentence alone.
            Activation::Invocation { .. } => Origin::Invocation,
            Activation::Interval { .. } => Origin::IntervalStart,
            Activation::Always => Origin::Unresolved,
        }
    }

    fn response(&mut self, subject: &Np, vp: &Vp, modal: Modal, negated: bool) -> Response {
        let key = self.key(subject, vp);
        let state = is_state(vp);
        let mut deadline = None;
        let mut duration = None;
        let mut references: Vec<Reference> = Vec::new();
        let mut cancellation = Vec::new();
        let mut until = Vec::new();
        let related = |clause: &Clause, lex: &Lexicon| {
            let kind = if matches!(clause.body, ClauseBody::Copular { .. }) { "state" } else { "event" };
            (model::clause_formula(clause, lex).to_string(), kind.to_string())
        };
        let positive = matches!(modal, Modal::Shall | Modal::Must) && !negated;
        // `shall not send before the first retry`: the action is forbidden
        // at the moments that the phrase names, and at no other.
        let forbidding = matches!(modal, Modal::Shall | Modal::Must) && negated;
        // A bound on the time of the action is measured from an origin; the
        // clause or the occurrence after `after` is then that origin.
        let measured = vp.roles.iter().any(|role| matches!(role, RolePp::Deadline(measure) if model::is_time_measure(measure)) || delay_bound(role));
        let ordering = |builder: &mut Self, relation: &str| {
            if !positive && !forbidding {
                builder.unresolved.push(format!("`{relation}` orders the completion of a required or a forbidden action: a permission or advice with `{relation}` has no reading; state the interval with `While` or `until`"));
            } else if state {
                builder.unresolved.push(format!("`{relation}` orders the completion of an action: the state `{}` has no completion", vp.render()));
            } else if matches!(builder.activation, Activation::Interval { .. }) {
                builder.unresolved.push(format!("`{relation}` orders the completion of an action after an activation: a statement under `While` has no activation; state the trigger with `When`"));
            }
        };
        for role in &vp.roles {
            match role {
                RolePp::Deadline(measure) if model::is_time_measure(measure) => {}
                _ if delay_bound(role) => {}
                RolePp::Duration(measure) if model::is_time_measure(measure) => duration = Some(role.render()),
                RolePp::Before(clause) => {
                    let (related, related_kind) = related(clause, self.lex);
                    ordering(self, "before");
                    references.push(Reference { relation: "before".to_string(), boundary: format!("the response completes before the {related_kind} begins"), related, related_kind, event: Some(model::clause_formula(clause, self.lex)), orders: true, pick: None, if_named: false });
                }
                RolePp::After(clause) => {
                    let (related, related_kind) = related(clause, self.lex);
                    if !measured {
                        ordering(self, "after");
                    }
                    references.push(Reference { relation: "after".to_string(), boundary: format!("the response starts after the {related_kind} begins"), related, related_kind, event: Some(model::clause_formula(clause, self.lex)), orders: !measured, pick: None, if_named: false });
                }
                RolePp::Until(clause) => {
                    let (related, related_kind) = related(clause, self.lex);
                    cancellation.push(related.clone());
                    until.push(model::clause_formula(clause, self.lex));
                    references.push(Reference { relation: "until".to_string(), boundary: format!("the response holds at every moment before the first moment of the {related_kind}, where its obligation ends"), related, related_kind, event: None, orders: false, pick: None, if_named: false });
                }
                // `before the first retry`, `after the last retry`: an order
                // between the completion and an occurrence that a noun names.
                RolePp::Other { preposition, np } if ["before", "after"].contains(&preposition.as_str()) && ordered_occurrence(np).is_some() => {
                    let (pick, word) = ordered_occurrence(np).unwrap();
                    self.read.push(word.clone());
                    if preposition == "after" && measured {
                        continue;
                    }
                    ordering(self, preposition);
                    if preposition == "before" && pick == Pick::Last {
                        self.unresolved.push(format!("`before the {word} …` names an occurrence that is known only when the trace ends: write `before the first …` or `before the next …`"));
                    }
                    let boundary = if preposition == "before" { "the response completes before the occurrence" } else { "the response completes after the occurrence" };
                    references.push(Reference { relation: preposition.clone(), boundary: boundary.to_string(), related: occurrence_key(np, self.lex), related_kind: "event".to_string(), event: None, orders: true, pick: Some(pick), if_named: false });
                }
                // `before the retry`: an occurrence where the package has an
                // action or an event of that name, and a part of the name of
                // the action elsewhere.
                RolePp::Other { preposition, np } if ["before", "after"].contains(&preposition.as_str()) && bare_occurrence(np) => {
                    if preposition == "after" && measured {
                        continue;
                    }
                    ordering(self, preposition);
                    let boundary = if preposition == "before" { "the response completes before the occurrence" } else { "the response completes after the occurrence" };
                    references.push(Reference { relation: preposition.clone(), boundary: boundary.to_string(), related: occurrence_key(np, self.lex), related_kind: "event".to_string(), event: None, orders: true, pick: None, if_named: true });
                }
                _ => {}
            }
        }
        // `within 5 seconds`, `at least 2 seconds after …`: the bounds on
        // the time from one origin to the completion.
        let bounds: Vec<String> = vp.roles.iter().filter(|role| matches!(role, RolePp::Deadline(measure) if model::is_time_measure(measure)) || delay_bound(role)).map(RolePp::render).collect();
        if !bounds.is_empty() {
            let origin = self.origin(vp);
            if origin == Origin::Unresolved {
                self.unresolved.push(format!("the deadline `{}` has no origin: the response has no trigger and no action, and the sentence names no event to measure from", bounds.join(" ")));
            }
            let event = vp.roles.iter().find_map(|r| match r {
                RolePp::After(clause) => Some(model::clause_formula(clause, self.lex)),
                _ => None,
            });
            for role in &vp.roles {
                if let RolePp::Other { preposition, np } = role {
                    if ["of", "after"].contains(&preposition.as_str()) {
                        if let Some((_, word)) = ordered_occurrence(np) {
                            self.read.push(word);
                        }
                    }
                }
            }
            deadline = Some(Deadline { event, pick: Pick::Last, bound: bounds.join(" and "), measures: "completion".to_string(), origin });
        }
        // `immediately` and `always` before the verb.
        let mut timing = None;
        for word in &vp.manner {
            let chosen = match word.to_ascii_lowercase().as_str() {
                "immediately" => Timing::Immediately,
                "always" => Timing::Always,
                _ => continue,
            };
            self.read.push(word.to_ascii_lowercase());
            if timing.is_some() {
                self.unresolved.push(format!("`{}` states two times for one action", vp.manner.join(" ")));
            }
            timing = Some(chosen);
            if state || matches!(self.activation, Activation::Interval { .. }) {
                // A required state holds from the next moment on, and an
                // action under `While` is done at each moment of its interval.
                timing = None;
            } else if !positive && !(forbidding && chosen == Timing::Immediately) {
                timing = None;
                self.unresolved.push(match (forbidding, chosen) {
                    (true, _) => "`shall not always` forbids nothing on a trace whose rest is open: state the moments at which the action is forbidden".to_string(),
                    _ => format!("`{word}` says when a required or a forbidden action completes: a permission or advice with `{word}` has no reading"),
                });
            } else if chosen == Timing::Immediately && !matches!(self.activation, Activation::Occurrence { .. }) {
                self.unresolved.push("`immediately` is the next moment after an activation: the statement has no trigger; state it with `When`".to_string());
            }
        }
        // `twice in a row`.
        let mut run = None;
        if vp.roles.iter().any(in_a_row) {
            self.read.push("consecutively".to_string());
            match vp.roles.iter().find_map(model::frequency) {
                Some((cmp, n)) if n >= 1 => run = Some((cmp, n as usize)),
                _ => self.unresolved.push("`in a row` says that counted occurrences follow each other: the action has no count; write `twice in a row` or `3 times in a row`".to_string()),
            }
            if forbidding && !state {
                // `shall not retry twice in a row`: no run of two completions.
                run = match run {
                    Some((Cmp::Eq | Cmp::Ge, n)) => Some((Cmp::Lt, n)),
                    Some(_) => {
                        self.unresolved.push("a prohibition with `in a row` forbids a run of a stated length: write `shall not … twice in a row` or `shall … at most 2 times in a row`".to_string());
                        None
                    }
                    None => None,
                };
            } else if !positive || state {
                self.unresolved.push("`in a row` counts the completions of a required or a forbidden action: a permission, advice or a state with `in a row` has no reading".to_string());
            } else if matches!(self.activation, Activation::Interval { .. }) {
                self.unresolved.push("`in a row` counts completions after an activation: a statement under `While` has no activation; state the trigger with `When`".to_string());
            }
        }
        let activated = matches!(self.activation, Activation::Occurrence { .. } | Activation::Invocation { .. });
        let liveness = (!state && positive && activated).then(|| {
            if cancellation.is_empty() {
                format!("eventually {}", completion_of(&key))
            } else {
                format!("eventually {} unless cancelled", completion_of(&key))
            }
        });
        let kind = if state { ResponseKind::State { state: key, holds: self.holds() } } else { ResponseKind::Action { start: start_of(&key), completion: completion_of(&key), key } };
        let modal = format!("{}{}", modal.as_str(), if negated { " not" } else { "" });
        let restricted = forbidding && !state && (timing.is_some() || run.is_some() || references.iter().any(|r| r.orders));
        if restricted {
            for reference in references.iter_mut().filter(|r| r.orders) {
                reference.boundary = format!("the action is forbidden {} the {}", if reference.relation == "before" { "until" } else { "from" }, if reference.related_kind == "state" { "state" } else { "occurrence" });
            }
        }
        Response { kind, modal, deadline, duration, references, liveness, cancellation, until, timing, run, restricted }
    }

    fn leaf_keys(&self, subject: &Np, composition: &Composition, node: &CompNode, out: &mut Vec<String>) {
        match node {
            CompNode::Leaf { index, .. } => out.push(self.key(subject, &composition.leaves[*index])),
            CompNode::All { items } | CompNode::Some { items } | CompNode::One { items } | CompNode::Sequence { items } => items.iter().for_each(|item| self.leaf_keys(subject, composition, item, out)),
            CompNode::Flow(flow) => flow.steps.iter().for_each(|step| self.leaf_keys(subject, composition, &step.node, out)),
        }
    }

    /// The completion-before-start relations of ordered items, and the flows.
    fn structure(&mut self, subject: &Np, composition: &Composition, node: &CompNode, orders: &mut Vec<(String, String)>, flows: &mut Vec<FlowShape>) {
        let pair = |builder: &mut Self, first: &CompNode, second: &CompNode, orders: &mut Vec<(String, String)>| {
            let (mut before, mut after) = (Vec::new(), Vec::new());
            builder.leaf_keys(subject, composition, first, &mut before);
            builder.leaf_keys(subject, composition, second, &mut after);
            for a in &before {
                for b in &after {
                    orders.push((completion_of(a), start_of(b)));
                }
            }
        };
        match node {
            CompNode::Leaf { .. } => {}
            CompNode::Sequence { items } => {
                // An ordered item needs a start and a completion: a state has neither.
                for item in items {
                    if let CompNode::Leaf { index, .. } = item {
                        let vp = &composition.leaves[*index];
                        if is_state(vp) {
                            self.unresolved.push(format!("the ordered item `{}` is a state: an ordered action has a start event and a completion event", vp.render()));
                        }
                    }
                }
                for window in items.windows(2) {
                    pair(self, &window[0], &window[1], orders);
                }
                items.iter().for_each(|item| self.structure(subject, composition, item, orders, flows));
            }
            CompNode::All { items } | CompNode::Some { items } | CompNode::One { items } => items.iter().for_each(|item| self.structure(subject, composition, item, orders, flows)),
            CompNode::Flow(flow) => {
                let node_of = |name: &str| flow.steps.iter().find(|s| s.name == name).map(|s| &s.node);
                for (from, to) in &flow.edges {
                    if let (Some(a), Some(b)) = (node_of(from), node_of(to)) {
                        pair(self, a, b, orders);
                    }
                }
                let choices = flow
                    .choices
                    .iter()
                    .map(|choice| {
                        for (_, target) in &choice.arms {
                            if let (Some(a), Some(b)) = (node_of(&choice.after), node_of(target)) {
                                pair(self, a, b, orders);
                            }
                        }
                        if let (Some(a), Some(b)) = (node_of(&choice.after), choice.otherwise.as_deref().and_then(node_of)) {
                            pair(self, a, b, orders);
                        }
                        ChoiceShape {
                            after: choice.after.clone(),
                            instant: format!("completion of step {}", choice.after),
                            guards: choice.arms.iter().map(|(guard, _)| model::group_formula(guard, self.lex).to_string()).collect(),
                            otherwise: choice.otherwise.is_some(),
                            selects: "exactly one target".to_string(),
                        }
                    })
                    .collect();
                flows.push(FlowShape {
                    // A flow has no cycle, so a selected path meets each of its steps once.
                    occurrences: flow.steps.iter().map(|step| (step.name.clone(), 1)).collect(),
                    choices,
                    finishes: flow.finish.iter().map(|step| (step.clone(), FINISH_MEANING.to_string())).collect(),
                });
                flow.steps.iter().for_each(|step| self.structure(subject, composition, &step.node, orders, flows));
            }
        }
    }
}

fn subjects(group: &NpGroup) -> Vec<&Np> {
    match group {
        NpGroup::Single(np) => vec![np],
        NpGroup::Coordinated { items, .. } => items.iter().collect(),
    }
}

/// The first discrete action of a core and whether the core has one.
fn first_action(core: &Core) -> Option<&Vp> {
    match core {
        Core::Deontic { vp, .. } => vp.items().iter().find(|item| !is_state(item)),
        Core::Conjoined { items } => items.iter().find_map(first_action),
        _ => None,
    }
}

/// The temporal shape of a statement, or `None` for a definition, which is timeless.
pub(super) fn obligation(sentence: &Sentence, otherwise: bool, statement: SpecRef, lex: &Lexicon) -> Option<Obligation> {
    if matches!(sentence.core, Core::Definition { .. }) {
        return None;
    }
    let frame = |f: &Frame| model::frame_formula(&f.keyword, &f.clause, lex).to_string();
    let configuration: Vec<String> = sentence.frames.scopes.iter().map(frame).collect();
    let states: Vec<String> = sentence.frames.states.iter().map(frame).collect();
    let activation = match (&sentence.frames.trigger, first_action(&sentence.core)) {
        (Some(trigger), _) => {
            let event = model::frame_formula(&trigger.keyword, &trigger.clause, lex).to_string();
            // The `otherwise` branch answers the occurrence that the condition misses.
            let event = if otherwise { format!("¬{event}") } else { event };
            Activation::Occurrence { event, unwanted: trigger.kind == TriggerKind::Contingency, gate: states }
        }
        (None, _) if !states.is_empty() => Activation::Interval { conditions: states },
        (None, Some(action)) => {
            let lemma = model::base_verb(&action.verb);
            let operation = lex.predicate_identity(&lemma).unwrap_or(lemma);
            Activation::Invocation { boundary: format!("each invocation of {operation}"), operation }
        }
        (None, None) => Activation::Always,
    };
    let mut builder = Builder { lex, activation: &activation, unresolved: Vec::new(), read: Vec::new() };
    let mut responses = Vec::new();
    let mut orders = Vec::new();
    let mut flows = Vec::new();
    fn collect(core: &Core, builder: &mut Builder, responses: &mut Vec<Response>, orders: &mut Vec<(String, String)>, flows: &mut Vec<FlowShape>) {
        match core {
            Core::Definition { .. } => {}
            Core::Conjoined { items } => items.iter().for_each(|item| collect(item, builder, responses, orders, flows)),
            Core::Deontic { subject, modal, negated, vp } => {
                for np in subjects(subject) {
                    // `No user shall delete the log` denies the action of
                    // each user, as `The user shall not delete the log` does:
                    // the response is forbidden and nothing is owed eventually.
                    let denied = *negated != matches!(np.det, Some(Det::No));
                    for item in vp.items() {
                        responses.push(builder.response(np, item, *modal, denied));
                    }
                    if let VpGroup::Composite(composition) = vp {
                        let before = flows.len();
                        builder.structure(np, composition, &composition.root, orders, flows);
                        // A step of a flow with a choice is required only on a path that selects it.
                        if flows[before..].iter().any(|flow| !flow.choices.is_empty()) {
                            for response in responses.iter_mut() {
                                if let Some(liveness) = &mut response.liveness {
                                    liveness.push_str(" on each path that selects its step");
                                }
                            }
                        }
                    }
                }
            }
            // A description states what holds; it has no start and no completion.
            other => {
                let holds = builder.holds();
                responses.push(Response { kind: ResponseKind::State { state: builder.lex.canon(&other.render()), holds }, modal: "is".to_string(), deadline: None, duration: None, references: Vec::new(), liveness: None, cancellation: Vec::new(), until: Vec::new(), timing: None, run: None, restricted: false });
            }
        }
    }
    collect(&sentence.core, &mut builder, &mut responses, &mut orders, &mut flows);
    let read = builder.read;
    let unresolved = builder.unresolved;
    let triggered = matches!(activation, Activation::Occurrence { .. });
    let exception = sentence.exception.as_ref().map(|clause| Exception {
        condition: model::clause_formula(clause, lex).to_string(),
        sampled: if triggered { "at activation" } else { "throughout the scope of the statement" }.to_string(),
    });
    let lifetime = triggered.then(|| {
        let cancelled: Vec<&String> = responses.iter().flat_map(|r| &r.cancellation).collect();
        let closes = if cancelled.is_empty() { "satisfaction".to_string() } else { format!("satisfaction or {}", cancelled.iter().map(|c| c.as_str()).collect::<Vec<_>>().join(" or ")) };
        Lifetime { opens: "the trigger occurrence".to_string(), closes, gate_resampled: false }
    });
    Some(Obligation { statement, configuration, activation, exception, lifetime, responses, orders, flows, unresolved, unlinked: Vec::new(), read })
}

impl Obligation {
    /// The shape in lines, as `trion model` prints it.
    pub fn lines(&self) -> Vec<String> {
        let mut out = Vec::new();
        if !self.configuration.is_empty() {
            out.push(format!("configuration: {}", self.configuration.join(" ∧ ")));
        }
        out.push(match &self.activation {
            Activation::Occurrence { event, unwanted, gate } => {
                let kind = if *unwanted { "unwanted occurrence" } else { "occurrence" };
                let gate = if gate.is_empty() { String::new() } else { format!("; gate sampled at the occurrence: {}", gate.join(" ∧ ")) };
                format!("activation: each {kind} of {event}{gate}")
            }
            Activation::Invocation { operation, boundary } => format!("activation: {boundary}; operation {operation}"),
            Activation::Interval { conditions } => format!("activation: throughout each interval of {}", conditions.join(" ∧ ")),
            Activation::Always => "activation: none; throughout the applicable system scope".to_string(),
        });
        if let Some(exception) = &self.exception {
            out.push(format!("exception: {} sampled {}", exception.condition, exception.sampled));
        }
        if let Some(lifetime) = &self.lifetime {
            out.push(format!("obligation: open from {} until {}; a later change of the gate does not close it", lifetime.opens, lifetime.closes));
        }
        for response in &self.responses {
            let mut line = match &response.kind {
                ResponseKind::Action { key, start, completion } => format!("action {key}: {start} then {completion}"),
                ResponseKind::State { state, holds } => format!("state {state}: holds {holds}"),
            };
            if let Some(deadline) = &response.deadline {
                let origin = match &deadline.origin {
                    Origin::Activation => "the activation".to_string(),
                    Origin::Invocation => "the invocation".to_string(),
                    Origin::IntervalStart => "the start of the interval".to_string(),
                    Origin::Explicit { event } => event.clone(),
                    Origin::Unresolved => "an unresolved origin".to_string(),
                };
                line.push_str(&format!("; {} {} measured from {origin}", deadline.measures, deadline.bound));
            }
            if let Some(duration) = &response.duration {
                line.push_str(&format!("; lasts {duration} from its start to its completion"));
            }
            for reference in response.references.iter().filter(|r| r.orders || !r.if_named) {
                line.push_str(&format!("; {} {} {}: {}", reference.relation, reference.related_kind, reference.related, reference.boundary));
            }
            match response.timing {
                Some(Timing::Immediately) => line.push_str("; immediately: completes at the next moment after the activation"),
                Some(Timing::Always) => line.push_str("; always: completes at every moment after the activation"),
                None => {}
            }
            if let Some((cmp, n)) = response.run {
                line.push_str(&format!("; in a row: the longest run of completions at moments that follow each other {} {n}", cmp.symbol()));
            }
            if let Some(liveness) = &response.liveness {
                line.push_str(&format!("; {liveness}"));
            }
            out.push(line);
        }
        for (completion, start) in &self.orders {
            out.push(format!("order: {completion} < {start}"));
        }
        for flow in &self.flows {
            let steps: Vec<String> = flow.occurrences.iter().map(|(step, count)| format!("{step}×{count}")).collect();
            out.push(format!("flow: occurrences on a selected path {}", steps.join(", ")));
            for choice in &flow.choices {
                let otherwise = if choice.otherwise { ", otherwise" } else { "" };
                out.push(format!("choice after {}: guards {}{otherwise} evaluated once at {}; selects {}", choice.after, choice.guards.join(" | "), choice.instant, choice.selects));
            }
            for (step, meaning) in &flow.finishes {
                out.push(format!("finish {step}: {meaning}"));
            }
        }
        for problem in &self.unresolved {
            out.push(format!("unresolved: {problem}"));
        }
        out
    }
}

/// A bounded trace: the contracts of a model read over a sequence of moments.
///
/// Each state and each event has one copy for each moment. An action has one
/// copy for each moment at which it can complete. A group keeps the index of
/// its contract, so a result names the same statements as the contracts do.
pub struct Trace {
    pub background: Vec<Formula>,
    /// For each contract: what it requires of the trace, and its condition at
    /// the first moment, which a search for conflicts forces.
    pub groups: Vec<(Formula, Option<Formula>)>,
}

/// How the action atoms of a contract are read.
#[derive(Clone, Copy, PartialEq)]
enum Reading {
    /// After an occurrence at moment i: the action completes at a later
    /// moment, and a required state holds at the next moment.
    Later,
    /// During an interval: the action is done at each of its moments.
    Now,
    /// With no moment of its own: the action completes at some moment.
    Sometime,
}

/// `true` for an atom that has a value at each moment.
fn timed(atom: &Atom) -> bool {
    match atom {
        Atom::Val { .. } => true,
        // The bounds of an action measure the action, not a state.
        Atom::Num { attr, .. } => !attr.contains('|'),
        // A relation between quantities holds at a moment when one of them is a state.
        Atom::Lin { terms, .. } => terms.iter().any(|(attr, _)| !attr.contains('|')),
        Atom::Event { key } => !(key.starts_with("exists ") || key.starts_with("reach ")),
        _ => false,
    }
}

fn at(atom: Atom, moment: usize) -> Atom {
    let stamp = |name: String| format!("{name}@{moment}");
    match atom {
        Atom::Val { attr, value } => Atom::Val { attr: stamp(attr), value },
        Atom::Num { attr, unit, cmp, n } => Atom::Num { attr: stamp(attr), unit, cmp, n },
        Atom::Lin { terms, unit, cmp, n } => Atom::Lin { terms: terms.into_iter().map(|(attr, coef)| if attr.contains('|') { (attr, coef) } else { (stamp(attr), coef) }).collect(), unit, cmp, n },
        Atom::Event { key } => Atom::Event { key: stamp(key) },
        Atom::Act { key } => Atom::Act { key: stamp(key) },
        Atom::Forbid { key } => Atom::Forbid { key: stamp(key) },
        Atom::Discouraged { key } => Atom::Discouraged { key: stamp(key) },
        other => other,
    }
}

/// The copy of an atom at one moment of a trace, as [`unroll`] names it.
/// An atom without a moment (a relation of the domain, a feature) is itself.
pub fn moment_atom(atom: &Atom, moment: usize) -> Atom {
    at(atom.clone(), moment)
}

/// The quantity that holds the time of a moment of a trace, in milliseconds.
pub fn moment_time(moment: usize) -> String {
    time_of(moment)
}

/// The `until` condition of each action that has one, by the key of the action.
type Untils = BTreeMap<String, Formula>;

/// The formula at one moment. States are read at `state`; an action
/// completes at one of `completions`. An action with an `until` condition is
/// done at each of those moments that comes before the first moment of the
/// condition.
fn place(formula: &Formula, state: usize, completions: &[usize], untils: &Untils) -> Formula {
    let done = |key: &str, moment: usize| Formula::Atom(Atom::Act { key: format!("{key}@{moment}") });
    let lasting = |key: &str, condition: &Formula, positive: bool| {
        let parts = completions.iter().enumerate().map(|(n, &moment)| {
            let before: Vec<Formula> = completions[..=n].iter().map(|&m| Formula::not(place(condition, m, &[m], &Untils::new()))).collect();
            let action = if positive { done(key, moment) } else { Formula::not(done(key, moment)) };
            Formula::implies(Formula::And(before), action)
        });
        Formula::And(parts.collect())
    };
    // Whether an action is forbidden or advised against is a fact of a moment:
    // `While S, the X shall not A.` forbids A where S holds and nowhere else.
    let standing = |atom: &Atom| Formula::And(completions.iter().map(|&m| Formula::Atom(at(atom.clone(), m))).collect());
    match formula {
        Formula::True => Formula::True,
        Formula::Not(inner) => match &**inner {
            Formula::Atom(Atom::Act { key }) if untils.contains_key(key) => lasting(key, &untils[key], false),
            other => Formula::Not(Box::new(place(other, state, completions, untils))),
        },
        Formula::Atom(atom @ (Atom::Forbid { .. } | Atom::Discouraged { .. })) => standing(atom),
        // A required action is done at a moment at which it is allowed.
        Formula::And(items) if completions.len() > 1 && items.iter().any(|i| matches!(i, Formula::Atom(Atom::Act { key }) if !untils.contains_key(key))) => {
            let allowed_of = |item: &Formula, key: &str| match item {
                Formula::Not(inner) => matches!(&**inner, Formula::Atom(Atom::Forbid { key: k } | Atom::Discouraged { key: k }) if k == key),
                _ => false,
            };
            let keys: Vec<&String> = items.iter().filter_map(|i| match i {
                Formula::Atom(Atom::Act { key }) if !untils.contains_key(key) => Some(key),
                _ => None,
            }).collect();
            let mut parts: Vec<Formula> = Vec::new();
            for key in &keys {
                let allowed: Vec<&Formula> = items.iter().filter(|i| allowed_of(i, key)).collect();
                let moments = completions.iter().map(|&m| {
                    let mut at_moment = vec![done(key, m)];
                    at_moment.extend(allowed.iter().map(|i| place(i, m, &[m], untils)));
                    Formula::And(at_moment)
                });
                parts.push(Formula::Or(moments.collect()));
            }
            let taken = |item: &Formula| keys.iter().any(|key| matches!(item, Formula::Atom(Atom::Act { key: k }) if k == *key) || allowed_of(item, key));
            parts.extend(items.iter().filter(|i| !taken(i)).map(|i| place(i, state, completions, untils)));
            Formula::And(parts)
        }
        Formula::Atom(Atom::Act { key }) => match (untils.get(key), completions) {
            (Some(condition), _) => lasting(key, condition, true),
            (None, [only]) => done(key, *only),
            (None, many) => Formula::Or(many.iter().map(|m| done(key, *m)).collect()),
        },
        Formula::Atom(atom) if timed(atom) => Formula::Atom(at(atom.clone(), state)),
        // A step of a flow is reached in one instance of the flow: each
        // activation has its own, as it reads its guards at its own moment.
        Formula::Atom(Atom::Event { key }) if key.starts_with("reach ") => Formula::Atom(Atom::Event { key: format!("{key} at activation {state}") }),
        Formula::Atom(atom) => Formula::Atom(atom.clone()),
        Formula::And(items) => Formula::And(items.iter().map(|i| place(i, state, completions, untils)).collect()),
        Formula::Or(items) => Formula::Or(items.iter().map(|i| place(i, state, completions, untils)).collect()),
        Formula::Implies(a, b) => Formula::Implies(Box::new(place(a, state, completions, untils)), Box::new(place(b, state, completions, untils))),
    }
}

/// The time of a moment, in milliseconds. A later moment is never earlier.
fn time_of(moment: usize) -> String {
    format!("{TIME}{moment}")
}

/// What the name of the time of a moment begins with.
const TIME: &str = "time@";

/// Replaces each atom that `with` answers for, and keeps the others.
fn replace(formula: Formula, with: &dyn Fn(&Atom) -> Option<Formula>) -> Formula {
    match formula {
        Formula::Atom(atom) => with(&atom).unwrap_or(Formula::Atom(atom)),
        Formula::Not(inner) => Formula::Not(Box::new(replace(*inner, with))),
        Formula::And(items) => Formula::And(items.into_iter().map(|i| replace(i, with)).collect()),
        Formula::Or(items) => Formula::Or(items.into_iter().map(|i| replace(i, with)).collect()),
        Formula::Implies(a, b) => Formula::Implies(Box::new(replace(*a, with)), Box::new(replace(*b, with))),
        other => other,
    }
}

/// The time of the first completion of an action in the rest of the trace.
/// The rest has no single time: two actions may complete at different
/// moments of it.
fn first_completion_in_rest(key: &str) -> String {
    format!("first completion time in the rest of {key}")
}

/// The time of the first occurrence of an event in the rest of the trace,
/// when the event is one occurrence that the model names: the completion of
/// an action, whose first time in the rest is that of the action, or an
/// event. An occurrence that a clause of several parts states has no such
/// time, and the rest does not order it.
fn first_occurrence_in_rest(event: &Formula) -> Option<String> {
    match event {
        Formula::Atom(Atom::Act { key }) => Some(first_completion_in_rest(key)),
        Formula::Atom(Atom::Event { key }) => Some(format!("first occurrence time in the rest of {key}")),
        _ => None,
    }
}

/// A completion and an occurrence that both lie in the rest of the trace,
/// in the order that a statement requires: the first of the two is strictly
/// earlier. The rest stands for the later moments, and each of the two has
/// a first time there. A completion before each occurrence is one before
/// the first occurrence, and an occurrence before each completion is one
/// before the first completion, so the order of the first times is the
/// order that the statement requires. Without it the rest would order
/// nothing, and two actions could each complete before the other there.
///
fn ordered_in_rest(earlier: &str, later: &str) -> Formula {
    Formula::Atom(Atom::difference(later, earlier, "ms", Cmp::Gt, 0))
}

/// States the bound on the time that an action takes as a relation between
/// two moments: the moment of its origin and each moment of its completion.
/// `origins` gives the event that a deadline names, by the key of its action,
/// and which of its occurrences is meant; without one the origin is the
/// activation at `activation`.
///
/// At the rest of the trace a completion stands for one or more completions
/// at later moments. A bound on each of them holds of the first one, and a
/// bound that one of them meets is met by the first one, so the time of the
/// first completion of the action in the rest stands for them. Two times of
/// the rest that are not ordered by the trace are not compared.
fn between_moments(placed: Formula, activation: usize, completions: &[usize], origins: &BTreeMap<String, (Formula, Pick)>, rest: usize) -> Formula {
    let none = Untils::new();
    replace(placed, &|atom| {
        let Atom::Num { attr, unit, cmp, n } = atom else { return None };
        let key = attr.strip_suffix(" elapsed").filter(|k| k.contains('|'))?;
        let done = |moment: usize| Formula::Atom(Atom::Act { key: format!("{key}@{moment}") });
        let in_rest = first_completion_in_rest(key);
        // The first completion of the rest is not earlier than the last moment.
        let later = Formula::Atom(Atom::difference(&in_rest, &time_of(rest - 1), unit, Cmp::Ge, 0));
        // The time from the position `from` to the completion at `to`, or
        // `None` where the trace does not order the two.
        let apart = |from: usize, to: usize| -> Option<Formula> {
            match (from == rest, to == rest) {
                (false, false) => Some(Formula::Atom(Atom::difference(&time_of(to), &time_of(from), unit, *cmp, *n))),
                (false, true) => Some(Formula::And(vec![later.clone(), Formula::Atom(Atom::difference(&in_rest, &time_of(from), unit, *cmp, *n))])),
                // The origin lies in the rest and the completion before it:
                // the time between them is not positive.
                (true, false) => match cmp {
                    Cmp::Ge | Cmp::Eq if *n > 0 => Some(Formula::not(Formula::True)),
                    Cmp::Gt if *n >= 0 => Some(Formula::not(Formula::True)),
                    _ => None,
                },
                (true, true) => None,
            }
        };
        Some(match origins.get(key) {
            // An upper bound from the first or the next occurrence is met by
            // one completion. Where no such occurrence is, nothing is bounded.
            Some((event, pick)) if matches!(pick, Pick::First | Pick::Next) && matches!(cmp, Cmp::Le | Cmp::Lt) => {
                let occurs = |position: usize| place(event, position, &[position], &none);
                let positions: Vec<usize> = if *pick == Pick::First { (0..=rest).collect() } else { (activation + 1..=rest).collect() };
                let mut ways = vec![Formula::And(positions.iter().map(|&position| Formula::not(occurs(position))).collect())];
                for (n, &from) in positions.iter().enumerate() {
                    let mut holds = vec![occurs(from)];
                    holds.extend(positions[..n].iter().map(|&earlier| Formula::not(occurs(earlier))));
                    holds.push(Formula::Or(completions.iter().map(|&to| Formula::And(vec![done(to), apart(from, to).unwrap_or(Formula::True)])).collect()));
                    ways.push(Formula::And(holds));
                }
                Formula::Or(ways)
            }
            Some((event, pick)) => {
                let occurs = |position: usize| place(event, position, &[position], &none);
                let mut parts = Vec::new();
                for &to in completions {
                    for from in 0..=rest {
                        let mut holds = vec![occurs(from), done(to)];
                        match pick {
                            // The last occurrence at or before the completion.
                            Pick::Last => {
                                if from > to {
                                    continue;
                                }
                                holds.extend((from + 1..=to).map(|later| Formula::not(occurs(later))));
                            }
                            // The first occurrence of the trace, before or after the completion.
                            Pick::First => holds.extend((0..from).map(|earlier| Formula::not(occurs(earlier)))),
                            // The first occurrence after the activation.
                            Pick::Next => {
                                if from <= activation {
                                    continue;
                                }
                                holds.extend((activation + 1..from).map(|earlier| Formula::not(occurs(earlier))));
                            }
                        }
                        if let Some(relation) = apart(from, to) {
                            parts.push(Formula::implies(Formula::And(holds), relation));
                        }
                    }
                }
                Formula::And(parts)
            }
            // An upper bound is met by one completion; a lower bound holds for each.
            // The bound still holds of the time that the action takes as one
            // quantity, which its duration is compared with.
            None if matches!(cmp, Cmp::Le | Cmp::Lt) => Formula::And(vec![Formula::Atom(atom.clone()), Formula::Or(completions.iter().filter_map(|&to| Some(Formula::And(vec![done(to), apart(activation, to)?]))).collect())]),
            None => Formula::And(vec![Formula::Atom(atom.clone()), Formula::And(completions.iter().filter_map(|&to| Some(Formula::implies(done(to), apart(activation, to)?))).collect())]),
        })
    })
}

/// The first moment at which an occurrence of `event` belongs to an
/// activation at `activation`. The occurrence that opens the activation
/// belongs to it; every other event belongs to it from the next moment on:
/// what happens at the moment of the trigger happened beside it and answers
/// nothing that the trigger opens. Without an activation the whole trace counts.
fn of_the_activation(shape: &Obligation, event: &Formula, activation: Option<usize>) -> usize {
    let Some(moment) = activation else { return 0 };
    let opens = matches!(&shape.activation, Activation::Occurrence { event: trigger, .. } if *trigger == event.to_string());
    if opens {
        moment
    } else {
        moment + 1
    }
}

/// What the adverbs, the counted runs and the order phrases of a statement
/// require of the completions after an activation at `activation`, or with
/// `None` of the completions of the whole trace.
///
/// Each formula is exact on the moments. At the rest it is implied by what
/// the statement says of the later moments: a completion of the rest is a
/// completion at some later moment, an event of the rest is an occurrence at
/// some later moment and a state of the rest holds throughout it.
fn orders_after(shape: &Obligation, activation: Option<usize>, rest: usize) -> Vec<Formula> {
    let none = Untils::new();
    let low = activation.map_or(0, |moment| moment + 1);
    let mut out = Vec::new();
    for response in &shape.responses {
        let ResponseKind::Action { key, .. } = &response.kind else { continue };
        let done = |moment: usize| Formula::Atom(Atom::Act { key: format!("{key}@{moment}") });
        if response.restricted {
            out.extend(forbidden_after(shape, response, key, activation, rest));
            continue;
        }
        match response.timing {
            Some(Timing::Immediately) if activation.is_some() => out.push(done(low.min(rest))),
            Some(Timing::Always) => out.extend((low..=rest).map(done)),
            _ => {}
        }
        if let Some((cmp, n)) = response.run {
            // A run of `length` completions that starts at `start`. A run
            // that reaches the rest continues there.
            let run = |start: usize, length: usize| Formula::And((start..(start + length).min(rest + 1)).map(done).collect());
            if matches!(cmp, Cmp::Ge | Cmp::Gt | Cmp::Eq) {
                let length = if cmp == Cmp::Gt { n + 1 } else { n };
                out.push(Formula::Or((low..=rest).map(|start| run(start, length)).collect()));
            }
            if matches!(cmp, Cmp::Le | Cmp::Lt | Cmp::Eq) {
                // A longer run is told only where it lies within the moments.
                let length = if cmp == Cmp::Lt { n } else { n + 1 };
                out.extend((low..rest).filter(|start| start + length <= rest).map(|start| Formula::not(run(start, length))));
            }
        }
        for reference in response.references.iter().filter(|r| r.orders) {
            let Some(event) = &reference.event else { continue };
            let is_event = reference.related_kind == "event";
            let occurs = |position: usize| place(event, position, &[position], &none);
            match reference.relation.as_str() {
                // The action completes at a moment before the occurrence. The
                // first occurrence of the trace may lie before the activation,
                // and then no completion precedes it.
                "before" => {
                    // Without an activation the order is told from the second
                    // moment on: no completion precedes the first moment, and
                    // whether the environment can act there is a question of
                    // realizability, not of consistency.
                    let from = match (activation, reference.pick) {
                        (None, _) => 1,
                        (Some(_), Some(Pick::First)) => 0,
                        (Some(_), _) => low,
                    };
                    for position in from..=rest {
                        let mut earlier: Vec<Formula> = (low..position.min(rest)).map(done).collect();
                        if position == rest && is_event {
                            // Both lie in the rest: the first completion there is before the first occurrence there.
                            earlier.push(match first_occurrence_in_rest(event) {
                                Some(occurrence) => Formula::And(vec![done(rest), ordered_in_rest(&first_completion_in_rest(key), &occurrence)]),
                                None => done(rest),
                            });
                        }
                        out.push(Formula::implies(occurs(position), Formula::Or(earlier)));
                    }
                }
                // An occurrence precedes each completion. `the next` and a
                // clause mean an occurrence at or after the activation.
                "after" => {
                    let from = match reference.pick {
                        Some(Pick::First | Pick::Last) => 0,
                        _ => of_the_activation(shape, event, activation),
                    };
                    for position in low.max(1)..=rest {
                        if position == rest && !is_event {
                            // A state may begin within the rest.
                            continue;
                        }
                        let mut earlier: Vec<Formula> = (from..position.min(rest)).map(occurs).collect();
                        if position == rest {
                            // Both lie in the rest: the first occurrence there is before the first completion there.
                            earlier.push(match first_occurrence_in_rest(event) {
                                Some(occurrence) => Formula::And(vec![occurs(rest), ordered_in_rest(&occurrence, &first_completion_in_rest(key))]),
                                None => occurs(rest),
                            });
                        }
                        out.push(Formula::implies(done(position), Formula::Or(earlier)));
                    }
                }
                _ => {}
            }
        }
    }
    out
}

/// What a prohibition with an order phrase, with `immediately` or with a
/// count in a row forbids after an activation at `activation`, or with
/// `None` on the whole trace.
///
/// Each formula is exact on the moments. At the rest the action is forbidden
/// only where the statement forbids it at every moment of the rest: a
/// completion and an occurrence that both lie in the rest are not ordered,
/// and a state of the rest that does not hold throughout it tells nothing.
fn forbidden_after(shape_of: &Obligation, response: &Response, key: &str, activation: Option<usize>, rest: usize) -> Vec<Formula> {
    let none = Untils::new();
    let low = activation.map_or(0, |moment| moment + 1);
    let done = |moment: usize| Formula::Atom(Atom::Act { key: format!("{key}@{moment}") });
    let never = |moment: usize| Formula::And(vec![Formula::not(done(moment)), Formula::Atom(Atom::Forbid { key: format!("{key}@{moment}") })]);
    let mut out = Vec::new();
    // `shall not immediately send`: no completion at the next moment. The
    // first moment of the rest is not told apart from its later moments.
    if response.timing == Some(Timing::Immediately) && activation.is_some() && low < rest {
        out.push(never(low));
    }
    // `shall not retry twice in a row`: no run of that length within the moments.
    if let Some((Cmp::Lt, length)) = response.run {
        out.extend((low..rest).filter(|start| start + length <= rest).map(|start| Formula::not(Formula::And((start..start + length).map(done).collect()))));
    }
    for reference in response.references.iter().filter(|r| r.orders) {
        let Some(event) = &reference.event else { continue };
        let is_event = reference.related_kind == "event";
        let occurs = |position: usize| place(event, position, &[position], &none);
        // The occurrences that the phrase speaks of: `the first` of the
        // whole trace, the others from the activation on.
        let from = match reference.pick {
            Some(Pick::First | Pick::Last) => 0,
            _ => of_the_activation(shape_of, event, activation),
        };
        match reference.relation.as_str() {
            // Forbidden until the occurrence: a completion at the moment of
            // the occurrence is not before it.
            "before" => {
                for position in low..=rest {
                    if position == rest && !is_event {
                        // A state may begin within the rest.
                        continue;
                    }
                    let mut occurred: Vec<Formula> = (from..=position.min(rest - 1)).map(occurs).collect();
                    if position == rest {
                        occurred.push(occurs(rest));
                    }
                    occurred.push(never(position));
                    out.push(Formula::Or(occurred));
                }
            }
            // Forbidden from the occurrence on; after `the last` occurrence
            // only where no occurrence follows.
            "after" => {
                for position in low.max(1)..=rest {
                    let earlier: Vec<Formula> = (from..position.min(rest)).map(occurs).collect();
                    let mut allowed = vec![Formula::not(Formula::Or(earlier)), never(position)];
                    if reference.pick == Some(Pick::Last) {
                        allowed.extend((position..=rest).map(occurs));
                    }
                    out.push(Formula::Or(allowed));
                }
            }
            _ => {}
        }
    }
    out
}

/// The response without what it says of the actions that a prohibition
/// forbids only at named moments: those moments are stated beside it.
fn without_restricted(response: Formula, shape: &Obligation) -> Formula {
    let keys: Vec<&str> = shape.responses.iter().filter(|r| r.restricted).filter_map(|r| match &r.kind {
        ResponseKind::Action { key, .. } => Some(key.as_str()),
        ResponseKind::State { .. } => None,
    }).collect();
    if keys.is_empty() {
        return response;
    }
    let named = |key: &str| keys.contains(&key.rsplit_once('@').map_or(key, |(name, _)| name));
    replace(response, &|atom| match atom {
        // The action stands under a negation in a prohibition.
        Atom::Act { key } if named(key) => Some(Formula::not(Formula::True)),
        Atom::Forbid { key } if named(key) => Some(Formula::True),
        _ => None,
    })
}

/// The guarantee of a contract as it holds of one situation. Two things
/// are left out, because they speak of moments of a trace and the trace
/// states them: what a prohibition forbids only at named moments, and the
/// bound of a deadline that is measured from an event that the sentence
/// names, which is another origin than the situation of the statement.
pub fn situation_guarantee(model: &Model, c: &crate::reading::model::Constraint) -> Formula {
    let Some(shape) = c.refs.first().and_then(|r| model.temporal.iter().find(|o| o.statement.id == r.id)) else { return c.guarantee.clone() };
    let elsewhere: Vec<&str> = shape
        .responses
        .iter()
        .filter(|r| r.deadline.as_ref().is_some_and(|d| d.event.is_some()))
        .filter_map(|r| match &r.kind {
            ResponseKind::Action { key, .. } => Some(key.as_str()),
            ResponseKind::State { .. } => None,
        })
        .collect();
    let measures = |attr: &str| elsewhere.iter().any(|key| attr.strip_prefix(key).is_some_and(|rest| rest.starts_with(' ')));
    replace(without_restricted(c.guarantee.clone(), shape), &|atom| match atom {
        Atom::Num { attr, .. } if measures(attr) => Some(Formula::True),
        Atom::Lin { terms, .. } if terms.iter().any(|(attr, _)| measures(attr)) => Some(Formula::True),
        _ => None,
    })
}

fn has_moment(formula: &Formula) -> bool {
    let mut any = false;
    formula.atoms(true, &mut |atom, _| any |= timed(atom) || matches!(atom, Atom::Act { .. } | Atom::Forbid { .. } | Atom::Discouraged { .. }));
    any
}

/// What of a response is kept where the rest of the trace cannot state all of it.
#[derive(Clone, Copy, PartialEq)]
enum Kept {
    /// Everything about actions: what completes, what does not and what is forbidden.
    Actions,
}

/// A formula that `formula` implies (or, at a negative position, one that
/// implies it), without what the rest of the trace cannot tell.
fn weaken(formula: Formula, positive: bool, kept: Kept) -> Formula {
    let dropped = || if positive { Formula::True } else { Formula::not(Formula::True) };
    match formula {
        Formula::True => Formula::True,
        Formula::Atom(atom) => {
            let keep = match &atom {
                Atom::Act { .. } => positive || kept == Kept::Actions,
                Atom::Forbid { .. } | Atom::Discouraged { .. } => kept == Kept::Actions,
                other => !timed(other),
            };
            if keep {
                Formula::Atom(atom)
            } else {
                dropped()
            }
        }
        Formula::Not(inner) => Formula::Not(Box::new(weaken(*inner, !positive, kept))),
        Formula::And(items) => Formula::And(items.into_iter().map(|i| weaken(i, positive, kept)).collect()),
        Formula::Or(items) => Formula::Or(items.into_iter().map(|i| weaken(i, positive, kept)).collect()),
        Formula::Implies(a, b) => Formula::Implies(Box::new(weaken(*a, !positive, kept)), Box::new(weaken(*b, positive, kept))),
    }
}

/// The response to a trigger of the rest, with each action of the rest
/// read after the first occurrence of the trigger there: `key@rest` becomes
/// `key after trigger@rest`. `related` maps each such action to the
/// action of the rest that it is one completion of.
fn after_trigger(formula: Formula, rest: usize, trigger: &str, related: &mut BTreeMap<String, String>) -> Formula {
    let suffix = format!("@{rest}");
    let found = std::cell::RefCell::new(BTreeMap::new());
    let relate = |key: &str| -> Option<String> {
        let base = key.strip_suffix(&suffix)?;
        let after = format!("{base} after {trigger}{suffix}");
        found.borrow_mut().insert(after.clone(), key.to_string());
        Some(after)
    };
    let replaced = replace(formula, &|atom| match atom {
        Atom::Act { key } => relate(key).map(|key| Formula::Atom(Atom::Act { key })),
        Atom::Forbid { key } => relate(key).map(|key| Formula::Atom(Atom::Forbid { key })),
        Atom::Discouraged { key } => relate(key).map(|key| Formula::Atom(Atom::Discouraged { key })),
        _ => None,
    });
    related.extend(found.into_inner());
    replaced
}

/// `true` for the reading of a necessary condition: an alternative between
/// a state and the prohibition of an action.
fn only_when(guarantee: &Formula) -> bool {
    let Formula::Or(parts) = guarantee else { return false };
    let holds = |part: &Formula, kind: &dyn Fn(&Atom) -> bool| {
        let mut found = false;
        part.atoms(true, &mut |atom, _| found |= kind(atom));
        found
    };
    parts.iter().any(|p| holds(p, &|a| matches!(a, Atom::Forbid { .. }))) && parts.iter().any(|p| !holds(p, &|a| matches!(a, Atom::Forbid { .. } | Atom::Act { .. })))
}

/// `true` when a condition denies a state. At the rest of the trace a state
/// atom says that the state holds throughout the rest, so its negation says
/// only that the state fails somewhere there: such a condition does not say
/// that it holds throughout.
fn denies_a_state(condition: &Formula) -> bool {
    let mut denied = false;
    condition.atoms(true, &mut |atom, positive| denied |= !positive && timed(atom));
    denied
}

/// `true` for a condition that is one event, or one of several events.
fn occurrence(condition: &Formula) -> bool {
    match condition {
        Formula::Atom(Atom::Event { .. }) => true,
        Formula::Or(items) => items.iter().all(occurrence),
        _ => false,
    }
}

/// `true` for an axiom whose atoms with a moment all stand negated: it
/// excludes states and requires none.
fn excludes_only(axiom: &Formula) -> bool {
    let mut only = true;
    axiom.atoms(true, &mut |atom, positive| only &= !positive || !timed(atom));
    only
}

/// The background of a model at every moment of a trace of `length` moments,
/// with the order of the times of the moments.
pub fn unroll_background(model: &Model, length: usize) -> Vec<Formula> {
    let rest = length.max(2);
    let all: Vec<usize> = (0..=rest).collect();
    let mut background = Vec::new();
    for axiom in &model.background {
        let mut acts = false;
        axiom.atoms(true, &mut |atom, _| acts |= matches!(atom, Atom::Act { .. } | Atom::Forbid { .. } | Atom::Discouraged { .. }));
        if acts {
            background.extend(all.iter().map(|&m| place(axiom, m, &[m], &Untils::new())));
        } else if has_moment(axiom) {
            // A state of the rest holds throughout the rest. An axiom that
            // only excludes states holds there too: two states that never
            // hold together do not both hold throughout the rest. Any other
            // axiom about states is not stated there.
            let upto = if excludes_only(axiom) { rest + 1 } else { rest };
            background.extend(all[..upto].iter().map(|&m| place(axiom, m, &[m], &Untils::new())));
        } else {
            background.push(axiom.clone());
        }
    }
    // A configuration holds one value over the whole behaviour.
    if !model.configured.is_empty() {
        let mut values: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut visit = |atom: &Atom, _: bool| {
            if let Atom::Val { attr, value } | Atom::Dom { attr, value } = atom {
                if model.configured.contains(attr) {
                    values.entry(attr.clone()).or_default().insert(value.clone());
                }
            }
        };
        for formula in model.background.iter().chain(model.constraints.iter().flat_map(|c| [&c.assume, &c.guarantee])) {
            formula.atoms(true, &mut visit);
        }
        for (attr, values) in &values {
            for value in values {
                let first = Formula::Atom(at(Atom::Val { attr: attr.clone(), value: value.clone() }, 0));
                for moment in 1..=rest {
                    let later = Formula::Atom(at(Atom::Val { attr: attr.clone(), value: value.clone() }, moment));
                    background.push(Formula::And(vec![Formula::implies(first.clone(), later.clone()), Formula::implies(later, first.clone())]));
                }
            }
        }
    }
    // Each moment has a time, and time does not run backwards.
    for moment in 0..rest {
        background.push(Formula::Atom(Atom::difference(&time_of(moment + 1), &time_of(moment), "ms", Cmp::Ge, 0)));
    }
    // An event is the occurrence of its action: where the action completes
    // in the rest of the trace, the event has occurred there by the time of
    // the first completion.
    for axiom in &model.background {
        let Formula::Implies(action, event) = axiom else { continue };
        let (Formula::Atom(Atom::Act { key }), Some(occurrence)) = (&**action, first_occurrence_in_rest(event)) else { continue };
        let completes = Formula::Atom(Atom::Act { key: format!("{key}@{rest}") });
        background.push(Formula::implies(completes, Formula::Atom(Atom::difference(&first_completion_in_rest(key), &occurrence, "ms", Cmp::Ge, 0))));
    }
    background
}

/// What an axiom about terms says of a trace: it holds at every moment.
pub fn unroll_axiom(axiom: &Formula, length: usize) -> Formula {
    let rest = length.max(2);
    if !has_moment(axiom) {
        return axiom.clone();
    }
    let none = Untils::new();
    Formula::And((0..=rest).map(|m| place(axiom, m, &[m], &none)).collect())
}

/// A formula about states, at each moment of a trace. The rest of the trace
/// is left out: it has no single state.
pub fn at_each_moment(formula: &Formula, length: usize) -> Formula {
    let none = Untils::new();
    Formula::And((0..length.max(2)).map(|m| place(formula, m, &[m], &none)).collect())
}

/// A formula about states, read at the first moment of a trace.
pub fn at_first_moment(formula: &Formula) -> Formula {
    place(formula, 0, &[0], &Untils::new())
}

/// What one contract requires of a trace of `length` moments, and its
/// condition at the first moment, which a search for conflicts forces. The
/// condition is the one that the statement states: a relation to another
/// statement narrows the formula only.
pub(super) fn unroll_contract(model: &Model, c: &crate::reading::model::Constraint, length: usize) -> (Formula, Option<Formula>) {
    contract_over(model, c, length, false, None)
}

/// The contract over a trace. `complete` asks for the reading of a
/// behaviour that ends with the trace: the count of a share binds only
/// there, so only there do the formulas hold the counters.
fn contract_over(model: &Model, c: &crate::reading::model::Constraint, length: usize, complete: bool, known: Known) -> (Formula, Option<Formula>) {
    // A refinement relates statements that all stand in the trace already.
    if c.kind == crate::reading::model::ConstraintKind::Refinement {
        return (Formula::True, None);
    }
    if c.kind == crate::reading::model::ConstraintKind::RoleActivation {
        let own = model.constraints.iter().find(|statement| {
            matches!(statement.kind, crate::reading::model::ConstraintKind::Spec | crate::reading::model::ConstraintKind::Permission)
                && statement.refs.first() == c.refs.first()
        });
        let held = match own {
            Some(own) => Formula::Or(activations_of(model, own, length, known).into_iter()
                .map(|(_, condition, response)| {
                    Formula::And(condition.into_iter().chain([response]).collect())
                }).collect()),
            None => unroll_axiom(&c.assume, length),
        };
        return (Formula::implies(held, unroll_axiom(&c.guarantee, length)), None);
    }
    // An axiom about terms holds at every moment, as the background does.
    // What a statement says of individuals stands beside its claim and holds
    // where the claim does: the facts follow from the claim, and are no
    // axiom without it.
    if c.kind.is_vocabulary() {
        // Facts about the individuals under the condition of the statement
        // are the meaning of the condition, and hold as an axiom: `When an
        // accepted construct has no supported formal interpretation` says
        // that such a construct exists. Other facts say what the response
        // does, and follow from the claim.
        let id = c.refs.first().map(|r| r.id.as_str());
        let own = model.constraints.iter().find(|o| matches!(o.kind, crate::reading::model::ConstraintKind::Spec | crate::reading::model::ConstraintKind::Permission) && o.refs.first().map(|r| r.id.as_str()) == id);
        let of_condition = own.is_some_and(|own| {
            let mut condition = BTreeSet::new();
            own.assume.atoms(true, &mut |atom, _| {
                condition.insert(atom.clone());
            });
            let under = |part: &Formula| match part {
                Formula::Implies(antecedent, _) => {
                    let mut inside = !condition.is_empty();
                    antecedent.atoms(true, &mut |atom, _| inside &= condition.contains(atom));
                    inside
                }
                _ => false,
            };
            match &c.guarantee {
                Formula::And(parts) => !parts.is_empty() && parts.iter().all(under),
                other => under(other),
            }
        });
        if c.kind == crate::reading::model::ConstraintKind::Carried && c.assume != Formula::True && !of_condition {
            // The claim is the contract of the statement over the trace.
            let claim = match own {
                Some(own) => contract_over(model, own, length, complete, known).0,
                None => unroll_axiom(&c.assume, length),
            };
            return (Formula::implies(claim, unroll_axiom(&c.guarantee, length)), None);
        }
        return (unroll_axiom(&c.guarantee, length), None);
    }
    if let Some(counted) = share_contract(model, c, length, complete, known) {
        return counted;
    }
    let mut parts: Vec<Formula> = Vec::new();
    for (_, condition, response) in activations_of(model, c, length, known) {
        let part = match condition {
            Some(condition) => Formula::implies(condition, response),
            None => response,
        };
        if !parts.contains(&part) {
            parts.push(part);
        }
    }
    let formula = if parts.len() == 1 { parts.remove(0) } else { Formula::And(parts) };
    let condition = crate::reading::priority::authored_condition(model, c);
    (formula, (condition != Formula::True).then(|| place(&condition, 0, &[0], &Untils::new())))
}

/// What is known of the atoms of a behaviour, when the contracts are stated
/// for one behaviour: the truth of an atom that the behaviour fixes.
type Known<'a> = Option<&'a dyn Fn(&Atom) -> Option<bool>>;

/// The truth of a formula as far as the known atoms decide it.
fn settled(formula: &Formula, known: &dyn Fn(&Atom) -> Option<bool>) -> Option<bool> {
    match formula {
        Formula::True => Some(true),
        Formula::Atom(atom) => known(atom),
        Formula::Not(inner) => settled(inner, known).map(|value| !value),
        Formula::And(items) => {
            let mut all = Some(true);
            for item in items {
                match settled(item, known) {
                    Some(false) => return Some(false),
                    Some(true) => {}
                    None => all = None,
                }
            }
            all
        }
        Formula::Or(items) => {
            let mut none = Some(false);
            for item in items {
                match settled(item, known) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => none = None,
                }
            }
            none
        }
        Formula::Implies(condition, consequence) => match (settled(condition, known), settled(consequence, known)) {
            (Some(false), _) | (_, Some(true)) => Some(true),
            (Some(true), Some(false)) => Some(false),
            _ => None,
        },
    }
}

/// The activations of one contract over a trace of `length` moments: for
/// each moment at which the contract can apply, its condition there, when
/// it has one, and the response that the condition opens. The contract
/// holds on the trace exactly when each condition implies its response.
///
/// Where the atoms of one behaviour are known, a moment at which the
/// condition fails in that behaviour is left out: the contract requires
/// nothing there, and no count holds such a moment.
fn activations_of(model: &Model, c: &crate::reading::model::Constraint, length: usize, known: Known) -> Vec<(usize, Option<Formula>, Formula)> {
    let rest = length.max(2);
    let all: Vec<usize> = (0..=rest).collect();
    let shape = c.refs.first().and_then(|r| model.temporal.iter().find(|o| o.statement.id == r.id));
    let reading = shape.map_or(Reading::Sometime, |o| match o.activation {
        Activation::Occurrence { .. } => Reading::Later,
        Activation::Interval { .. } => Reading::Now,
        Activation::Invocation { .. } | Activation::Always => Reading::Sometime,
    });
    // `shall stop only when the door is open` is read as `C ∨ forbidden`: at
    // each moment the action needs the state at that moment, and a moment
    // without the state forbids the action there and nowhere else.
    let reading = if reading == Reading::Sometime && only_when(&c.guarantee) { Reading::Now } else { reading };
    let mut untils = Untils::new();
    for response in shape.iter().flat_map(|o| &o.responses) {
        if let (ResponseKind::Action { key, .. }, false) = (&response.kind, response.until.is_empty()) {
            untils.insert(key.clone(), Formula::Or(response.until.clone()));
        }
    }
    let none = Untils::new();
    let guarded = c.has_guard();
    let mut origins: BTreeMap<String, (Formula, Pick)> = BTreeMap::new();
    for response in shape.iter().flat_map(|o| &o.responses) {
        if let (ResponseKind::Action { key, .. }, Some(deadline)) = (&response.kind, &response.deadline) {
            if let Some(event) = &deadline.event {
                origins.insert(key.clone(), (event.clone(), deadline.pick));
            }
        }
    }
    // What the adverbs and the order phrases add to the response to an
    // activation at a moment. An activation in the rest adds nothing: the
    // rest does not order what happens in it.
    let ordered = |response: Formula, activation: Option<usize>| match shape {
        Some(shape) => {
            let mut all = vec![without_restricted(response, shape)];
            all.extend(orders_after(shape, activation, rest));
            if all.len() == 1 {
                all.remove(0)
            } else {
                Formula::And(all)
            }
        }
        None => response,
    };
    let mut parts = Vec::new();
    for &moment in &all {
        let condition = guarded.then(|| place(&c.assume, moment, &[moment], &none));
        if let (Some(condition), Some(known)) = (&condition, known) {
            if settled(condition, known) == Some(false) {
                continue;
            }
        }
        let response = match reading {
            // An event of the rest is an occurrence at one of its moments. A
            // response to it completes later in the rest; what the response
            // forbids, and the state that it requires, hold at moments that
            // the rest does not tell apart, so they are not stated there. A
            // condition that is no single event may hold at one moment of
            // the rest and fail at the next: it opens nothing there.
            //
            // What the response does after its own trigger is told apart
            // all the same: a completion in the rest after the first
            // occurrence of the trigger there. A requirement says that one
            // exists and a prohibition that none does, so two statements
            // that answer one trigger of the rest in opposite ways
            // contradict there as they do at each moment.
            Reading::Later if moment == rest => {
                if !occurrence(&c.assume) {
                    continue;
                }
                // `shall not immediately A` forbids A at the one position
                // after the trigger. The rest holds every later position at
                // once and has no first one apart: what the prohibition says
                // there is said by a trigger at an earlier moment, whose next
                // moment is its own.
                let mut forbids = false;
                c.guarantee.atoms(true, &mut |atom, positive| forbids |= positive && matches!(atom, Atom::Forbid { .. }));
                if forbids && shape.is_some_and(|o| o.responses.iter().any(|r| r.timing == Some(Timing::Immediately))) {
                    continue;
                }
                let placed = place(&c.guarantee, rest, &[rest], &untils);
                let trigger = place(&c.assume, rest, &[rest], &none).to_string();
                let mut related: BTreeMap<String, String> = BTreeMap::new();
                let after = after_trigger(placed, rest, &trigger, &mut related);
                let mut parts = vec![weaken(after, true, Kept::Actions)];
                parts.extend(related.into_iter().map(|(after, key)| Formula::implies(Formula::Atom(Atom::Act { key: after }), Formula::Atom(Atom::Act { key }))));
                Formula::And(parts)
            }
            // The state that a trigger at the last moment requires holds at
            // the first moment of the rest. A state atom of the rest speaks
            // of the whole rest, so that state is not stated.
            Reading::Later if moment + 1 == rest => ordered(between_moments(weaken(place(&c.guarantee, rest, &[rest], &untils), true, Kept::Actions), moment, &[rest], &origins, rest), Some(moment)),
            // The time that a triggered action takes lies between two moments.
            Reading::Later => ordered(between_moments(place(&c.guarantee, moment + 1, &all[moment + 1..], &untils), moment, &all[moment + 1..], &origins, rest), Some(moment)),
            // A condition holds in the rest when it holds throughout the
            // rest; then so does what the statement requires.
            Reading::Now | Reading::Sometime if moment == rest && guarded && denies_a_state(&c.assume) => continue,
            Reading::Now => place(&c.guarantee, moment, &[moment], &untils),
            Reading::Sometime => ordered(place(&c.guarantee, moment, &all, &untils), None),
        };
        parts.push((moment, condition, response));
    }
    parts
}

/// The atom of a count that the reading makes: at least `j` of the first
/// `i` activations of a statement are of the named kind.
fn count_atom(tag: &str, statement: &str, i: usize, j: usize) -> Atom {
    Atom::Rel { name: format!("{COUNT} of {tag} of [{statement}]"), args: vec![i.to_string(), j.to_string()] }
}

const COUNT: &str = "count";

/// The proposition that a behaviour goes on after the moments of the
/// trace. A complete behaviour of those moments does not.
pub fn continues() -> Atom {
    Atom::Config { key: "the behaviour goes on after the trace".to_string() }
}

/// `true` for an atom that counts activations: the reading makes it, and
/// no fact of a behaviour stands for it.
pub fn is_count(atom: &Atom) -> bool {
    matches!(atom, Atom::Rel { name, .. } if name.starts_with("count of "))
}

/// The atoms `at least j of the first i formulas hold`, for each j up to
/// `most`, with the formulas that define them: a sequential counter. The
/// result holds, for each j from 0 to `most`, the formula `at least j of
/// all the formulas hold`.
fn at_least(tag: &str, statement: &str, formulas: &[Formula], most: usize, definitions: &mut Vec<Formula>) -> Vec<Formula> {
    let never = || Formula::not(Formula::True);
    let most = most.min(formulas.len());
    // Before the first formula: at least 0 hold, and no more.
    let mut row: Vec<Formula> = std::iter::once(Formula::True).chain((1..=most).map(|_| never())).collect();
    for (i, formula) in formulas.iter().enumerate() {
        let mut next = vec![Formula::True];
        for j in 1..=most {
            // More than i + 1 formulas cannot hold among the first i + 1.
            if j > i + 1 {
                next.push(never());
                continue;
            }
            let atom = Formula::atom(count_atom(tag, statement, i + 1, j));
            let meaning = Formula::Or(vec![row[j].clone(), Formula::And(vec![formula.clone(), row[j - 1].clone()])]);
            definitions.push(Formula::implies(atom.clone(), meaning.clone()));
            definitions.push(Formula::implies(meaning, atom.clone()));
            next.push(atom);
        }
        row = next;
    }
    row
}

/// The contract of a statement that bounds a share, over a trace.
///
/// The population of the share is the set of the activations of the
/// statement: each instance at each moment at which its condition holds.
/// An activation is answered when the response of its instance meets it.
/// Over the moments of the trace both are counted, and the bound is
/// compared in whole numbers: `answered · 100 000` against `thousandths of
/// a percent · population`. A population of none has no share and meets
/// every bound.
///
/// The rest of the trace stands for moments without number. Where the
/// behaviour goes on after the trace ([`continues`]), its counts are not
/// those of the trace, and a share that the trace fails may hold of the
/// behaviour: the count then requires nothing, apart from a bound that
/// leaves no activation out (all of them, or none of them). A bound on the
/// quantity of the share holds where the population is not empty, and the
/// axioms about the shares of one population relate those quantities.
fn share_contract(model: &Model, c: &crate::reading::model::Constraint, length: usize, complete: bool, known: Known) -> Option<(Formula, Option<Formula>)> {
    let id = &c.refs.first()?.id;
    if !model.individuals.as_ref()?.shares.iter().any(|share| &share.statement == id) {
        return None;
    }
    let rest = length.max(2);
    // Each activation as its condition and its response: within the trace, and in the rest.
    let mut within: Vec<(Formula, Formula)> = Vec::new();
    let mut later: Vec<(Formula, Formula)> = Vec::new();
    let mut first: Vec<Formula> = Vec::new();
    for counted in model.counted.iter().filter(|counted| &counted.statement == id) {
        let mut seen: Vec<(Formula, Formula)> = Vec::new();
        for (moment, condition, response) in activations_of(model, &counted.constraint, length, known) {
            let pair = (condition.unwrap_or(Formula::True), response);
            // A statement without a moment has one activation for each instance.
            if seen.contains(&pair) {
                continue;
            }
            seen.push(pair.clone());
            if moment == 0 && !first.contains(&pair.0) {
                first.push(pair.0.clone());
            }
            if moment == rest {
                later.push(pair);
            } else {
                within.push(pair);
            }
        }
    }
    let full = 100 * i128::from(trion_solver::NUMERIC_SCALE);
    let mut bounds: Vec<(Cmp, i128)> = Vec::new();
    c.guarantee.atoms(true, &mut |atom, positive| {
        if let Atom::Num { cmp, n, .. } = atom {
            let cmp = match (cmp, positive) {
                (cmp, true) => *cmp,
                (Cmp::Ge, false) => Cmp::Lt,
                (Cmp::Gt, false) => Cmp::Le,
                (Cmp::Le, false) => Cmp::Gt,
                (Cmp::Lt, false) => Cmp::Ge,
                // What is not equal is bounded by nothing that a count reads.
                (Cmp::Eq, false) => return,
            };
            bounds.push((cmp, i128::from(*n)));
        }
    });
    let any = |formulas: Vec<Formula>| match formulas.len() {
        0 => Formula::not(Formula::True),
        1 => formulas.into_iter().next().unwrap_or(Formula::True),
        _ => Formula::Or(formulas),
    };
    let size = within.len();
    let mut parts: Vec<Formula> = Vec::new();
    // The counts of the trace: the population, the answered and the unanswered activations.
    let population: Vec<Formula> = within.iter().map(|(condition, _)| condition.clone()).collect();
    // An upper bound counts each activation whose action completes as the
    // statement says, whatever forbids it or advises against it: what the
    // formulas add to a behaviour could otherwise mark a completion and
    // take it out of the count. A lower bound counts the activations that
    // the response meets as a requirement.
    // What the reading adds beside the status is left out in the same way:
    // a quantity that is no time of a moment (the time that an action
    // takes, the time of a completion in the rest) is no part of the
    // behaviour, and a bound on it could be failed at will.
    let of_a_moment = |attr: &String| attr.strip_prefix(TIME).is_some_and(|moment| moment.parse::<usize>().is_ok());
    let completed = |response: &Formula| {
        replace(response.clone(), &|atom| match atom {
            Atom::Forbid { .. } | Atom::Discouraged { .. } => Some(Formula::not(Formula::True)),
            Atom::Num { attr, .. } if !of_a_moment(attr) => Some(Formula::True),
            Atom::Lin { terms, .. } if !terms.iter().all(|(attr, _)| of_a_moment(attr)) => Some(Formula::True),
            _ => None,
        })
    };
    let answered: Vec<Formula> = within.iter().map(|(condition, response)| Formula::And(vec![condition.clone(), completed(response)])).collect();
    let unanswered: Vec<Formula> = within.iter().map(|(condition, response)| Formula::And(vec![condition.clone(), Formula::not(response.clone())])).collect();
    // For a population of k, the least and the greatest count of answered activations that each bound allows.
    let allowed = |k: usize| -> (i128, i128) {
        let k = k as i128;
        let (mut least, mut most) = (0, k);
        for (cmp, thousandths) in &bounds {
            let product = thousandths * k;
            let (floor, ceiling) = (product.div_euclid(full), (product + full - 1).div_euclid(full));
            match cmp {
                Cmp::Ge => least = least.max(ceiling),
                Cmp::Gt => least = least.max(floor + 1),
                Cmp::Le => most = most.min(floor),
                Cmp::Lt => most = most.min(ceiling - 1),
                Cmp::Eq => {
                    least = least.max(ceiling);
                    most = most.min(floor);
                }
            }
        }
        (least, most)
    };
    // What a population of k allows: so many unanswered activations, and
    // so many completed ones. Neither falls as k grows, so a count of u is
    // allowed exactly from the least population that allows it on:
    // `count ≥ u → population ≥ least(u)`, and no population of the trace
    // allows a count without such a population.
    let unanswered_allowed = |k: usize| k as i128 - allowed(k).0;
    let completed_allowed = |k: usize| allowed(k).1;
    let mut needed: Vec<(bool, usize, Option<usize>)> = Vec::new();
    for (of_answered, limit) in [(false, &unanswered_allowed as &dyn Fn(usize) -> i128), (true, &completed_allowed)] {
        // A trace without an activation has no count to bound.
        if size == 0 {
            break;
        }
        for u in 0..=size {
            match (1..=size).find(|&k| limit(k) >= u as i128) {
                // A count is never greater than the population.
                Some(k) if k <= u.max(1) => {}
                Some(k) => needed.push((of_answered, u, Some(k))),
                None => {
                    needed.push((of_answered, u, None));
                    break;
                }
            }
        }
    }
    let most = |of_answered: bool| needed.iter().filter(|(which, _, _)| *which == of_answered).map(|(_, u, _)| *u).max().unwrap_or(0);
    let most_population = needed.iter().map(|(_, u, k)| k.unwrap_or(0).max(usize::from(*u == 0))).max().unwrap_or(0);
    let mut definitions: Vec<Formula> = Vec::new();
    let of_population = at_least("population", id, &population, most_population, &mut definitions);
    let of_unanswered = at_least("unanswered", id, &unanswered, most(false), &mut definitions);
    let of_answered = at_least("answered", id, &answered, most(true), &mut definitions);
    let mut count: Vec<Formula> = Vec::new();
    for (which, u, least) in &needed {
        // A count of none stands for a population that is not empty.
        let counted = match (*u, *which) {
            (0, _) => of_population[1].clone(),
            (u, false) => of_unanswered[u].clone(),
            (u, true) => of_answered[u].clone(),
        };
        count.push(match least {
            Some(k) => Formula::implies(counted, of_population[*k].clone()),
            None => Formula::not(counted),
        });
    }
    // The counts of the trace are the counts of the behaviour only where
    // the behaviour ends with the trace.
    // Where a behaviour may go on, `the behaviour goes on` satisfies the
    // implication and the counters define their atoms freely: the formulas
    // with the count are satisfiable exactly when those without it are. So
    // the count is stated only for a behaviour that ends with the trace.
    let goes_on = Formula::atom(continues());
    if complete && !count.is_empty() {
        parts.extend(definitions);
        parts.push(Formula::implies(Formula::not(goes_on.clone()), Formula::And(count)));
    }
    if !later.is_empty() {
        parts.push(Formula::implies(any(later.iter().map(|(condition, _)| condition.clone()).collect()), goes_on));
    }
    // A bound that leaves no activation out holds of each activation, in the rest as well.
    // Such a bound allows nothing else of a population of any size.
    let many = 1_000_000_000;
    let (all, none) = (allowed(many).0 == many as i128, allowed(many).1 == 0);
    for (condition, response) in within.iter().chain(&later) {
        if all {
            parts.push(Formula::implies(condition.clone(), response.clone()));
        }
        if none {
            parts.push(Formula::implies(condition.clone(), Formula::not(completed(response))));
        }
    }
    // The quantity of the share has its bounds where the population is not empty.
    let not_empty = any(within.iter().chain(&later).map(|(condition, _)| condition.clone()).collect());
    parts.push(Formula::implies(not_empty, c.guarantee.clone()));
    let formula = if parts.len() == 1 { parts.remove(0) } else { Formula::And(parts) };
    Some((formula, (!first.is_empty() && !first.contains(&Formula::True)).then(|| any(first))))
}

/// Reads the contracts of a model over a trace of `length` moments.
///
/// - A state response holds at every moment; under `While S` it holds at
///   every moment where S holds.
/// - After a trigger at moment i, an action completes at a later moment and a
///   required state holds at the next moment. The states around the trigger
///   and an `unless` condition are read at moment i.
/// - A feature scope and a bound of an action have no moment.
/// - An action completes at the moment at which its event holds.
///
/// After the last moment stands one more position, the rest of the trace. It
/// sums up everything that happens later. A state holds there when it holds
/// throughout the rest. An action completes there when it completes at some
/// moment of the rest, and an event occurs there when it occurs at some
/// moment of the rest. An obligation without a deadline is therefore never
/// broken by the end of the trace. A trigger and its response are never read
/// at one moment: a response to an event of the rest completes later in the
/// rest, and a state that a trigger requires at a moment of the rest is not
/// stated.
pub fn unroll(model: &Model, length: usize) -> Trace {
    let length = length.max(2);
    let groups = model.constraints.iter().map(|c| unroll_contract(model, c, length)).collect();
    Trace { background: unroll_background(model, length), groups }
}

/// The contracts of a model over a behaviour that ends with the trace:
/// nothing happens after its last moment. Beside what [`unroll`] gives, the
/// formulas count the activations of each share and say that the
/// behaviour does not go on.
pub fn unroll_complete(model: &Model, length: usize) -> Trace {
    let length = length.max(2);
    let groups = model.constraints.iter().map(|c| contract_over(model, c, length, true, None)).collect();
    let mut background = unroll_background(model, length);
    background.push(Formula::not(Formula::atom(continues())));
    Trace { background, groups }
}

/// The contracts of a model over one complete behaviour of `length`
/// moments, of which `known` tells the atoms that the behaviour fixes. The
/// formulas are those of [`unroll_complete`] without the activations whose
/// condition fails in the behaviour: each of them holds there whatever the
/// rest of the formula says, and no share counts it.
pub fn unroll_complete_in(model: &Model, length: usize, known: &dyn Fn(&Atom) -> Option<bool>) -> Trace {
    let length = length.max(2);
    let groups = model.constraints.iter().map(|c| contract_over(model, c, length, true, Some(known))).collect();
    let mut background = unroll_background(model, length);
    background.push(Formula::not(Formula::atom(continues())));
    Trace { background, groups }
}

/// An axiom about events and actions, stated at every moment of a trace.
pub fn at_every_moment(axiom: &Formula, length: usize) -> Vec<Formula> {
    let none = Untils::new();
    (0..=length.max(2)).map(|m| place(axiom, m, &[m], &none)).collect()
}

/// Reports each statement without a unique activation or interval interpretation.
/// The verbs that a noun of an occurrence can come from: `failure` is `fail`.
fn verbs_of(noun: &str) -> Vec<String> {
    let mut found = vec![noun.to_string()];
    for (ending, with) in [("ure", ""), ("ation", "e"), ("ation", ""), ("tion", "t"), ("tion", "te"), ("ion", ""), ("ion", "e"), ("al", "e"), ("al", ""), ("ment", ""), ("ance", ""), ("ence", ""), ("y", ""), ("se", "d")] {
        if let Some(stem) = noun.strip_suffix(ending) {
            if stem.len() >= 3 {
                found.push(format!("{stem}{with}"));
            }
        }
    }
    found
}

/// Gives each deadline and each order phrase that names an occurrence by a
/// noun phrase the event of that occurrence: `within 5 seconds of the last
/// retry` is measured from the last moment at which a retry happens, and
/// `of the first retry` from the first. An occurrence that no event of the
/// package matches leaves the phrase without a reading.
pub(super) fn resolve_origins(model: &mut Model) {
    let mut events: BTreeSet<String> = BTreeSet::new();
    let mut note = |formula: &Formula| {
        formula.atoms(true, &mut |atom, _| match atom {
            Atom::Event { key } => {
                events.insert(key.clone());
            }
            // An action is an event when it completes.
            Atom::Act { key } => {
                events.insert(key.replacen('|', " ", 1));
            }
            _ => {}
        })
    };
    for c in &model.constraints {
        note(&c.assume);
        note(&c.guarantee);
    }
    // The event of the occurrence that a phrase names, and which occurrence.
    let resolve = |name: &str, strict: bool| -> Result<(Formula, Pick), String> {
        let words: Vec<&str> = name.split_whitespace().collect();
        let pick = words.iter().find_map(|w| pick_of(w)).unwrap_or_default();
        let noun = words.iter().copied().find(|w| pick_of(w).is_none() && !["most", "recent", "the", "a", "an"].contains(w)).ok_or_else(|| format!("`{name}` names no occurrence"))?;
        let verbs = verbs_of(&crate::reading::model::base_verb(noun));
        let matching: Vec<Formula> = events
            .iter()
            .filter(|key| {
                let words: Vec<String> = key.split_whitespace().map(|w| crate::reading::model::base_verb(w.rsplit("::").next().unwrap_or(w))).collect();
                if !strict {
                    return words.iter().any(|w| verbs.contains(w));
                }
                // A bare noun names an occurrence only by the verb of an
                // action of the package or by the verb that ends an event.
                match key.split_once(' ') {
                    Some((actor, action)) if model.constraints.iter().any(|c| mentions_action(&c.guarantee, &format!("{actor}|{action}"))) => words.get(1).is_some_and(|verb| verbs.contains(verb)),
                    _ => words.last().is_some_and(|verb| verbs.contains(verb)),
                }
            })
            .map(|key| match key.split_once(' ') {
                // The completion of an action of the package is that occurrence.
                Some((actor, action)) if model.constraints.iter().any(|c| mentions_action(&c.guarantee, &format!("{actor}|{action}"))) => Formula::Atom(Atom::Act { key: format!("{actor}|{action}") }),
                _ => Formula::Atom(Atom::Event { key: key.clone() }),
            })
            .collect();
        match matching.len() {
            0 => Err(format!("no event of the package is an occurrence of `{noun}`")),
            1 => Ok((matching.into_iter().next().unwrap(), pick)),
            _ => Ok((Formula::Or(matching), pick)),
        }
    };
    let mut resolved: Vec<(usize, usize, Option<Result<(Formula, Pick), String>>, Vec<(usize, Result<(Formula, Pick), String>)>)> = Vec::new();
    for (at, obligation) in model.temporal.iter().enumerate() {
        for (index, response) in obligation.responses.iter().enumerate() {
            let deadline = match &response.deadline {
                Some(Deadline { origin: Origin::Explicit { event: name }, event: None, .. }) => Some(resolve(name, false)),
                _ => None,
            };
            let references = response.references.iter().enumerate().filter(|(_, r)| r.orders && r.event.is_none()).map(|(n, r)| (n, resolve(&r.related, r.if_named))).collect();
            resolved.push((at, index, deadline, references));
        }
    }
    // An occurrence that a clause of an order phrase states is the completion
    // of the action of the package that has its name.
    let mut actions: BTreeMap<String, String> = BTreeMap::new();
    for c in &model.constraints {
        c.guarantee.atoms(true, &mut |atom, _| {
            if let Atom::Act { key } = atom {
                actions.insert(key.replacen('|', " ", 1), key.clone());
            }
        });
    }
    for obligation in &mut model.temporal {
        for reference in obligation.responses.iter_mut().flat_map(|r| &mut r.references).filter(|r| r.orders) {
            if let Some(event) = reference.event.take() {
                reference.event = Some(replace(event, &|atom| match atom {
                    Atom::Event { key } => actions.get(key).map(|action| Formula::Atom(Atom::Act { key: action.clone() })),
                    _ => None,
                }));
            }
        }
    }
    for (at, index, deadline, references) in resolved {
        let obligation = &mut model.temporal[at];
        let response = &mut obligation.responses[index];
        if let (Some(found), Some(deadline)) = (deadline, &mut response.deadline) {
            match found {
                Ok((event, pick)) => {
                    deadline.event = Some(event);
                    deadline.pick = pick;
                }
                Err(problem) => {
                    let Origin::Explicit { event: name } = &deadline.origin else { continue };
                    obligation.unlinked.push(format!("the deadline `{}` is measured from `{name}`, and {problem}", deadline.bound));
                }
            }
        }
        for (n, found) in references {
            let reference = &mut response.references[n];
            match found {
                Ok((event, _)) => reference.event = Some(event),
                // `before the retry` is an order on the trace whatever stands
                // around the statement: without an occurrence of that name
                // the phrase has no reading.
                Err(problem) if reference.if_named => obligation.unlinked.push(format!("`{} {}` orders the completion and an occurrence, and {problem}: state the occurrence in a statement of the package, or name a place with another word than `{}`", reference.relation, reference.related, reference.relation)),
                Err(problem) => obligation.unlinked.push(format!("`{} {}` orders the completion and an occurrence, and {problem}", reference.relation, reference.related)),
            }
        }
    }
}

fn mentions_action(formula: &Formula, key: &str) -> bool {
    let mut found = false;
    formula.atoms(true, &mut |atom, _| found |= matches!(atom, Atom::Act { key: k } if k == key));
    found
}

pub fn diagnostics(obligations: &[Obligation]) -> Vec<Diagnostic> {
    obligations.iter().flat_map(|o| o.unresolved.iter().chain(&o.unlinked).map(|problem| Diagnostic::error("UNRESOLVED_TEMPORAL_SCOPE", problem.clone(), vec![o.statement.clone()]))).collect()
}

#[cfg(test)]
mod moments {
    use super::*;
    use trion_solver::{Instance, Status};

    fn respond_after_event(bound: i64, apart: i64) -> Status {
        let key = "api|respond";
        let event = Formula::Atom(Atom::Event { key: "retry".to_string() });
        let elapsed = Formula::Atom(Atom::Num { attr: format!("{key} elapsed"), unit: "ms".to_string(), cmp: Cmp::Le, n: bound });
        let origins = BTreeMap::from([(key.to_string(), (event.clone(), Pick::Last))]);
        let relation = between_moments(elapsed, 0, &[1, 2], &origins, 3);
        let none = Untils::new();
        let at_moment = |m: usize| place(&event, m, &[m], &none);
        // The retry occurs at the first moment only, and the response completes at the third.
        let facts = vec![
            at_moment(0),
            Formula::not(at_moment(1)),
            Formula::not(at_moment(2)),
            Formula::Atom(Atom::Act { key: format!("{key}@2") }),
            Formula::Atom(Atom::difference(&time_of(1), &time_of(0), "ms", Cmp::Ge, 0)),
            Formula::Atom(Atom::difference(&time_of(2), &time_of(1), "ms", Cmp::Ge, 0)),
            Formula::Atom(Atom::difference(&time_of(2), &time_of(0), "ms", Cmp::Ge, apart)),
        ];
        Instance::new(&facts, &[(relation, None)], None).status(&[0], &[])
    }

    const KEY: &str = "api|respond";

    fn event() -> Formula {
        Formula::Atom(Atom::Event { key: "retry".to_string() })
    }

    fn occurs(moment: usize) -> Formula {
        place(&event(), moment, &[moment], &Untils::new())
    }

    fn done(moment: usize) -> Formula {
        Formula::Atom(Atom::Act { key: format!("{KEY}@{moment}") })
    }

    fn apart(to: usize, from: usize, cmp: Cmp, n: i64) -> Formula {
        Formula::Atom(Atom::difference(&time_of(to), &time_of(from), "ms", cmp, n))
    }

    fn order(length: usize) -> Vec<Formula> {
        (0..length).map(|m| apart(m + 1, m, Cmp::Ge, 0)).collect()
    }

    fn status(mut facts: Vec<Formula>, required: Formula, rest: usize) -> Status {
        facts.extend(order(rest));
        Instance::new(&facts, &[(required, None)], None).status(&[0], &[])
    }

    /// The bound `cmp n` on the time of the action, measured from the picked
    /// occurrence of the retry, after an activation at the first moment of a
    /// trace of three moments and its rest.
    fn bound(cmp: Cmp, n: i64, pick: Pick) -> Formula {
        let elapsed = Formula::Atom(Atom::Num { attr: format!("{KEY} elapsed"), unit: "ms".to_string(), cmp, n });
        between_moments(elapsed, 0, &[1, 2, 3], &BTreeMap::from([(KEY.to_string(), (event(), pick))]), 3)
    }

    #[test]
    fn a_bound_from_the_first_occurrence_is_measured_from_the_first_one() {
        // Retries at the first two moments, six seconds apart; the response
        // completes at the third moment, one second after the second retry.
        let facts = || vec![occurs(0), occurs(1), Formula::not(occurs(2)), Formula::not(occurs(3)), Formula::not(done(1)), done(2), Formula::not(done(3)), apart(1, 0, Cmp::Ge, 6000), apart(2, 1, Cmp::Le, 1000)];
        // Two seconds after the first retry have passed; after the last retry they have not.
        assert_eq!(status(facts(), bound(Cmp::Ge, 2000, Pick::First), 3), Status::Satisfiable);
        assert_eq!(status(facts(), bound(Cmp::Ge, 2000, Pick::Last), 3), Status::Unsatisfiable);
        // Within five seconds of the last retry, and not of the first.
        assert_eq!(status(facts(), bound(Cmp::Le, 5000, Pick::Last), 3), Status::Satisfiable);
        assert_eq!(status(facts(), bound(Cmp::Le, 5000, Pick::First), 3), Status::Unsatisfiable);
    }

    #[test]
    fn a_bound_from_the_next_occurrence_is_measured_from_the_first_one_after_the_activation() {
        // A retry at the activation and one at the third moment; the response completes at the second.
        let early = || vec![occurs(0), Formula::not(occurs(1)), occurs(2), Formula::not(occurs(3)), done(1), Formula::not(done(2)), Formula::not(done(3))];
        // The response completes before the next retry: it is not two seconds after it.
        assert_eq!(status(early(), bound(Cmp::Ge, 2000, Pick::Next), 3), Status::Unsatisfiable);
        assert_eq!(status(early(), bound(Cmp::Le, 5000, Pick::Next), 3), Status::Satisfiable);
        // The response completes ten seconds after the next retry.
        let late = || vec![Formula::not(occurs(0)), occurs(1), Formula::not(occurs(2)), Formula::not(occurs(3)), Formula::not(done(1)), done(2), Formula::not(done(3)), apart(2, 1, Cmp::Ge, 10000)];
        assert_eq!(status(late(), bound(Cmp::Le, 5000, Pick::Next), 3), Status::Unsatisfiable);
        assert_eq!(status(late(), bound(Cmp::Ge, 2000, Pick::Next), 3), Status::Satisfiable);
        // Without a next retry the bound binds nothing.
        let never = vec![Formula::not(occurs(1)), Formula::not(occurs(2)), Formula::not(occurs(3)), done(2)];
        assert_eq!(status(never, bound(Cmp::Le, 5000, Pick::Next), 3), Status::Satisfiable);
    }

    #[test]
    fn each_action_has_its_own_time_in_the_rest_of_the_trace() {
        let elapsed = |key: &str, cmp: Cmp, n: i64| between_moments(Formula::Atom(Atom::Num { attr: format!("{key} elapsed"), unit: "ms".to_string(), cmp, n }), 0, &[1, 2, 3], &BTreeMap::new(), 3);
        let only_in_rest = |key: &str| vec![Formula::not(Formula::Atom(Atom::Act { key: format!("{key}@1") })), Formula::not(Formula::Atom(Atom::Act { key: format!("{key}@2") })), Formula::Atom(Atom::Act { key: format!("{key}@3") })];
        // One action completes within five seconds and another after ten: both in the rest.
        let mut facts = only_in_rest("api|respond");
        facts.extend(only_in_rest("api|archive"));
        let both = Formula::And(vec![elapsed("api|respond", Cmp::Le, 5000), elapsed("api|archive", Cmp::Ge, 10000)]);
        assert_eq!(status(facts, both, 3), Status::Satisfiable);
        // One action cannot do both.
        let one = Formula::And(vec![elapsed("api|respond", Cmp::Le, 5000), elapsed("api|respond", Cmp::Ge, 10000)]);
        assert_eq!(status(only_in_rest("api|respond"), one, 3), Status::Unsatisfiable);
        // A completion in the rest is not earlier than the last moment.
        let mut late = only_in_rest("api|respond");
        late.push(apart(2, 0, Cmp::Ge, 10000));
        assert_eq!(status(late, elapsed("api|respond", Cmp::Le, 5000), 3), Status::Unsatisfiable);
    }

    fn shape(timing: Option<Timing>, run: Option<(Cmp, usize)>, references: Vec<Reference>) -> Obligation {
        let response = Response { kind: ResponseKind::Action { key: KEY.to_string(), start: start_of(KEY), completion: completion_of(KEY) }, modal: "shall".to_string(), deadline: None, duration: None, references, liveness: None, cancellation: Vec::new(), until: Vec::new(), timing, run, restricted: false };
        Obligation { statement: SpecRef { id: "A".to_string(), file: String::new(), line: 0, text: String::new() }, configuration: Vec::new(), activation: Activation::Always, exception: None, lifetime: None, responses: vec![response], orders: Vec::new(), flows: Vec::new(), unresolved: Vec::new(), unlinked: Vec::new(), read: Vec::new() }
    }

    fn reference(relation: &str, pick: Option<Pick>) -> Reference {
        Reference { relation: relation.to_string(), related: "retry".to_string(), related_kind: "event".to_string(), boundary: String::new(), event: Some(event()), orders: true, pick, if_named: false }
    }

    fn ordered(shape: &Obligation, activation: Option<usize>, rest: usize) -> Formula {
        Formula::And(orders_after(shape, activation, rest))
    }

    fn forbidden(timing: Option<Timing>, run: Option<(Cmp, usize)>, references: Vec<Reference>, activation: Option<usize>) -> Formula {
        let mut shape = shape(timing, run, references);
        shape.responses[0].restricted = true;
        ordered(&shape, activation, 3)
    }

    #[test]
    fn a_prohibition_with_an_order_forbids_the_moments_that_the_phrase_names() {
        let no = |moment: usize| Formula::not(occurs(moment));
        let before = forbidden(None, None, vec![reference("before", None)], None);
        assert_eq!(status(vec![no(0), done(0)], before.clone(), 3), Status::Unsatisfiable);
        // A completion at the moment of the occurrence is not before it.
        assert_eq!(status(vec![occurs(0), done(0)], before.clone(), 3), Status::Satisfiable);
        assert_eq!(status(vec![occurs(0), done(1)], before.clone(), 3), Status::Satisfiable);
        // The rest does not order a completion and an occurrence that both lie in it.
        assert_eq!(status(vec![no(0), no(1), no(2), occurs(3), done(3)], before.clone(), 3), Status::Satisfiable);
        // Without any occurrence the action is forbidden throughout the rest.
        assert_eq!(status(vec![no(0), no(1), no(2), no(3), done(3)], before, 3), Status::Unsatisfiable);
        let after = forbidden(None, None, vec![reference("after", Some(Pick::First))], None);
        assert_eq!(status(vec![occurs(0), done(1)], after.clone(), 3), Status::Unsatisfiable);
        assert_eq!(status(vec![no(0), occurs(1), done(1)], after.clone(), 3), Status::Satisfiable);
        assert_eq!(status(vec![no(0), occurs(1), done(0)], after.clone(), 3), Status::Satisfiable);
        assert_eq!(status(vec![occurs(0), done(3)], after.clone(), 3), Status::Unsatisfiable);
        assert_eq!(status(vec![no(0), no(1), no(2), occurs(3), done(3)], after, 3), Status::Satisfiable);
        // After the last occurrence: a later occurrence frees the moment.
        let last = forbidden(None, None, vec![reference("after", Some(Pick::Last))], None);
        assert_eq!(status(vec![occurs(0), done(1), occurs(2)], last.clone(), 3), Status::Satisfiable);
        assert_eq!(status(vec![occurs(0), done(1), no(1), no(2), no(3)], last, 3), Status::Unsatisfiable);
    }

    #[test]
    fn a_prohibition_with_immediately_or_a_run_forbids_those_moments() {
        let at_once = forbidden(Some(Timing::Immediately), None, Vec::new(), Some(0));
        assert_eq!(status(vec![done(1)], at_once.clone(), 3), Status::Unsatisfiable);
        assert_eq!(status(vec![done(2)], at_once, 3), Status::Satisfiable);
        // The first moment of the rest is not told apart from its later moments.
        let late = forbidden(Some(Timing::Immediately), None, Vec::new(), Some(2));
        assert_eq!(status(vec![done(3)], late, 3), Status::Satisfiable);
        let run = forbidden(None, Some((Cmp::Lt, 2)), Vec::new(), None);
        assert_eq!(status(vec![done(0), done(1)], run.clone(), 3), Status::Unsatisfiable);
        assert_eq!(status(vec![done(0), done(2)], run.clone(), 3), Status::Satisfiable);
        assert_eq!(status(vec![done(2), done(3)], run, 3), Status::Satisfiable);
    }

    #[test]
    fn a_response_before_an_occurrence_completes_at_an_earlier_moment() {
        let before = ordered(&shape(None, None, vec![reference("before", None)]), Some(0), 3);
        // The retry follows the activation at once: no moment lies between them.
        assert_eq!(status(vec![occurs(1)], before.clone(), 3), Status::Unsatisfiable);
        assert_eq!(status(vec![Formula::not(occurs(1)), occurs(2), done(1)], before.clone(), 3), Status::Satisfiable);
        assert_eq!(status(vec![Formula::not(occurs(1)), occurs(2), Formula::not(done(1))], before.clone(), 3), Status::Unsatisfiable);
        // A retry of the rest and a completion of the rest are not ordered by the trace.
        let in_rest = vec![Formula::not(occurs(1)), Formula::not(occurs(2)), occurs(3), Formula::not(done(1)), Formula::not(done(2)), done(3)];
        assert_eq!(status(in_rest, before.clone(), 3), Status::Satisfiable);
        // The first retry of the trace may lie before the activation.
        let first = ordered(&shape(None, None, vec![reference("before", Some(Pick::First))]), Some(1), 3);
        assert_eq!(status(vec![occurs(0)], first, 3), Status::Unsatisfiable);
        let next = ordered(&shape(None, None, vec![reference("before", None)]), Some(1), 3);
        assert_eq!(status(vec![occurs(0), Formula::not(occurs(2)), Formula::not(occurs(3))], next, 3), Status::Satisfiable);
    }

    #[test]
    fn a_response_after_an_occurrence_completes_at_a_later_moment() {
        let after = ordered(&shape(None, None, vec![reference("after", None)]), Some(1), 3);
        // The retry and the completion at one moment: the completion is not after it.
        assert_eq!(status(vec![Formula::not(occurs(1)), occurs(2), done(2)], after.clone(), 3), Status::Unsatisfiable);
        // A retry at the moment of the activation happened beside the trigger
        // and belongs to no activation that the trigger opens. Until work
        // item W06 it counted (`an occurrence at or after the activation`),
        // and this line asserted `Satisfiable`: with it, two actions of one
        // activation could each come after the other.
        assert_eq!(status(vec![occurs(1), Formula::not(occurs(2)), done(2)], after.clone(), 3), Status::Unsatisfiable);
        let early = ordered(&shape(None, None, vec![reference("after", None)]), Some(0), 3);
        assert_eq!(status(vec![occurs(1), done(2)], early, 3), Status::Satisfiable);
        // A retry before the activation is no retry after it; the last retry may lie before it.
        assert_eq!(status(vec![occurs(0), Formula::not(occurs(1)), done(2)], after, 3), Status::Unsatisfiable);
        let last = ordered(&shape(None, None, vec![reference("after", Some(Pick::Last))]), Some(1), 3);
        assert_eq!(status(vec![occurs(0), Formula::not(occurs(1)), done(2)], last, 3), Status::Satisfiable);
    }

    #[test]
    fn immediately_is_the_next_moment_and_always_is_each_moment() {
        let immediately = ordered(&shape(Some(Timing::Immediately), None, Vec::new()), Some(0), 3);
        assert_eq!(status(vec![Formula::not(done(1)), done(2)], immediately.clone(), 3), Status::Unsatisfiable);
        assert_eq!(status(vec![done(1)], immediately, 3), Status::Satisfiable);
        // After an activation at the last moment the next moment lies in the rest.
        let last = ordered(&shape(Some(Timing::Immediately), None, Vec::new()), Some(2), 3);
        assert_eq!(status(vec![Formula::not(done(3))], last, 3), Status::Unsatisfiable);
        let always = ordered(&shape(Some(Timing::Always), None, Vec::new()), None, 3);
        assert_eq!(status(vec![done(0), done(1), Formula::not(done(2))], always.clone(), 3), Status::Unsatisfiable);
        assert_eq!(status(Vec::new(), always, 3), Status::Satisfiable);
    }

    #[test]
    fn a_count_in_a_row_bounds_the_longest_run_of_completions() {
        let twice = ordered(&shape(None, Some((Cmp::Eq, 2)), Vec::new()), Some(0), 4);
        // Two completions with a moment between them are no run of two.
        assert_eq!(status(vec![done(1), Formula::not(done(2)), done(3), Formula::not(done(4))], twice.clone(), 4), Status::Unsatisfiable);
        assert_eq!(status(vec![done(1), done(2), Formula::not(done(3))], twice.clone(), 4), Status::Satisfiable);
        // Three in a row are more than twice.
        assert_eq!(status(vec![done(1), done(2), done(3)], twice.clone(), 4), Status::Unsatisfiable);
        // A run that reaches the rest may continue there.
        assert_eq!(status(vec![Formula::not(done(1)), Formula::not(done(2)), Formula::not(done(3)), done(4)], twice, 4), Status::Satisfiable);
        let at_most = ordered(&shape(None, Some((Cmp::Le, 1)), Vec::new()), Some(0), 4);
        assert_eq!(status(vec![done(2), done(3)], at_most.clone(), 4), Status::Unsatisfiable);
        assert_eq!(status(vec![done(1), Formula::not(done(2)), done(3)], at_most, 4), Status::Satisfiable);
    }

    #[test]
    fn a_deadline_is_measured_from_the_last_occurrence_of_its_named_event() {
        // Ten seconds lie between the retry and the response: `within 5 seconds of the retry` fails.
        assert_eq!(respond_after_event(5000, 10000), Status::Unsatisfiable);
        assert_eq!(respond_after_event(5000, 4000), Status::Satisfiable);
    }
}
