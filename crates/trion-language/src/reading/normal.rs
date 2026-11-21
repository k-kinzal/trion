//! The plain form of a statement about individuals.
//!
//! A relative clause, `no` and a count before a noun of a declared type
//! add no meaning of their own: each stands for a statement that names its
//! individuals one by one and states its conditions as conditions. This
//! module writes that statement, and the reading over individuals
//! ([`crate::reading::typed`]) reads it by its other rules. The instances
//! of the statement are instances of the plain form.
//!
//! - `variable-that`: a relative clause on a noun of a declared type is a
//!   condition of the statement about that individual. A clause with a
//!   copula (`that is open`, `that is a member of the room`, `whose mode is
//!   maintenance`) holds at the moment at which the statement applies, as a
//!   `While` condition does. A clause with a verb (`that arrives from the
//!   gateway`, `that the gateway forwards`) is the event at which the
//!   statement applies, as a `When` condition is; a statement applies at
//!   one event, so a statement with an event of its own has none in a
//!   relative clause.
//! - `variable-no`: `no T` as the subject or the object of a statement with
//!   a modal verb denies the statement of each individual: `No user shall
//!   archive a room.` is `Each user shall not archive a room.`
//! - `variable-count`: a number before a noun of a declared type names so
//!   many individuals, one by one: `two members` is `a member` and `a
//!   second member`, which are different individuals (`variable-other`).
//!   In a `While` or `Where` condition the clause holds of each of them; in
//!   what an obligation requires or advice advises, the action is taken on
//!   each of them, and the response chooses them.
//! - `choice-order`: a composition of plain actions is a list of them:
//!   `all of the following actions` requires each, `one or more of the
//!   following actions` requires one, and `the following actions in
//!   order` requires each, each strictly after the one before it.

use crate::reading::lexicon::Lexicon;
use crate::reading::typed::{head_noun, outside, Outside, Step, Types};
use crate::syntax::ast::*;

/// The ordinals that tell the individuals of one noun apart, from the second on.
pub(super) const ORDINALS: [&str; 5] = ["second", "third", "fourth", "fifth", "sixth"];

/// A statement in its plain form, with the steps that led to it.
pub(super) struct Normal {
    pub sentence: Sentence,
    pub steps: Vec<Step>,
}

struct Shaper<'a> {
    types: &'a Types,
    lex: &'a Lexicon,
    steps: Vec<Step>,
    /// The conditions that the relative clauses state, in their order.
    states: Vec<Clause>,
    /// The event that a relative clause states.
    event: Option<Clause>,
}

fn is_ordinal(word: &str) -> bool {
    ORDINALS.iter().any(|ordinal| word.eq_ignore_ascii_case(ordinal)) || word.eq_ignore_ascii_case("other")
}

impl Shaper<'_> {
    fn declared(&self, np: &Np) -> bool {
        self.types.canonical(&head_noun(np, self.lex)).is_some()
    }

    /// The noun phrase that names again what `np` names.
    fn again(np: &Np) -> Np {
        Np { det: Some(Det::The), modifiers: np.modifiers.iter().filter(|m| is_ordinal(m)).cloned().collect(), head: np.head.clone(), of: None, relative: None, of_also: Vec::new(), of_conj: None }
    }

    /// Takes the relative clauses off a noun phrase of a declared type and
    /// keeps what they state. `chosen` is true where the response of the
    /// statement chooses the individual that `a` or `an` names.
    fn lift(&mut self, np: &mut Np, chosen: bool) -> Result<(), Outside> {
        if let Some(owner) = &mut np.of {
            self.lift(owner, false)?;
        }
        if !self.declared(np) {
            return Ok(());
        }
        let Some(relative) = np.relative.take() else { return Ok(()) };
        let words = Np { relative: Some(relative.clone()), ..np.clone() }.render();
        if chosen && matches!(np.det, Some(Det::A | Det::An)) {
            return outside(words, "the response chooses this individual among those that stand in the named relations, and a relative clause restricts it by a state or an event of a moment: relate it to a named individual, as in `a member of the room`, or name it in a condition");
        }
        let again = Self::again(np);
        let mut next = Some(relative);
        while let Some(relative) = next {
            let Relative { marker, body, and } = *relative;
            next = and;
            match body {
                RelativeBody::Copular { copula, predicate, agent, roles } => {
                    let clause = Clause { subject: NpGroup::Single(again.clone()), body: ClauseBody::Copular { copula, predicate, agent, roles } };
                    self.steps.push(Step { rule: "variable-that", words: words.clone(), yields: format!("While {}", clause.render()) });
                    self.states.push(clause);
                }
                RelativeBody::Content { clause } if marker == RelMarker::Whose => {
                    let mut clause = *clause;
                    let NpGroup::Single(property) = &mut clause.subject else { return outside(words, "`whose` names one property of the individual") };
                    if property.of.is_some() {
                        return outside(words, "`whose` names one property of the individual");
                    }
                    property.det = Some(Det::The);
                    property.of = Some(Box::new(again.clone()));
                    self.steps.push(Step { rule: "variable-that", words: words.clone(), yields: format!("While {}", clause.render()) });
                    self.states.push(clause);
                }
                RelativeBody::Verbal { negation: Some(_), .. } => return outside(words, "a relative clause that denies an event names no event at which the statement applies: state the absence as a state"),
                RelativeBody::Verbal { verb, particle, manner, object, roles, negation: None } => {
                    let clause = Clause { subject: NpGroup::Single(again.clone()), body: ClauseBody::Verbal { verb, particle, manner, object, roles, content: None, negation: None } };
                    self.occurs(clause, &words)?;
                }
                RelativeBody::ObjectGap { subject, verb, particle, manner, roles } => {
                    let clause = Clause { subject, body: ClauseBody::Verbal { verb, particle, manner, object: Some(NpGroup::Single(again.clone())), roles, content: None, negation: None } };
                    self.occurs(clause, &words)?;
                }
                RelativeBody::Content { .. } => return outside(words, "a content clause on a declared type is not read over individuals"),
            }
        }
        Ok(())
    }

    fn occurs(&mut self, clause: Clause, words: &str) -> Result<(), Outside> {
        if self.event.is_some() {
            return outside(words, "a relative clause with a verb is the event at which the statement applies, and the statement names two of them: a statement applies at one event");
        }
        self.steps.push(Step { rule: "variable-that", words: words.to_string(), yields: format!("When {}", clause.render()) });
        self.event = Some(clause);
        Ok(())
    }

    fn group(&mut self, group: &mut NpGroup, chosen: bool) -> Result<(), Outside> {
        match group {
            NpGroup::Single(np) => self.lift(np, chosen),
            NpGroup::Coordinated { items, .. } => items.iter_mut().try_for_each(|np| self.lift(np, chosen)),
        }
    }

    fn roles(&mut self, roles: &mut [RolePp], chosen: bool) -> Result<(), Outside> {
        for role in roles {
            match role {
                RolePp::Recipient(g) | RolePp::Topic(g) | RolePp::Source(g) | RolePp::Goal(g) | RolePp::Agent(g) => self.group(g, chosen)?,
                RolePp::Means { np, .. } | RolePp::Location { np, .. } | RolePp::Other { np, .. } => self.group(np, chosen)?,
                _ => {}
            }
        }
        Ok(())
    }

    fn clause(&mut self, clause: &mut Clause) -> Result<(), Outside> {
        self.group(&mut clause.subject, false)?;
        match &mut clause.body {
            ClauseBody::Copular { agent, roles, .. } => {
                if let Some(agent) = agent {
                    self.group(agent, false)?;
                }
                self.roles(roles, false)
            }
            ClauseBody::Verbal { object, roles, .. } => {
                if let Some(object) = object {
                    self.group(object, false)?;
                }
                self.roles(roles, false)
            }
        }
    }

    fn vp(&mut self, vp: &mut Vp, chosen: bool) -> Result<(), Outside> {
        if let Some(object) = &mut vp.object {
            self.group(object, chosen)?;
        }
        self.roles(&mut vp.roles, chosen)
    }

    /// The number of individuals that a noun phrase of a declared type
    /// names by a count, when it names more than one.
    fn count(&self, np: &Np) -> Result<Option<u64>, Outside> {
        if !self.declared(np) {
            return Ok(None);
        }
        let n = match &np.det {
            Some(Det::Cardinal { n, .. } | Det::AtLeast { n }) if *n >= 2 => *n,
            _ => return Ok(None),
        };
        if n as usize > ORDINALS.len() + 1 {
            return outside(np.render(), "a count of more than six individuals is not named one by one: state it as a statement about the domain");
        }
        if np.modifiers.iter().any(|m| is_ordinal(m)) {
            return outside(np.render(), "a count names its individuals by their ordinals, and this noun phrase has one");
        }
        Ok(Some(n))
    }

    /// What a predicate about several individuals says of one of them:
    /// `are members of the room` is `is a member of the room`, and `are
    /// administrators` is `is an administrator`. A value stays as it is.
    fn of_one(&self, clause: &mut Clause) {
        let ClauseBody::Copular { copula, predicate: Predicate::Words { words, .. }, roles, .. } = &mut clause.body else { return };
        // `members of the room`: the owner stands among the words or as the role after them.
        let owned = matches!(roles.as_slice(), [RolePp::Other { preposition, .. }] if preposition.eq_ignore_ascii_case("of"));
        if *copula == ClauseCopula::Are {
            *copula = ClauseCopula::Is;
        }
        let at = usize::from(words.first().is_some_and(|w| w.eq_ignore_ascii_case("not")));
        let Some(first) = words.get(at).cloned() else { return };
        if ["a", "an", "the"].iter().any(|article| first.eq_ignore_ascii_case(article)) {
            return;
        }
        let noun = crate::syntax::words::base_verb(&first.to_lowercase());
        let related = words.get(at + 1).is_some_and(|w| w.eq_ignore_ascii_case("of")) || (words.len() == at + 1 && owned);
        let kind = words.len() == at + 1 && self.types.canonical(&crate::reading::typed::noun_of(std::slice::from_ref(&first), self.lex)).is_some();
        if related || kind {
            let article = if noun.starts_with(['a', 'e', 'i', 'o', 'u']) { "an" } else { "a" };
            words[at] = noun;
            words.insert(at, article.to_string());
        }
    }

    /// The noun phrase of the individual at one place of a count: `a
    /// member`, `a second member`, ….
    fn nth(np: &Np, at: usize) -> Np {
        let mut one = np.clone();
        one.head = crate::syntax::words::base_verb(&np.head.to_lowercase());
        one.det = Some(Det::A);
        if at > 0 {
            one.modifiers.insert(0, ORDINALS[at - 1].to_string());
        }
        one
    }

    /// The clauses of a `While` or `Where` frame with each counted subject
    /// named one by one.
    fn counted_clauses(&mut self, group: &mut ClauseGroup) -> Result<(), Outside> {
        let mut items: Vec<Clause> = Vec::new();
        for clause in std::mem::take(&mut group.items) {
            let counted = match &clause.subject {
                NpGroup::Single(np) => self.count(np)?.map(|n| (np.clone(), n)),
                NpGroup::Coordinated { .. } => None,
            };
            let Some((np, n)) = counted else {
                items.push(clause);
                continue;
            };
            if group.conj == Some(Conj::Or) {
                return outside(clause.render(), "a count in one of several alternative conditions is not read over individuals: write one statement for each alternative");
            }
            let mut named = Vec::new();
            for at in 0..n as usize {
                let mut one = clause.clone();
                one.subject = NpGroup::Single(Self::nth(&np, at));
                self.of_one(&mut one);
                named.push(one.render());
                items.push(one);
            }
            self.steps.push(Step { rule: "variable-count", words: clause.render(), yields: named.join(" and ") });
        }
        if items.len() > 1 && group.conj.is_none() {
            group.conj = Some(Conj::And);
        }
        group.items = items;
        Ok(())
    }

    /// The verb phrase of a response with a counted object or role named
    /// one by one: one action for each individual.
    fn counted_vp(&mut self, vp: &Vp) -> Result<Option<Vec<Vp>>, Outside> {
        // The place of the count: the object, or one of the roles.
        let mut places: Vec<(Option<usize>, Np, u64)> = Vec::new();
        if let Some(NpGroup::Single(np)) = &vp.object {
            if let Some(n) = self.count(np)? {
                places.push((None, np.clone(), n));
            }
        }
        for (at, role) in vp.roles.iter().enumerate() {
            let group = match role {
                RolePp::Recipient(g) | RolePp::Topic(g) | RolePp::Source(g) | RolePp::Goal(g) | RolePp::Agent(g) => g,
                RolePp::Means { np, .. } | RolePp::Location { np, .. } | RolePp::Other { np, .. } => np,
                _ => continue,
            };
            if let NpGroup::Single(np) = group {
                if let Some(n) = self.count(np)? {
                    places.push((Some(at), np.clone(), n));
                }
            }
        }
        let (place, np, n) = match places.len() {
            0 => return Ok(None),
            1 => places.remove(0),
            _ => return outside(vp.render(), "two counts in one action are not read over individuals: write one statement for each"),
        };
        let mut items = Vec::new();
        for at in 0..n as usize {
            let mut one = vp.clone();
            let named = NpGroup::Single(Self::nth(&np, at));
            match place {
                None => one.object = Some(named),
                Some(role) => match &mut one.roles[role] {
                    RolePp::Recipient(g) | RolePp::Topic(g) | RolePp::Source(g) | RolePp::Goal(g) | RolePp::Agent(g) => *g = named,
                    RolePp::Means { np, .. } | RolePp::Location { np, .. } | RolePp::Other { np, .. } => *np = named,
                    _ => {}
                },
            }
            items.push(one);
        }
        self.steps.push(Step { rule: "variable-count", words: vp.render(), yields: items.iter().map(Vp::render).collect::<Vec<_>>().join(" and ") });
        Ok(Some(items))
    }
}

/// `true` when a noun phrase of a declared type is named by a count of
/// more than one somewhere in the clause.
fn counts_in(shaper: &Shaper, clause: &Clause) -> bool {
    let mut any = false;
    crate::reading::typed::clause_nps(clause, &mut |np| any |= matches!(shaper.count(np), Ok(Some(_)) | Err(_)));
    any
}

/// Writes a statement in its plain form.
pub(super) fn normal(sentence: &Sentence, types: &Types, lex: &Lexicon) -> Result<Normal, Outside> {
    let mut shaper = Shaper { types, lex, steps: Vec::new(), states: Vec::new(), event: None };
    let mut plain = sentence.clone();
    // `no` before the subject or the object denies the statement of each individual.
    if let Core::Deontic { subject, modal, negated, vp } = &mut plain.core {
        let mut denied: Option<String> = None;
        if let NpGroup::Single(np) = subject {
            if matches!(np.det, Some(Det::No)) && shaper.declared(np) {
                denied = Some(np.render());
                np.det = Some(Det::Each);
            }
        }
        if let VpGroup::Single(item) = vp {
            if let Some(NpGroup::Single(np)) = &mut item.object {
                if matches!(np.det, Some(Det::No)) && shaper.declared(np) {
                    if denied.is_some() {
                        return outside(np.render(), "`no` before the subject and before the object denies the statement twice: state it with one of them");
                    }
                    denied = Some(np.render());
                    np.det = Some(Det::Each);
                }
            }
        }
        if let Some(words) = denied {
            if *negated {
                return outside(words, "`no` denies the statement, and the verb is denied as well: state it with one of them");
            }
            *negated = true;
            shaper.steps.push(Step { rule: "variable-no", words, yields: format!("each individual, and the statement denied: {} not", modal.as_str()) });
        }
    }
    // A composition of plain actions is a list of them.
    if let Core::Deontic { subject, vp, .. } = &mut plain.core {
        let words = vp.render();
        if let VpGroup::Composite(composition) = vp {
            let typed = composition.leaves.iter().any(|leaf| {
                let mut any = false;
                crate::reading::typed::vp_nps(leaf, &mut |np| any |= shaper.declared(np));
                any
            }) || matches!(subject, NpGroup::Single(np) if shaper.declared(np));
            if typed {
                let (CompNode::All { items } | CompNode::Some { items } | CompNode::Sequence { items }) = &composition.root else {
                    return outside("composition", "of the compositions, `all of`, `one or more of` and `in order` are read over individuals: `exactly one of` and a flow are not, so write one statement for each action");
                };
                let mut actions: Vec<Vp> = Vec::new();
                for item in items {
                    match item {
                        CompNode::Leaf { index, exception: None } => actions.push(composition.leaves[*index].clone()),
                        _ => return outside("composition", "a composition within a composition, or an action of a composition with an exception of its own, is not read over individuals: write one statement for each action"),
                    }
                }
                let ordered = matches!(composition.root, CompNode::Sequence { .. });
                let either = matches!(composition.root, CompNode::Some { .. });
                if ordered {
                    // Each action after the one before it: `after <subject> <action>`.
                    let earlier: Vec<Vp> = actions.clone();
                    for (at, action) in actions.iter_mut().enumerate().skip(1) {
                        let before = &earlier[at - 1];
                        let named: Vec<RolePp> = before.roles.iter().filter(|role| !matches!(role, RolePp::Deadline(_) | RolePp::Duration(_) | RolePp::Rate { .. } | RolePp::Before(_) | RolePp::After(_) | RolePp::Until(_))).cloned().collect();
                        let clause = Clause { subject: subject.clone(), body: ClauseBody::Verbal { verb: before.verb.clone(), particle: before.particle.clone(), manner: Vec::new(), object: before.object.clone(), roles: named, content: None, negation: None } };
                        action.roles.push(RolePp::After(Box::new(clause)));
                    }
                    shaper.steps.push(Step { rule: "choice-order", words, yields: actions.iter().map(Vp::render).collect::<Vec<_>>().join("; ") });
                }
                *vp = if either { VpGroup::Alternatives { items: actions } } else { VpGroup::All { negated: vec![false; actions.len()], items: actions } };
            }
        }
    }
    // A count names its individuals one by one.
    for frame in plain.frames.scopes.iter_mut().chain(plain.frames.states.iter_mut()) {
        shaper.counted_clauses(&mut frame.clause)?;
    }
    if let Some(trigger) = &plain.frames.trigger {
        if let Some(clause) = trigger.clause.items.iter().find(|clause| counts_in(&shaper, clause)) {
            return outside(clause.render(), "a count in the event of a statement names several occurrences of one moment, and a statement applies at one event: state the count as a state, as in `While two users are members of the room,`");
        }
    }
    if let Core::Deontic { subject, modal, negated, vp } = &mut plain.core {
        if let NpGroup::Single(np) = subject {
            if shaper.count(np)?.is_some() {
                return outside(np.render(), "a count before the subject of a statement with a modal verb is not read over individuals: name the individuals in a condition, as in `While two users are members of the room,`");
            }
        }
        let chooses = !*negated && matches!(modal, Modal::Shall | Modal::Must | Modal::Should);
        let mut listed: Option<Vec<Vp>> = None;
        if let VpGroup::Single(item) = vp {
            if let Some(items) = shaper.counted_vp(item)? {
                if !chooses {
                    return outside(item.render(), "a count in what is forbidden, advised against or permitted is not read over individuals: a prohibition and a permission reach each individual, so name `each` or one individual");
                }
                listed = Some(items);
            }
        } else if vp.items().iter().any(|item| matches!(shaper.counted_vp(item), Ok(Some(_)) | Err(_))) {
            return outside(vp.render(), "a count in a list of actions is not read over individuals: write one statement for each action");
        }
        if let Some(items) = listed {
            *vp = VpGroup::All { negated: vec![false; items.len()], items };
        }
    }
    // The relative clauses, in the order of the sentence.
    for frame in plain.frames.scopes.iter_mut().chain(plain.frames.states.iter_mut()) {
        for clause in &mut frame.clause.items {
            shaper.clause(clause)?;
        }
    }
    if let Some(trigger) = &mut plain.frames.trigger {
        for clause in &mut trigger.clause.items {
            shaper.clause(clause)?;
        }
    }
    match &mut plain.core {
        Core::Deontic { subject, modal, negated, vp } => {
            shaper.group(subject, false)?;
            let chooses = !*negated && matches!(modal, Modal::Shall | Modal::Must | Modal::Should);
            match vp {
                VpGroup::Single(item) => shaper.vp(item, chooses)?,
                VpGroup::Alternatives { items } | VpGroup::All { items, .. } => items.iter_mut().try_for_each(|item| shaper.vp(item, chooses))?,
                VpGroup::Composite(composition) => composition.leaves.iter_mut().try_for_each(|item| shaper.vp(item, chooses))?,
            }
        }
        Core::Description { subject, roles, .. } => {
            shaper.group(subject, false)?;
            shaper.roles(roles, false)?;
        }
        _ => {}
    }
    for clause in std::mem::take(&mut shaper.states) {
        plain.frames.states.push(Frame { keyword: "While".to_string(), clause: ClauseGroup::single(clause) });
    }
    if let Some(event) = shaper.event.take() {
        if plain.frames.trigger.is_some() {
            return outside(event.render(), "a relative clause with a verb is the event at which the statement applies, and the statement names another event: a statement applies at one event");
        }
        plain.frames.trigger = Some(Trigger { kind: TriggerKind::Event, keyword: "When".to_string(), clause: ClauseGroup::single(event) });
    }
    Ok(Normal { sentence: plain, steps: shaper.steps })
}
