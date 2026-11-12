//! The references of a sentence: `its header`, `their names`, `it`, `that flow`.
//!
//! A pronoun is accepted where exactly one noun phrase can be what it refers
//! to: a noun phrase that stands before the pronoun in the sentence and
//! agrees with it in number. Neither the distance nor the grammatical role of
//! a noun phrase prefers it. With no such noun phrase the pronoun is
//! unresolved, and with more than one it is ambiguous; the author then
//! repeats the noun. A reference is replaced by what it refers to, so that
//! the name of the thing is built from nodes: `its header` after `each block`
//! is `the header of the block`, and `that flow` after `a flow` is `the flow`.

use super::ast::*;
use super::parse::ParseError;

/// The conditions that stand before the core of the sentence. A condition
/// after the core is read after it, as it is written.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct Preposed {
    pub scopes: usize,
    pub states: usize,
    pub trigger: bool,
}

/// Resolves every pronoun and every demonstrative determiner of a sentence.
pub(crate) fn resolve(frames: &mut Frames, core: &mut Core, extras: &mut [&mut Clause], groups: &mut [&mut ClauseGroup], preposed: Preposed) -> Result<(), ParseError> {
    // The first pass resolves each pronoun and collects the noun phrases of
    // the sentence; the second resolves each demonstrative against them,
    // wherever in the sentence its antecedent stands.
    let mut resolver = Resolver::new();
    resolver.sentence(frames, core, extras, groups, preposed)?;
    resolver.collecting = false;
    resolver.sentence(frames, core, extras, groups, preposed)
}

impl Resolver {
    fn new() -> Self {
        Resolver { seen: Vec::new(), collecting: true, gathering: false, before: Vec::new(), later: None, subjects: Vec::new(), in_subject: false, open: Vec::new() }
    }

    fn sentence(&mut self, frames: &mut Frames, core: &mut Core, extras: &mut [&mut Clause], groups: &mut [&mut ClauseGroup], preposed: Preposed) -> Result<(), ParseError> {
        self.before.clear();
        self.subjects.clear();
        self.open.clear();
        // A pronoun in a condition before the core, with no noun phrase before
        // it, refers forward to the one noun phrase of the core that agrees.
        let later = if self.collecting {
            let mut gatherer = Resolver::new();
            gatherer.gathering = true;
            let mut copy = core.clone();
            let _ = gatherer.core(&mut copy);
            gatherer.before
        } else {
            Vec::new()
        };
        let scopes = preposed.scopes.min(frames.scopes.len());
        let states = preposed.states.min(frames.states.len());
        self.later = Some(later);
        for frame in frames.scopes[..scopes].iter_mut().chain(frames.states[..states].iter_mut()) {
            self.clauses(&mut frame.clause)?;
        }
        if preposed.trigger {
            if let Some(trigger) = &mut frames.trigger {
                self.clauses(&mut trigger.clause)?;
            }
        }
        self.later = None;
        self.core(core)?;
        for frame in frames.scopes[scopes..].iter_mut().chain(frames.states[states..].iter_mut()) {
            self.clauses(&mut frame.clause)?;
        }
        if !preposed.trigger {
            if let Some(trigger) = &mut frames.trigger {
                self.clauses(&mut trigger.clause)?;
            }
        }
        for clause in extras.iter_mut() {
            self.clause(clause)?;
        }
        for group in groups.iter_mut() {
            self.clauses(group)?;
        }
        Ok(())
    }

    fn clauses(&mut self, group: &mut ClauseGroup) -> Result<(), ParseError> {
        group.items.iter_mut().try_for_each(|clause| self.clause(clause))
    }
}

fn nps(group: &NpGroup) -> Vec<&Np> {
    match group {
        NpGroup::Single(np) => vec![np],
        NpGroup::Coordinated { items, .. } => items.iter().collect(),
    }
}

/// The singular of a word, by its ending.
fn fold(word: &str) -> String {
    let lower = word.to_lowercase();
    if let Some(stem) = lower.strip_suffix("ies") {
        return format!("{stem}y");
    }
    for ending in ["ses", "xes", "ches", "shes"] {
        if lower.ends_with(ending) {
            return lower[..lower.len() - 2].to_string();
        }
    }
    match lower.strip_suffix('s') {
        Some(stem) if !stem.ends_with('s') && stem.len() > 2 => stem.to_string(),
        _ => lower,
    }
}

/// The words of the name of a thing. A quoted text after a noun says which
/// one it is, as in `the token "//"`: a later `that token` names it without the text.
fn words(np: &Np) -> Vec<String> {
    let all: Vec<&String> = np.modifiers.iter().chain(std::iter::once(&np.head)).collect();
    let quoted = |w: &str| w.starts_with(['"', '`']);
    let kept: Vec<&String> = if all.len() > 1 && all.last().is_some_and(|w| quoted(w)) { all[..all.len() - 1].to_vec() } else { all };
    kept.into_iter().map(|w| fold(w)).collect()
}

/// A thing as a later reference names it: the same words, with the article `the`.
fn named(np: &Np) -> Np {
    let mut named = np.clone();
    named.det = Some(Det::The);
    named
}

/// A noun phrase that a pronoun may refer to.
#[derive(Debug, Clone)]
struct Candidate {
    /// The thing as a reference names it.
    group: NpGroup,
    plural: bool,
    /// The name without articles: two mentions of one thing are one candidate.
    key: String,
    /// `true` where the determiner introduces a thing: `a namespace` after
    /// `a namespace` is a second namespace, and `the namespace` is the first.
    fresh: bool,
}

/// A noun phrase without its articles and clauses.
fn bare(np: &Np) -> Np {
    let mut bare = np.clone();
    bare.det = None;
    bare.relative = None;
    bare.of = bare.of.map(|of| Box::new(self::bare(&of)));
    bare.of_also = bare.of_also.iter().map(self::bare).collect();
    bare
}

/// Whether a word names more than one thing, by its ending.
fn plural_word(word: &str) -> bool {
    let lower = word.to_lowercase();
    lower.len() > 3 && lower.ends_with('s') && !["ss", "us", "is"].iter().any(|ending| lower.ends_with(ending))
}

/// Whether a noun phrase names more than one thing: its determiner says so, or its head does.
fn plural(np: &Np) -> bool {
    match &np.det {
        Some(Det::A | Det::An | Det::Each | Det::Every) => false,
        Some(Det::All | Det::Both) => true,
        Some(Det::AtLeast { n } | Det::AtMost { n } | Det::Exactly { n } | Det::Cardinal { n, .. }) if *n != 1 => true,
        Some(Det::AtLeast { .. } | Det::AtMost { .. } | Det::Exactly { .. } | Det::Cardinal { .. }) => false,
        _ => plural_word(&np.head),
    }
}

/// A quoted text alone is a text, and no thing that has parts.
fn text_alone(np: &Np) -> bool {
    np.modifiers.is_empty() && np.head.starts_with(['"', '`'])
}

fn is_pronoun(np: &Np) -> bool {
    np.det.is_none() && np.modifiers.is_empty() && np.of.is_none() && np.relative.is_none() && matches!(np.head.to_lowercase().as_str(), "it" | "they" | "them")
}

fn candidate(np: &Np) -> Candidate {
    let bare = bare(np);
    let fresh = !matches!(&np.det, None | Some(Det::The | Det::Reference { .. }));
    Candidate { key: bare.render(), plural: plural(np), group: NpGroup::Single(named(&bare)), fresh }
}

struct Resolver {
    /// The noun phrases of the sentence that name a thing themselves.
    seen: Vec<Np>,
    /// `true` in the first pass.
    collecting: bool,
    /// `true` where the noun phrases are listed and no pronoun is resolved.
    gathering: bool,
    /// The noun phrases that stand before the place that is read, in their order.
    before: Vec<Candidate>,
    /// The noun phrases of the core, while a condition before the core is read.
    later: Option<Vec<Candidate>>,
    /// The subjects of the clauses that enclose the place that is read.
    subjects: Vec<Vec<String>>,
    /// `true` while the subject of a clause is read.
    in_subject: bool,
    /// The places in `before` of the things whose owners are read.
    open: Vec<usize>,
}

impl Resolver {
    fn core(&mut self, core: &mut Core) -> Result<(), ParseError> {
        match core {
            Core::Definition { term, definiens } => match definiens {
                // The term and the genus name one thing: the term is the candidate.
                Definiens::Np { np, roles } => {
                    self.np(term, true)?;
                    for genus in match np {
                        NpGroup::Single(genus) => std::slice::from_mut(genus),
                        NpGroup::Coordinated { items, .. } => items.as_mut_slice(),
                    } {
                        self.np(genus, false)?;
                    }
                    self.roles(roles)
                }
                Definiens::Clause(clause) => {
                    self.np(term, true)?;
                    self.clause(clause)
                }
            },
            Core::Description { subject, predicate, agent, roles, .. } => {
                self.subject(subject)?;
                self.predicate(predicate)?;
                if let Some(agent) = agent {
                    self.group(agent)?;
                }
                self.roles(roles)?;
                self.subjects.pop();
                Ok(())
            }
            Core::Deontic { subject, vp, .. } | Core::Relation { subject, vp } => {
                self.subject(subject)?;
                match vp {
                    VpGroup::Single(item) => self.vp(item)?,
                    VpGroup::Alternatives { items } | VpGroup::All { items, .. } => items.iter_mut().try_for_each(|item| self.vp(item))?,
                    VpGroup::Composite(composition) => composition.leaves.iter_mut().try_for_each(|item| self.vp(item))?,
                }
                self.subjects.pop();
                Ok(())
            }
            Core::Existence { subject } => self.group(subject),
            Core::Conjoined { items } => items.iter_mut().try_for_each(|item| self.core(item)),
        }
    }

    /// The subject of a clause: an object pronoun of the clause does not refer to it.
    fn subject(&mut self, subject: &mut NpGroup) -> Result<(), ParseError> {
        self.in_subject = true;
        let read = self.group(subject);
        self.in_subject = false;
        read?;
        self.subjects.push(nps(subject).into_iter().map(|np| bare(np).render()).collect());
        Ok(())
    }

    fn clause(&mut self, clause: &mut Clause) -> Result<(), ParseError> {
        self.subject(&mut clause.subject)?;
        match &mut clause.body {
            ClauseBody::Copular { predicate, agent, roles, .. } => {
                self.predicate(predicate)?;
                if let Some(agent) = agent {
                    self.group(agent)?;
                }
                self.roles(roles)?;
            }
            ClauseBody::Verbal { object, roles, content, .. } => {
                if let Some(object) = object {
                    self.group(object)?;
                }
                self.roles(roles)?;
                if let Some(content) = content {
                    self.clause(content)?;
                }
            }
        }
        self.subjects.pop();
        Ok(())
    }

    /// The parts of a verb phrase in the order of the sentence. After a
    /// giving verb, one receiver and one object stand in either order (`give
    /// each statement the names`, `give the names to each statement`), and
    /// the tree does not keep it: a pronoun in one of them has the noun
    /// phrases of the other among its candidates. What follows `become` or
    /// `remain` says a state, and names no thing.
    fn vp(&mut self, vp: &mut Vp) -> Result<(), ParseError> {
        let either_order = super::parse::is_giving_verb(&vp.verb) && matches!(vp.roles.as_slice(), [RolePp::Recipient(_)]) && vp.object.is_some();
        let state = matches!(vp.verb.to_lowercase().as_str(), "become" | "becomes" | "remain" | "remains");
        if let Some(object) = &mut vp.object {
            let mark = self.before.len();
            let others = if either_order && !self.gathering {
                let mut gatherer = Resolver::new();
                gatherer.gathering = true;
                let mut copy = vp.roles.clone();
                let _ = gatherer.roles(&mut copy);
                gatherer.before
            } else {
                Vec::new()
            };
            let borrowed = others.len();
            self.before.extend(others);
            let read = self.group(object);
            self.before.drain(mark..mark + borrowed);
            read?;
            if state {
                self.before.truncate(mark);
            }
        }
        self.roles(&mut vp.roles)?;
        if let Some(complement) = &mut vp.complement {
            self.predicate(complement)?;
        }
        match &mut vp.content {
            Some(content) => self.clause(content),
            None => Ok(()),
        }
    }

    fn predicate(&mut self, predicate: &mut Predicate) -> Result<(), ParseError> {
        match predicate {
            Predicate::AbleTo { vp } => self.vp(vp),
            Predicate::Pp { np, .. } => self.group(np),
            Predicate::Comparison(comparison) => {
                self.measure(&mut comparison.value)?;
                match &mut comparison.upper {
                    Some(upper) => self.measure(upper),
                    None => Ok(()),
                }
            }
            Predicate::Words { .. } | Predicate::Enumeration { .. } => Ok(()),
        }
    }

    fn measure(&mut self, measure: &mut Measure) -> Result<(), ParseError> {
        match measure {
            Measure::Np { np } => self.group(np),
            Measure::Quantity { .. } | Measure::Bounded { .. } => Ok(()),
        }
    }

    fn roles(&mut self, roles: &mut [RolePp]) -> Result<(), ParseError> {
        for role in roles {
            match role {
                RolePp::Recipient(group) | RolePp::Topic(group) | RolePp::Source(group) | RolePp::Goal(group) | RolePp::Agent(group) | RolePp::Means { np: group, .. } | RolePp::Location { np: group, .. } | RolePp::Other { np: group, .. } => self.group(group)?,
                RolePp::Before(clause) | RolePp::After(clause) | RolePp::Until(clause) => self.clause(clause)?,
                RolePp::Deadline(measure) | RolePp::Duration(measure) => self.measure(measure)?,
                RolePp::Rate { .. } => {}
            }
        }
        Ok(())
    }

    /// A group of noun phrases. The things that `and` joins are candidates
    /// one by one and, together, one plural candidate; the things that `or`
    /// joins are one candidate, as in `each title or locator shall contain its value`.
    fn group(&mut self, group: &mut NpGroup) -> Result<(), ParseError> {
        match group {
            NpGroup::Single(np) if is_pronoun(np) => {
                if self.collecting && !self.gathering {
                    let found = self.antecedent(&np.head.clone(), true)?;
                    *group = found.group;
                }
                Ok(())
            }
            NpGroup::Single(np) => self.np(np, true),
            NpGroup::Coordinated { items, conj, .. } => {
                let alternatives = *conj == Conj::Or;
                for item in items.iter_mut() {
                    self.np(item, !alternatives)?;
                }
                let all: Vec<Np> = items.iter().map(|np| named(&bare(np))).collect();
                let key = all.iter().map(|np| bare(np).render()).collect::<Vec<_>>().join(if alternatives { " or " } else { " and " });
                let plural = !alternatives || items.iter().any(plural);
                let texts = items.iter().all(text_alone);
                let mut together = group.clone();
                if let NpGroup::Coordinated { items, .. } = &mut together {
                    *items = all;
                }
                // Quoted texts alone are texts, and no things that have parts.
                if !texts {
                    self.before.push(Candidate { group: together, plural, key, fresh: false });
                }
                Ok(())
            }
        }
    }

    fn np(&mut self, np: &mut Np, candidate_itself: bool) -> Result<(), ParseError> {
        let mut resolved = false;
        if let Some(Det::Reference { word }) = np.det.clone() {
            match word.as_str() {
                "its" | "their" if self.collecting && !self.gathering => {
                    self.possessive(np, &word)?;
                    resolved = true;
                }
                "this" | "that" | "these" | "those" if !self.collecting => self.demonstrative(np, &word)?,
                _ => {}
            }
        }
        let demonstrative = matches!(&np.det, Some(Det::Reference { word }) if matches!(word.as_str(), "this" | "that" | "these" | "those"));
        let at = (candidate_itself && !demonstrative && !text_alone(np)).then(|| {
            self.before.push(candidate(np));
            self.before.len() - 1
        });
        if !resolved {
            // A pronoun in the owner of a thing does not refer to that thing:
            // in `the interpretation of its term`, `its` is not the interpretation.
            self.open.extend(at);
            let read = self.owners(np);
            if at.is_some() {
                self.open.pop();
            }
            read?;
            if let Some(at) = at {
                self.before[at] = candidate(np);
            }
        }
        // The noun is named before its clause: `a sequence that no line of that sequence precedes`.
        let mut head = np.clone();
        head.relative = None;
        if self.collecting && !self.gathering && !demonstrative {
            let mut seen = head.clone();
            seen.det = None;
            self.seen.push(seen);
        }
        let mut relative = np.relative.as_deref_mut();
        while let Some(clause) = relative {
            self.relative(clause, &head)?;
            relative = clause.and.as_deref_mut();
        }
        Ok(())
    }

    fn owners(&mut self, np: &mut Np) -> Result<(), ParseError> {
        if let Some(of) = &mut np.of {
            self.np(of, true)?;
        }
        np.of_also.iter_mut().try_for_each(|other| self.np(other, true))
    }

    /// A relative clause. The noun that the clause restricts is its subject
    /// where the clause has no subject of its own.
    fn relative(&mut self, relative: &mut Relative, head: &Np) -> Result<(), ParseError> {
        match &mut relative.body {
            RelativeBody::Content { clause } => self.clause(clause),
            RelativeBody::Copular { predicate, agent, roles, .. } => {
                self.subjects.push(vec![bare(head).render()]);
                self.predicate(predicate)?;
                if let Some(agent) = agent {
                    self.group(agent)?;
                }
                self.roles(roles)?;
                self.subjects.pop();
                Ok(())
            }
            RelativeBody::Verbal { object, roles, .. } => {
                self.subjects.push(vec![bare(head).render()]);
                if let Some(object) = object {
                    self.group(object)?;
                }
                self.roles(roles)?;
                self.subjects.pop();
                Ok(())
            }
            RelativeBody::ObjectGap { subject, roles, .. } => {
                self.subject(subject)?;
                self.roles(roles)?;
                self.subjects.pop();
                Ok(())
            }
        }
    }

    /// The one noun phrase that a pronoun refers to. `object` is `true` for
    /// `it`, `they` and `them`: such a pronoun after the subject of its
    /// clause does not refer to that subject, which `itself` would.
    fn antecedent(&self, word: &str, object: bool) -> Result<Candidate, ParseError> {
        let wants_plural = matches!(word.to_lowercase().as_str(), "their" | "they" | "them");
        let excluded: &[String] = match self.subjects.last() {
            Some(subject) if object && !self.in_subject => subject,
            _ => &[],
        };
        let agreeing = |list: &[Candidate], open: &[usize]| {
            let mut found: Vec<Candidate> = Vec::new();
            for (at, candidate) in list.iter().enumerate() {
                let named_before = !candidate.fresh && found.iter().any(|f| f.key == candidate.key);
                if candidate.plural == wants_plural && !open.contains(&at) && !excluded.contains(&candidate.key) && !named_before {
                    found.push(candidate.clone());
                }
            }
            found
        };
        let mut found = agreeing(&self.before, &self.open);
        if found.is_empty() {
            if let Some(later) = &self.later {
                found = agreeing(later, &[]);
            }
        }
        match found.len() {
            0 => Err(ParseError::UnresolvedPronoun { word: word.to_string() }),
            1 => Ok(found.remove(0)),
            _ => Err(ParseError::AmbiguousPronoun { word: word.to_string(), candidates: found.iter().map(|c| format!("`{}`", c.key)).collect::<Vec<_>>().join(" or ") }),
        }
    }

    /// `its header` is the header of the one thing that `its` can refer to.
    fn possessive(&mut self, np: &mut Np, word: &str) -> Result<(), ParseError> {
        // `its header of the file` has two owners: the phrase names the owner itself.
        if np.of.is_some() {
            return Err(ParseError::NoFormalReading { word: word.to_string(), advice: "a noun phrase has one owner: write the owner after `of` and drop the possessive" });
        }
        // The error names the whole phrase, so that the author sees which one is meant.
        let phrase = np.render();
        let found = self.antecedent(word, false).map_err(|error| match error {
            ParseError::AmbiguousPronoun { candidates, .. } => ParseError::AmbiguousPronoun { word: phrase.clone(), candidates },
            ParseError::UnresolvedPronoun { .. } => ParseError::UnresolvedPronoun { word: phrase.clone() },
            other => other,
        })?;
        // `each title or locator shall contain its value`: the value of the title or of the locator.
        let (owners, conj): (Vec<Np>, Conj) = match found.group {
            NpGroup::Single(one) => (vec![one], Conj::And),
            NpGroup::Coordinated { items, conj, .. } => (items, conj),
        };
        let mut owners = owners.into_iter();
        np.of = owners.next().map(Box::new);
        np.of_also = owners.collect();
        np.of_conj = (!np.of_also.is_empty()).then_some(conj);
        np.det = Some(Det::The);
        Ok(())
    }

    /// `that flow` is the flow that the sentence named before.
    fn demonstrative(&mut self, np: &mut Np, word: &str) -> Result<(), ParseError> {
        let own = words(np);
        let mut found: Vec<&Np> = Vec::new();
        for candidate in self.seen.iter() {
            let theirs = words(candidate);
            if theirs.ends_with(&own) && !found.iter().any(|f| words(f) == theirs && f.of == candidate.of && f.of_also == candidate.of_also) {
                found.push(candidate);
            }
        }
        // The phrase with the same words is the antecedent before a longer one that ends in them.
        if found.iter().any(|f| f.modifiers.len() == np.modifiers.len()) {
            found.retain(|f| f.modifiers.len() == np.modifiers.len());
        }
        match found.as_slice() {
            [] => Err(ParseError::UnresolvedPronoun { word: format!("{word} {}", np.head) }),
            [one] => {
                // The name of the antecedent is taken, and no clause of its owners:
                // a clause that holds the reference itself would never end.
                fn plain(np: &mut Np) {
                    np.relative = None;
                    if let Some(of) = &mut np.of {
                        plain(of);
                    }
                    np.of_also.iter_mut().for_each(plain);
                }
                let mut antecedent = (*one).clone();
                plain(&mut antecedent);
                np.modifiers = antecedent.modifiers;
                np.head = antecedent.head;
                if np.of.is_none() && np.of_also.is_empty() {
                    np.of = antecedent.of;
                    np.of_also = antecedent.of_also;
                    np.of_conj = antecedent.of_conj;
                }
                if np.relative.is_none() {
                    np.relative = antecedent.relative;
                }
                np.det = Some(Det::The);
                Ok(())
            }
            many => Err(ParseError::AmbiguousPronoun { word: format!("{word} {}", np.head), candidates: many.iter().map(|np| format!("`{}`", np.render())).collect::<Vec<_>>().join(" or ") }),
        }
    }
}
