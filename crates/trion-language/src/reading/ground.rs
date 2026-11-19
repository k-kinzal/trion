//! The instances of a statement over the individuals of a domain.
//!
//! A statement that names a declared type speaks about each individual of
//! the type ([`crate::reading::typed`]). Over a domain of `scope`
//! individuals of each carrier, the statement stands for one instance for
//! each assignment of its variables: the same sentence with each variable
//! replaced by the name of an individual, under the condition that the
//! individuals are of the named types and stand in the named relations.
//!
//! `When a member of a room posts a message to the room, the system shall
//! store the message.` over two individuals of each type is eight
//! instances, among them `When user#1 posts message#2 to room#1, the system
//! shall store message#2.` under the condition `member(room#1, member#1)`.
//! An instance is a simple sentence: the reading of sentences reads it as it
//! reads any other, so that one binding names one individual in the
//! condition, in the response and in every statement.
//!
//! A relation between individuals (`the user is a member of the room`) is
//! no state of a moment: it is taken out of the sentence and stands in the
//! condition of the instance as a relation of the domain.

use crate::diagnostic::SpecRef;
use crate::document::{Spec, SpecSet};
use crate::reading::lexicon::Lexicon;
use crate::reading::typed::{self, Condition, Force, Meaning, Reading, Relation, Response, Site, Term, Types, Variable};
use crate::syntax::ast::*;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use trion_solver::{Atom, Formula};

/// One instance of a statement: which individual each variable names.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct InstanceOf {
    /// The statement that the instance is an instance of.
    pub statement: String,
    /// The identifier of the instance: the statement with its binding.
    pub instance: String,
    /// Each variable with the individual that it names.
    pub binding: Vec<(String, String)>,
}

/// A statement that names a declared type outside the typed fragment.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct OutsideOf {
    pub statement: SpecRef,
    pub construct: String,
    pub why: String,
}

/// A fact of a concrete behaviour, with the names of its individuals.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(tag = "fact", rename_all = "snake_case")]
pub enum Fact {
    /// The event occurs, or the action completes.
    Occurs { verb: String, particle: Option<String>, actor: String, object: Option<String>, roles: Vec<(String, String)> },
    /// The individual is in the state.
    State { subject: String, value: String },
    /// The individuals stand in the relation.
    Related { relation: String, owner: String, member: String },
    /// The individual is of the kind.
    Kind { kind: String, subject: String },
}

/// What an atom of the formulas says of a concrete behaviour. The reading
/// states it for each atom that an instance of a typed statement holds, so
/// that a formula can be evaluated on a behaviour without reading the name
/// of an atom.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct AtomOf {
    pub atom: Atom,
    pub fact: Fact,
}

/// The typed reading of a set: its types, the meaning of each typed
/// statement and the instances over the domain.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct Individuals {
    /// The version of the meaning rules.
    pub version: &'static str,
    /// Each noun that names individuals, with the declared type of its carrier.
    pub types: Vec<(String, String)>,
    /// The number of individuals of each carrier.
    pub scope: usize,
    pub meanings: Vec<Meaning>,
    pub instances: Vec<InstanceOf>,
    pub outside: Vec<OutsideOf>,
    /// The statements about the domain, each with what it says.
    pub domain: Vec<crate::reading::typed::DomainStatement>,
    /// What each atom of the instances says of a concrete behaviour.
    pub atoms: Vec<AtomOf>,
    /// The quantity that holds the share of each statement that bounds one.
    pub shares: Vec<ShareOf>,
}

/// The quantity of the formulas that holds the share of a statement, in percent.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct ShareOf {
    pub quantity: String,
    pub statement: String,
}

/// A statement that the grounding states directly: a relation or a kind of
/// the individuals of one instance.
pub(super) struct Direct {
    pub reference: SpecRef,
    pub assume: Formula,
    pub guarantee: Formula,
}

pub(super) struct Grounded {
    /// The meaning and the assignment of each instance, by its identifier.
    pub bindings: BTreeMap<String, (usize, Vec<usize>)>,
    /// The set with each typed statement replaced by its instances, and
    /// without the statements about the domain.
    pub set: SpecSet,
    /// The same set with the statements about the domain.
    pub with_domain: SpecSet,
    pub individuals: Individuals,
    /// The condition of each instance, by its identifier.
    pub guards: BTreeMap<String, Formula>,
    pub direct: Vec<Direct>,
    /// What an instance states of the domain under its conditions: a
    /// relation or a kind of its individuals, by the identifier of the instance.
    pub claims: BTreeMap<String, Formula>,
    /// The relations that the instances speak about.
    pub relations: BTreeSet<(String, String, String)>,
    /// The statements about the domain: the reading over individuals is
    /// their whole reading, and no representative stands beside it.
    pub about_the_domain: BTreeSet<String>,
    /// The statements that bound a share: each stands for one bound on the
    /// share of its activations.
    pub shares: BTreeSet<String>,
    /// The instances of the statements that bound a share, each with its
    /// statement: what one activation of the statement is, and what answers
    /// it. An instance of this kind requires nothing; it is counted.
    pub counted: BTreeMap<String, String>,
    /// The instances whose response chooses an individual: for each
    /// alternative of the instance, in the order of the alternatives, what
    /// makes its individual one that may be chosen, and the verb phrases
    /// of the statement about that individual.
    pub alternatives: BTreeMap<String, Vec<(Formula, VpGroup)>>,
}

fn individual(noun: &str, index: usize) -> String {
    format!("{noun}#{index}")
}

fn rel(name: &str, args: Vec<String>) -> Formula {
    Formula::atom(Atom::Rel { name: name.to_string(), args })
}

fn denied_if(formula: Formula, denied: bool) -> Formula {
    if denied {
        Formula::not(formula)
    } else {
        formula
    }
}

/// The assignment of one instance: each variable with its index in its carrier.
struct Assignment<'a> {
    meaning: &'a Meaning,
    index: Vec<usize>,
}

impl Assignment<'_> {
    /// The index of the individual of a variable. A variable that the
    /// response chooses has no individual in the assignment of the
    /// instance (its place holds 0): it has one in each alternative.
    fn index_of(&self, term: &Term) -> Option<usize> {
        match term {
            Term::Variable(id) => self.index.get(*id as usize).copied().filter(|index| *index > 0),
            _ => None,
        }
    }

    fn name(&self, id: u32) -> String {
        individual(&self.meaning.variables[id as usize].carrier, self.index[id as usize])
    }

    fn related(&self, relation: &Relation, relations: &mut BTreeSet<(String, String, String)>) -> Option<Formula> {
        let (owner, member) = (self.index_of(&relation.owner)?, self.index_of(&relation.member)?);
        relations.insert((relation.relation.clone(), relation.owner_noun.clone(), relation.relation.clone()));
        Some(denied_if(rel(&relation.relation, vec![individual(&relation.owner_noun, owner), individual(&relation.relation, member)]), relation.denied))
    }

    fn kind(&self, kind: &str, subject: &Term, denied: bool) -> Option<Formula> {
        Some(denied_if(rel(kind, vec![individual(kind, self.index_of(subject)?)]), denied))
    }

    /// The name of what a term denotes in the instance.
    fn term(&self, term: &Term) -> String {
        match term {
            Term::Variable(id) => self.name(*id),
            Term::Constant(name) => name.clone(),
            Term::Attribute { name, of } => format!("{name} of {}", self.term(of)),
        }
    }

    fn occurs(&self, pattern: &typed::Pattern) -> Fact {
        Fact::Occurs { verb: pattern.verb.clone(), particle: pattern.particle.clone(), actor: self.term(&pattern.actor), object: pattern.object.as_ref().map(|o| self.term(o)), roles: pattern.roles.iter().map(|(marker, term)| (marker.clone(), self.term(term))).collect() }
    }

    fn related_fact(&self, relation: &Relation) -> Option<AtomOf> {
        let (owner, member) = (self.index_of(&relation.owner)?, self.index_of(&relation.member)?);
        Some(AtomOf {
            atom: Atom::Rel { name: relation.relation.clone(), args: vec![individual(&relation.owner_noun, owner), individual(&relation.relation, member)] },
            fact: Fact::Related { relation: relation.relation.clone(), owner: self.term(&relation.owner), member: self.term(&relation.member) },
        })
    }

    fn kind_fact(&self, kind: &str, subject: &Term) -> Option<AtomOf> {
        Some(AtomOf { atom: Atom::Rel { name: kind.to_string(), args: vec![individual(kind, self.index_of(subject)?)] }, fact: Fact::Kind { kind: kind.to_string(), subject: self.term(subject) } })
    }

    /// What each atom of the condition of the instance says.
    fn account(&self, atoms: &mut Vec<AtomOf>) {
        let mut found: Vec<AtomOf> = Vec::new();
        for variable in self.meaning.variables.iter().filter(|v| self.index[v.id as usize] > 0) {
            found.extend(self.kind_fact(&variable.noun, &Term::Variable(variable.id)));
        }
        for relation in &self.meaning.restrictions {
            found.extend(self.related_fact(relation));
        }
        let conditions = self.meaning.frames.iter().flat_map(|f| &f.conditions).chain(&self.meaning.exception);
        for condition in conditions {
            match condition {
                Condition::Related(relation) => found.extend(self.related_fact(relation)),
                Condition::Kind { kind, subject, .. } => found.extend(self.kind_fact(kind, subject)),
                _ => {}
            }
        }
        for response in &self.meaning.responses {
            match response {
                Response::Related(relation) => found.extend(self.related_fact(relation)),
                Response::Kind { kind, subject, .. } => found.extend(self.kind_fact(kind, subject)),
                _ => {}
            }
        }
        for atom in found {
            if !atoms.contains(&atom) {
                atoms.push(atom);
            }
        }
    }

    /// The condition of the instance: the types of its individuals, the
    /// restrictions of its variables and the relations that its conditions name.
    fn guard(&self, relations: &mut BTreeSet<(String, String, String)>) -> Vec<Formula> {
        let mut parts: Vec<Formula> = Vec::new();
        for variable in self.meaning.variables.iter().filter(|v| self.index[v.id as usize] > 0) {
            parts.push(rel(&variable.noun, vec![individual(&variable.noun, self.index[variable.id as usize])]));
        }
        for relation in &self.meaning.restrictions {
            parts.extend(self.related(relation, relations));
        }
        for condition in self.meaning.frames.iter().flat_map(|f| &f.conditions) {
            match condition {
                Condition::Related(relation) => parts.extend(self.related(relation, relations)),
                Condition::Kind { kind, subject, denied } => parts.extend(self.kind(kind, subject, *denied)),
                _ => {}
            }
        }
        match &self.meaning.exception {
            Some(Condition::Related(relation)) => parts.extend(self.related(relation, relations).map(Formula::not)),
            Some(Condition::Kind { kind, subject, denied }) => parts.extend(self.kind(kind, subject, *denied).map(Formula::not)),
            _ => {}
        }
        parts.dedup();
        parts
    }
}

impl Assignment<'_> {
    /// What makes an individual one that the response may choose: its kind,
    /// and the restrictions that name it.
    fn choice(&self, relations: &mut BTreeSet<(String, String, String)>) -> Vec<Formula> {
        let chosen = |term: &Term| matches!(term, Term::Variable(id) if self.meaning.variables[*id as usize].site == Site::Chosen);
        let mut parts: Vec<Formula> = Vec::new();
        for variable in self.meaning.variables.iter().filter(|v| v.site == Site::Chosen) {
            parts.push(rel(&variable.noun, vec![individual(&variable.noun, self.index[variable.id as usize])]));
        }
        for relation in self.meaning.restrictions.iter().filter(|r| chosen(&r.owner) || chosen(&r.member)) {
            parts.extend(self.related(relation, relations));
        }
        parts
    }
}

/// The variables of a statement that an instance binds (`chosen` false) or
/// that the response chooses (`chosen` true).
fn variables_of(meaning: &Meaning, chosen: bool) -> Vec<u32> {
    meaning.variables.iter().filter(|v| (v.site == Site::Chosen) == chosen).map(|v| v.id).collect()
}

/// Each assignment of the named variables over the individuals
/// `1..=scope`, beside what `base` assigns. The place of a variable
/// without an individual holds 0.
fn filled(count: usize, variables: &[u32], base: Option<&[usize]>, scope: usize) -> Vec<Vec<usize>> {
    let mut all = vec![base.map_or_else(|| vec![0; count], <[usize]>::to_vec)];
    for id in variables {
        all = all
            .into_iter()
            .flat_map(|done| {
                (1..=scope).map(move |i| {
                    let mut next = done.clone();
                    next[*id as usize] = i;
                    next
                })
            })
            .collect();
    }
    all
}

/// `true` when the assignment gives different individuals to the variables
/// of one noun: `a member` and `a second member` are two members. The
/// place of a variable without an individual holds 0.
fn told_apart(meaning: &Meaning, index: &[usize]) -> bool {
    meaning.variables.iter().all(|a| meaning.variables.iter().all(|b| a.id >= b.id || a.noun != b.noun || index[a.id as usize] == 0 || index[a.id as usize] != index[b.id as usize]))
}

/// Replaces each variable of a sentence by the name of its individual, and
/// takes the relations between individuals out of the conditions.
struct Substitution<'a> {
    types: &'a Types,
    lex: &'a Lexicon,
    /// The name of the individual of each variable, by the key of the variable.
    names: BTreeMap<String, String>,
}

impl Substitution<'_> {
    fn key(&self, np: &Np) -> Option<String> {
        let head = typed::head_noun(np, self.lex);
        self.types.canonical(&head)?;
        let ordinals = np.modifiers.iter().filter(|m| ["second", "third", "fourth", "fifth", "sixth", "other"].iter().any(|w| m.eq_ignore_ascii_case(w))).map(|m| m.to_lowercase());
        Some(ordinals.chain(std::iter::once(head)).collect::<Vec<_>>().join(" "))
    }

    fn np(&self, np: &mut Np) {
        match self.key(np).and_then(|key| self.names.get(&key)) {
            Some(name) => *np = Np { det: None, modifiers: Vec::new(), head: name.clone(), of: None, relative: None, of_also: Vec::new(), of_conj: None },
            None => {
                if let Some(of) = &mut np.of {
                    self.np(of);
                }
                np.of_also.iter_mut().for_each(|owner| self.np(owner));
            }
        }
    }

    fn group(&self, group: &mut NpGroup) {
        match group {
            NpGroup::Single(np) => self.np(np),
            NpGroup::Coordinated { items, .. } => items.iter_mut().for_each(|np| self.np(np)),
        }
    }

    fn measure(&self, measure: &mut Measure) {
        if let Measure::Np { np } = measure {
            self.group(np);
        }
    }

    fn roles(&self, roles: &mut [RolePp]) {
        for role in roles {
            match role {
                RolePp::Recipient(g) | RolePp::Topic(g) | RolePp::Source(g) | RolePp::Goal(g) | RolePp::Agent(g) => self.group(g),
                RolePp::Means { np, .. } | RolePp::Location { np, .. } | RolePp::Other { np, .. } => self.group(np),
                RolePp::Deadline(m) | RolePp::Duration(m) => self.measure(m),
                RolePp::Before(c) | RolePp::After(c) | RolePp::Until(c) => self.clause(c),
                RolePp::Rate { .. } => {}
            }
        }
    }

    fn predicate(&self, predicate: &mut Predicate) {
        match predicate {
            Predicate::Comparison(c) => {
                self.measure(&mut c.value);
                c.upper.iter_mut().for_each(|m| self.measure(m));
            }
            Predicate::AbleTo { vp } => self.vp(vp),
            Predicate::Pp { np, .. } => self.group(np),
            Predicate::Words { .. } | Predicate::Enumeration { .. } => {}
        }
    }

    fn clause(&self, clause: &mut Clause) {
        self.group(&mut clause.subject);
        match &mut clause.body {
            ClauseBody::Copular { predicate, agent, roles, .. } => {
                self.predicate(predicate);
                agent.iter_mut().for_each(|g| self.group(g));
                self.roles(roles);
            }
            ClauseBody::Verbal { object, roles, content, .. } => {
                object.iter_mut().for_each(|g| self.group(g));
                self.roles(roles);
                content.iter_mut().for_each(|c| self.clause(c));
            }
        }
    }

    fn vp(&self, vp: &mut Vp) {
        vp.object.iter_mut().for_each(|g| self.group(g));
        self.roles(&mut vp.roles);
        vp.complement.iter_mut().for_each(|p| self.predicate(p));
        vp.content.iter_mut().for_each(|c| self.clause(c));
    }

    /// `true` for a clause that states a relation between individuals or
    /// the kind of an individual: it stands in the condition of the instance.
    fn of_the_domain(&self, clause: &Clause) -> bool {
        let ClauseBody::Copular { predicate: Predicate::Words { words }, agent: None, roles, .. } = &clause.body else { return false };
        let NpGroup::Single(subject) = &clause.subject else { return false };
        self.key(subject).is_some() && matches!(typed::said(words, roles, self.lex), Some(typed::Said::Related { .. } | typed::Said::Kind { .. }))
    }

    fn clauses(&self, group: &mut ClauseGroup) {
        group.items.retain(|clause| !self.of_the_domain(clause));
        if group.items.len() < 2 {
            group.conj = None;
        }
        group.items.iter_mut().for_each(|c| self.clause(c));
    }

    fn sentence(&self, sentence: &mut Sentence) {
        let frames = &mut sentence.frames;
        for frame in frames.scopes.iter_mut().chain(frames.states.iter_mut()) {
            self.clauses(&mut frame.clause);
        }
        frames.scopes.retain(|f| !f.clause.items.is_empty());
        frames.states.retain(|f| !f.clause.items.is_empty());
        if let Some(trigger) = &mut frames.trigger {
            self.clauses(&mut trigger.clause);
        }
        if frames.trigger.as_ref().is_some_and(|t| t.clause.items.is_empty()) {
            frames.trigger = None;
        }
        if sentence.exception.as_ref().is_some_and(|c| self.of_the_domain(c)) {
            sentence.exception = None;
        }
        sentence.exception.iter_mut().for_each(|c| self.clause(c));
        match &mut sentence.core {
            Core::Deontic { subject, vp, .. } => {
                self.group(subject);
                match vp {
                    VpGroup::Single(vp) => self.vp(vp),
                    VpGroup::Alternatives { items } | VpGroup::All { items, .. } => items.iter_mut().for_each(|vp| self.vp(vp)),
                    VpGroup::Composite(composition) => composition.leaves.iter_mut().for_each(|vp| self.vp(vp)),
                }
            }
            Core::Description { subject, predicate, roles, .. } => {
                self.group(subject);
                self.predicate(predicate);
                self.roles(roles);
            }
            _ => {}
        }
        match &mut sentence.purpose {
            Some(Purpose::SoThat(clause)) => self.clause(clause),
            Some(Purpose::InOrderTo(vp)) => self.vp(vp),
            None => {}
        }
    }
}

fn binding_text(meaning: &Meaning, index: &[usize]) -> String {
    meaning.variables.iter().filter(|v| v.site != Site::Chosen).map(|v| individual(&v.carrier, index[v.id as usize])).collect::<Vec<_>>().join(",")
}

/// The declared types of a set: each noun of a carrier that holds a declared
/// noun, with the smallest declared noun of the carrier.
fn types_of(set: &SpecSet, lex: &Lexicon, carriers: &BTreeMap<String, String>) -> Types {
    let mut declared: BTreeSet<String> = BTreeSet::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let scoped = lex.in_document(doc);
        for decl in &doc.individuals {
            let words: Vec<String> = decl.name.split_whitespace().map(str::to_string).collect();
            declared.insert(typed::noun_of(&words, &scoped));
        }
    }
    let root = |noun: &str| carriers.get(noun).cloned().unwrap_or_else(|| noun.to_string());
    let mut name_of: BTreeMap<String, String> = BTreeMap::new();
    for noun in &declared {
        name_of.entry(root(noun)).or_insert_with(|| noun.clone());
    }
    let mut canonical: BTreeMap<String, String> = BTreeMap::new();
    for noun in declared.iter().chain(carriers.keys()) {
        if let Some(name) = name_of.get(&root(noun)) {
            canonical.insert(noun.clone(), name.clone());
        }
    }
    Types::new(canonical)
}

/// Reads a set over individuals. `None` when the set declares no type.
pub(super) fn apply(set: &SpecSet, lex: &Lexicon, scope: usize) -> Option<Grounded> {
    if scope == 0 || set.packages.iter().flat_map(|p| &p.documents).all(|d| d.individuals.is_empty()) {
        return None;
    }
    let (scope, carriers) = crate::reading::instances::domain(set, lex, scope);
    let types = types_of(set, lex, &carriers);
    // A scenario names its individuals: the domain holds as many of each carrier as a scenario names.
    let mut scope = scope;
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let scoped = lex.in_document(doc);
        for scenario in &doc.scenarios {
            let mut named: BTreeMap<&str, usize> = BTreeMap::new();
            for (_, written) in &scenario.individuals {
                let words: Vec<String> = written.split_whitespace().map(str::to_string).collect();
                if let Some(carrier) = types.canonical(&typed::noun_of(&words, &scoped)) {
                    *named.entry(carrier).or_default() += 1;
                }
            }
            scope = scope.max(named.values().copied().max().unwrap_or(0));
        }
    }
    let mut individuals = Individuals { version: typed::VERSION, types: types.nouns().map(|(noun, declared)| (noun.to_string(), declared.to_string())).collect(), scope, ..Default::default() };
    // The meaning of each statement, by the package and the identifier of the statement.
    let mut read: BTreeMap<(usize, String), Meaning> = BTreeMap::new();
    let mut about_the_domain: BTreeSet<String> = BTreeSet::new();
    for (p, pkg) in set.packages.iter().enumerate() {
        for doc in &pkg.documents {
            let scoped = lex.in_document(doc);
            for spec in &doc.specs {
                let display = if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) };
                if crate::reading::instances::about_the_domain(spec, &scoped) {
                    if typed::names_a_type(&spec.sentence, &types, &scoped) {
                        about_the_domain.insert(display);
                    }
                    continue;
                }
                match typed::read(&display, &crate::expand::lowered(&spec.sentence), &types, &scoped) {
                    Reading::Untyped => {}
                    Reading::Typed(meaning) if spec.otherwise && meaning.frames.iter().any(|frame| {
                        matches!(frame.kind, typed::FrameKind::When | typed::FrameKind::If)
                            && frame.conditions.iter().any(|condition| matches!(condition, Condition::Related(_) | Condition::Kind { .. }))
                    }) => {
                        individuals.outside.push(OutsideOf {
                            statement: SpecRef { id: display, file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() },
                            construct: "otherwise".into(),
                            why: "the grounding of a trigger over individual types or relations does not preserve its complement: state the complementary condition in a separate sentence".into(),
                        });
                    }
                    Reading::Typed(meaning) => {
                        read.insert((p, spec.display_id()), *meaning);
                    }
                    Reading::Outside { construct, why } => individuals.outside.push(OutsideOf { statement: SpecRef { id: display, file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() }, construct, why }),
                }
            }
        }
    }
    // A measure names one population: the activations of the statements
    // that bound a share of it. Two statements with other variables or
    // other conditions have other activations, and one name for both would
    // order the shares of two populations as the shares of one.
    let mut populations: BTreeMap<String, (String, Meaning)> = BTreeMap::new();
    let mut apart: Vec<(usize, String)> = Vec::new();
    for ((p, id), meaning) in &read {
        let Some(share) = &meaning.share else { continue };
        let (first, other) = populations.entry(share.population.clone()).or_insert_with(|| (meaning.statement.clone(), meaning.clone()));
        if (&other.variables, &other.restrictions, &other.frames, &other.exception) != (&meaning.variables, &meaning.restrictions, &meaning.frames, &meaning.exception) {
            let spec = set.packages[*p].documents.iter().flat_map(|d| &d.specs).find(|spec| spec.display_id() == *id);
            let (file, line, text) = spec.map_or((String::new(), 0, String::new()), |spec| (spec.file.clone(), spec.line, spec.sentence.source.clone()));
            individuals.outside.push(OutsideOf {
                statement: SpecRef { id: meaning.statement.clone(), file, line, text },
                construct: format!("percent of {}", share.population),
                why: format!("the measure `{}` names the activations of [{first}], and this statement applies to other individuals or under other conditions, so it counts another population: declare a measure of its own for it", share.population),
            });
            apart.push((*p, id.clone()));
        }
    }
    for key in apart {
        read.remove(&key);
    }
    // The instances of a statement whose bindings agree with a binding on
    // each variable that both statements name.
    let agreeing = |p: usize, target: &str, meaning: &Meaning, index: &[usize]| -> Vec<String> {
        let Some(other) = read.get(&(p, target.to_string())) else { return vec![target.to_string()] };
        let bound = |meaning: &Meaning| -> Vec<Variable> { meaning.variables.iter().filter(|v| v.site != Site::Chosen).cloned().collect() };
        filled(other.variables.len(), &variables_of(other, false), None, scope)
            .into_iter()
            .filter(|candidate| told_apart(other, candidate))
            .filter(|candidate| bound(other).iter().all(|v| bound(meaning).iter().find(|own| own.key == v.key && own.carrier == v.carrier).is_none_or(|own| index[own.id as usize] == candidate[v.id as usize])))
            .map(|candidate| format!("{target}/{}", binding_text(other, &candidate)))
            .collect()
    };
    let order: BTreeMap<(usize, String), usize> = read.keys().cloned().enumerate().map(|(at, key)| (key, at)).collect();
    let mut grounded = Grounded { bindings: BTreeMap::new(), with_domain: SpecSet::default(), set: set.clone(), individuals, guards: BTreeMap::new(), direct: Vec::new(), claims: BTreeMap::new(), relations: BTreeSet::new(), about_the_domain: BTreeSet::new(), shares: BTreeSet::new(), counted: BTreeMap::new(), alternatives: BTreeMap::new() };
    for (p, pkg) in grounded.set.packages.iter_mut().enumerate() {
        let (is_root, name) = (pkg.is_root, pkg.name.clone());
        for doc in &mut pkg.documents {
            let scoped = lex.in_document(doc);
            let mut specs: Vec<Spec> = Vec::new();
            for spec in std::mem::take(&mut doc.specs) {
                let Some(meaning) = read.get(&(p, spec.display_id())) else {
                    // A statement without variables that yields to a statement with them yields to each instance.
                    let mut spec = spec;
                    let none = Meaning { variables: Vec::new(), ..placeholder() };
                    spec.overrides = spec.overrides.iter().flat_map(|target| agreeing(p, target, &none, &[])).collect();
                    spec.details = spec.details.iter().flat_map(|target| agreeing(p, target, &none, &[])).collect();
                    specs.push(spec);
                    continue;
                };
                let display = |id: &str| if is_root { id.to_string() } else { format!("{name}::{id}") };
                // The instances are instances of the plain form of the statement.
                let mut spec = spec;
                if let Some(plain) = typed::plain(&spec.sentence, &types, &scoped) {
                    spec.sentence = plain;
                }
                // A bound on a share is a statement about the activations as
                // a whole. The statement stays as the bound; its instances
                // say what one activation is and what answers it, without
                // the bound, and they are counted and not required.
                let counted = meaning.share.is_some();
                let spec = if counted {
                    grounded.shares.insert(display(&spec.display_id()));
                    specs.push(spec.clone());
                    let mut one = spec;
                    crate::reading::model::without_share(&mut one.sentence);
                    one
                } else {
                    spec
                };
                let picks = variables_of(meaning, true);
                for index in filled(meaning.variables.len(), &variables_of(meaning, false), None, scope).into_iter().filter(|index| told_apart(meaning, index)) {
                    let assignment = Assignment { meaning, index: index.clone() };
                    let instance_id = format!("{}/{}", spec.display_id(), binding_text(meaning, &index));
                    let guard = assignment.guard(&mut grounded.relations);
                    assignment.account(&mut grounded.individuals.atoms);
                    grounded.bindings.insert(display(&instance_id), (order[&(p, spec.display_id())], index.clone()));
                    if counted {
                        grounded.counted.insert(display(&instance_id), display(&spec.display_id()));
                    }
                    let guard = if guard.len() == 1 { guard[0].clone() } else { Formula::And(guard) };
                    grounded.individuals.instances.push(InstanceOf {
                        statement: display(&spec.display_id()),
                        instance: display(&instance_id),
                        binding: meaning.variables.iter().filter(|v| v.site != Site::Chosen).map(|v| (v.key.clone(), assignment.name(v.id))).collect(),
                    });
                    // A relation or a kind that a statement without a modal
                    // verb states of its individuals is a fact of the domain.
                    let stated = match (meaning.force, meaning.responses.as_slice()) {
                        (Force::Description, [Response::Related(relation)]) => assignment.related(relation, &mut grounded.relations),
                        (Force::Description, [Response::Kind { kind, subject, denied }]) => assignment.kind(kind, subject, *denied),
                        _ => None,
                    };
                    if let Some(guarantee) = &stated {
                        if meaning.frames.iter().flat_map(|f| &f.conditions).all(|c| matches!(c, Condition::Related(_) | Condition::Kind { .. })) && meaning.exception.as_ref().is_none_or(|c| matches!(c, Condition::Related(_) | Condition::Kind { .. })) {
                            grounded.direct.push(Direct { reference: SpecRef { id: display(&instance_id), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() }, assume: guard, guarantee: guarantee.clone() });
                            continue;
                        }
                        // Under an event or a state, the sentence gives the condition and the domain gives the claim.
                        grounded.claims.insert(display(&instance_id), guarantee.clone());
                    }
                    let names = meaning.variables.iter().filter(|v| v.site != Site::Chosen).map(|v| (v.key.clone(), assignment.name(v.id))).collect();
                    let mut instance = spec.clone();
                    instance.id = Some(instance_id.clone());
                    instance.overrides = spec.overrides.iter().flat_map(|target| agreeing(p, target, meaning, &index)).collect();
                    instance.details = spec.details.iter().flat_map(|target| agreeing(p, target, meaning, &index)).collect();
                    Substitution { types: &types, lex: &scoped, names }.sentence(&mut instance.sentence);
                    // An individual that the response chooses: the instance
                    // requires the action of one of the individuals of the
                    // domain, each under what makes it one that may be chosen.
                    if let (false, Core::Deontic { vp, .. }) = (picks.is_empty(), &instance.sentence.core) {
                        let whole = vp.clone();
                        let mut groups: Vec<VpGroup> = Vec::new();
                        let mut eligible: Vec<Formula> = Vec::new();
                        for full in filled(meaning.variables.len(), &picks, Some(&index), scope).into_iter().filter(|full| told_apart(meaning, full)) {
                            let alternative = Assignment { meaning, index: full.clone() };
                            let parts = alternative.choice(&mut grounded.relations);
                            alternative.account(&mut grounded.individuals.atoms);
                            let names = meaning.variables.iter().filter(|v| v.site == Site::Chosen).map(|v| (v.key.clone(), alternative.name(v.id))).collect();
                            let chosen = Substitution { types: &types, lex: &scoped, names };
                            let mut group = whole.clone();
                            match &mut group {
                                VpGroup::Single(vp) => chosen.vp(vp),
                                VpGroup::Alternatives { items } | VpGroup::All { items, .. } => items.iter_mut().for_each(|vp| chosen.vp(vp)),
                                VpGroup::Composite(composition) => composition.leaves.iter_mut().for_each(|vp| chosen.vp(vp)),
                            }
                            grounded.bindings.insert(format!("{}|{}", display(&instance_id), groups.len()), (order[&(p, spec.display_id())], full));
                            groups.push(group);
                            eligible.push(if parts.len() == 1 { parts[0].clone() } else { Formula::And(parts) });
                        }
                        // The sentence of the instance names each action of each alternative.
                        let singles: Option<Vec<Vp>> = groups.iter().map(|group| if let VpGroup::Single(vp) = group { Some(vp.clone()) } else { None }).collect();
                        if let Core::Deontic { vp, .. } = &mut instance.sentence.core {
                            *vp = match singles {
                                Some(mut items) if items.len() == 1 => VpGroup::Single(items.remove(0)),
                                Some(items) => VpGroup::Alternatives { items },
                                None => {
                                    let items: Vec<Vp> = groups.iter().flat_map(|group| group.items().to_vec()).collect();
                                    VpGroup::All { negated: vec![false; items.len()], items }
                                }
                            };
                        }
                        grounded.alternatives.insert(display(&instance_id), eligible.into_iter().zip(groups).collect());
                    }
                    grounded.guards.insert(display(&instance_id), guard);
                    specs.push(instance);
                }
            }
            doc.specs = specs;
        }
    }
    grounded.individuals.meanings = read.into_values().collect();
    grounded.with_domain = grounded.set.clone();
    for pkg in &mut grounded.set.packages {
        let (is_root, name) = (pkg.is_root, pkg.name.clone());
        for doc in &mut pkg.documents {
            doc.specs.retain(|spec| !about_the_domain.contains(&if is_root { spec.display_id() } else { format!("{name}::{}", spec.display_id()) }));
        }
    }
    grounded.about_the_domain = about_the_domain;
    Some(grounded)
}

fn placeholder() -> Meaning {
    Meaning { statement: String::new(), version: typed::VERSION, source: String::new(), variables: Vec::new(), restrictions: Vec::new(), frames: Vec::new(), exception: None, force: Force::Description, choice: typed::Choice::One, responses: Vec::new(), share: None, steps: Vec::new() }
}

fn single_atom(formula: &Formula) -> Option<Atom> {
    match formula {
        Formula::Atom(atom) => Some(atom.clone()),
        Formula::Not(inner) => single_atom(inner),
        _ => None,
    }
}

impl Grounded {
    /// States what the atoms of one instance say: the atom of each
    /// condition that the sentence keeps and the atom of each response.
    /// `condition` gives the formula of one clause under its frame keyword,
    /// and `guarantee` is the guarantee of the contract of the instance.
    pub(super) fn account(&self, instance: &str, sentence: &Sentence, guarantee: &Formula, condition: &dyn Fn(&str, &Clause) -> Formula, atoms: &mut Vec<AtomOf>) {
        let Some((at, index)) = self.bindings.get(instance) else { return };
        let meaning = &self.individuals.meanings[*at];
        let assignment = Assignment { meaning, index: index.clone() };
        let mut push = |atom: Atom, fact: Fact| {
            let entry = AtomOf { atom, fact };
            if !atoms.contains(&entry) {
                atoms.push(entry);
            }
        };
        // The clauses of the sentence in the order of the frames; the
        // relations and the kinds were taken out of it.
        let kept: Vec<(&str, &Clause)> = sentence
            .frames
            .scopes
            .iter()
            .chain(&sentence.frames.states)
            .map(|f| (f.keyword.as_str(), &f.clause))
            .chain(sentence.frames.trigger.iter().map(|t| (t.keyword.as_str(), &t.clause)))
            .flat_map(|(keyword, group)| group.items.iter().map(move |clause| (keyword, clause)))
            .collect();
        let stated = meaning.frames.iter().flat_map(|f| &f.conditions).filter(|c| !matches!(c, Condition::Related(_) | Condition::Kind { .. }));
        for ((keyword, clause), stated) in kept.into_iter().zip(stated) {
            let Some(atom) = single_atom(&condition(keyword, clause)) else { continue };
            match stated {
                Condition::Occurs { pattern, .. } => push(atom, assignment.occurs(pattern)),
                Condition::Holds { subject, value, .. } => push(atom, Fact::State { subject: assignment.term(subject), value: value.clone() }),
                _ => {}
            }
        }
        if let (Some(clause), Some(stated)) = (&sentence.exception, &meaning.exception) {
            if let Some(atom) = single_atom(&condition("unless", clause)) {
                match stated {
                    Condition::Occurs { pattern, .. } => push(atom, assignment.occurs(pattern)),
                    Condition::Holds { subject, value, .. } => push(atom, Fact::State { subject: assignment.term(subject), value: value.clone() }),
                    _ => {}
                }
            }
        }
        // The actions of the guarantee in the order of the responses.
        let mut actions: Vec<String> = Vec::new();
        let mut values: Vec<Atom> = Vec::new();
        guarantee.atoms(true, &mut |atom, _| match atom {
            Atom::Act { key } | Atom::Forbid { key } if !actions.contains(key) => actions.push(key.clone()),
            Atom::Val { .. } if !values.contains(atom) => values.push(atom.clone()),
            // An enumeration admits each listed value: the state is the value of the same attribute.
            Atom::Dom { attr, value } => {
                let state = Atom::Val { attr: attr.clone(), value: value.clone() };
                if !values.contains(&state) {
                    values.push(state);
                }
            }
            _ => {}
        });
        let required: Vec<&typed::Pattern> = meaning.responses.iter().filter_map(|r| match r {
            Response::Action { pattern, .. } => Some(pattern),
            _ => None,
        }).collect();
        // A required action with a role is also the action without its
        // roles: the guarantee holds that atom after the atom of the action.
        let mut named: Vec<(String, Fact)> = Vec::new();
        let mut next = 0;
        for key in actions {
            match named.last() {
                Some((whole, Fact::Occurs { verb, particle, actor, object, roles })) if !roles.is_empty() && whole.len() > key.len() && whole.starts_with(key.as_str()) => {
                    let base = Fact::Occurs { verb: verb.clone(), particle: particle.clone(), actor: actor.clone(), object: object.clone(), roles: Vec::new() };
                    named.push((key, base));
                }
                _ => {
                    let Some(pattern) = required.get(next) else {
                        named.clear();
                        break;
                    };
                    named.push((key, assignment.occurs(pattern)));
                    next += 1;
                }
            }
        }
        if next == required.len() {
            for (key, fact) in named {
                push(Atom::Act { key }, fact);
            }
        }
        match (meaning.responses.as_slice(), values.as_slice()) {
            ([Response::State { subject, value, .. }], [atom]) => push(atom.clone(), Fact::State { subject: assignment.term(subject), value: value.clone() }),
            ([Response::Values { subject, values: listed }], atoms) if atoms.len() == listed.len() => {
                for (atom, value) in atoms.iter().zip(listed) {
                    push(atom.clone(), Fact::State { subject: assignment.term(subject), value: value.clone() });
                }
            }
            _ => {}
        }
        // The events that an order names.
        if let Core::Deontic { vp, .. } = &sentence.core {
            let named = vp.items().iter().flat_map(|item| &item.roles).filter_map(|role| match role {
                RolePp::After(clause) | RolePp::Before(clause) => Some(&**clause),
                _ => None,
            });
            let patterns = meaning.responses.iter().flat_map(|r| match r {
                Response::Action { after, before, .. } => after.iter().chain(before).collect::<Vec<_>>(),
                _ => Vec::new(),
            });
            for (clause, pattern) in named.zip(patterns) {
                if let Some(atom) = single_atom(&condition("when", clause)) {
                    push(atom, assignment.occurs(pattern));
                }
            }
        }
    }
}
