//! Modeling: each sentence becomes an assume-guarantee contract, and the
//! contracts compose into one set of formulas.

use super::lexicon::{is_article, strip_backticks, Lexicon};
use crate::diagnostic::SpecRef;
use crate::document::{Role, SpecSet};
use trion_solver::{Atom, Cmp, Formula, NUMERIC_SCALE};
use crate::syntax::ast::*;
pub(super) use crate::syntax::words::base_verb;
use regex::Regex;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

/// The conjunction or the disjunction of some formulas; one formula stands for itself.
fn combine(conj: Option<Conj>, mut parts: Vec<Formula>) -> Formula {
    match (parts.len(), conj) {
        (1, _) => parts.remove(0),
        (_, Some(Conj::Or)) => Formula::Or(parts),
        _ => Formula::And(parts),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ConstraintKind {
    Spec,
    /// A `may` sentence: no other statement forbids its action where it
    /// applies. A prohibition that applies there contradicts it.
    Permission,
    Binding,
    Form,
    /// What a definition, an inclusion, an exclusion or a refinement says
    /// about terms. It holds at every moment and obliges nobody.
    Axiom,
    /// A statement is detailed by other statements. The details must refine
    /// it, which is a proof obligation and no premise: the relation adds no
    /// formula to any question.
    Refinement,
    /// What a statement about terms says about the atoms of other
    /// statements, and what a statement says about individuals whose domain
    /// other statements name. It is a relation between entries and no part
    /// of the local reading of its statement; it holds as an axiom does.
    Carried,
}

impl ConstraintKind {
    /// `true` for what the vocabulary and the refinements say: no obligation.
    pub fn is_axiom(self) -> bool {
        matches!(self, ConstraintKind::Axiom | ConstraintKind::Refinement | ConstraintKind::Carried)
    }

    /// `true` for what a statement about terms says, alone or applied to
    /// the atoms of other statements.
    pub fn is_vocabulary(self) -> bool {
        matches!(self, ConstraintKind::Axiom | ConstraintKind::Carried)
    }
}

/// A relation between entries that a statement about terms or individuals
/// gives rise to: `applied` for an inclusion, an exclusion or a definition
/// over the atoms of other statements, `individuals` for a statement read
/// over a domain that other statements name.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Applied {
    pub kind: String,
    pub subject: SpecRef,
    pub rests_on: Vec<SpecRef>,
}

/// One contract. `assume → guarantee` is the unit of composition.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Constraint {
    pub kind: ConstraintKind,
    pub assume: Formula,
    pub guarantee: Formula,
    pub refs: Vec<SpecRef>,
}

impl Constraint {
    pub fn formula(&self) -> Formula {
        match self.assume {
            Formula::True => self.guarantee.clone(),
            _ => Formula::implies(self.assume.clone(), self.guarantee.clone()),
        }
    }

    pub fn has_guard(&self) -> bool {
        self.assume != Formula::True
    }
}

/// An instance of a statement that bounds a share: what one activation of
/// the statement is and what answers it. It requires nothing by itself; the
/// statement counts it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Counted {
    /// The statement that bounds the share.
    pub statement: String,
    pub constraint: Constraint,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Default)]
pub struct Model {
    pub constraints: Vec<Constraint>,
    /// The states that a feature scope selects (`Where the audit feature is
    /// included`): a configuration, which holds one value over a whole
    /// behaviour.
    #[serde(skip)]
    pub configured: std::collections::BTreeSet<String>,
    /// The statements that the reading over the individuals of a bounded
    /// domain reads: what their predicates and values say is a relation.
    #[serde(skip)]
    pub over_instances: std::collections::BTreeSet<String>,
    /// The instances that the statements that bound a share count.
    pub counted: Vec<Counted>,
    /// Axioms that always hold, such as the exclusivity of attribute values.
    pub background: Vec<Formula>,
    /// Attributes whose whole domain is known, with their values.
    pub closed_domains: BTreeMap<String, BTreeSet<String>>,
    /// For each attribute, the values that appear in a condition.
    pub guarded_values: BTreeMap<String, BTreeSet<String>>,
    /// Closed domains as first enumerated, before any `extend`.
    pub base_domains: BTreeMap<String, BTreeSet<String>>,
    /// For each attribute, the extension values with the namespace that declares each.
    pub domain_extensions: BTreeMap<String, BTreeSet<(String, String)>>,
    /// What each statement says about time, beside its contract.
    pub temporal: Vec<crate::reading::temporal::Obligation>,
    /// Each statement that yields to another one, with the statement that wins.
    pub priorities: Vec<crate::reading::priority::Priority>,
    /// For each statement that details others, the statements that it details.
    pub refined: BTreeMap<String, Vec<SpecRef>>,
    /// Each statement about terms or individuals whose axioms reach the
    /// atoms of other statements, with the statements that hold those atoms.
    pub applied: Vec<Applied>,
    /// The units in which each quantity is measured, stated or carried over
    /// a relation between quantities.
    pub quantity_units: BTreeMap<String, BTreeSet<String>>,
    /// The number of individuals of each carrier, when a statement relates individuals.
    pub instance_scope: Option<usize>,
    /// The relative clauses that restrict a noun phrase and that the reader
    /// read as the difference of a restricted class, as their keys spell them.
    pub read_clauses: BTreeSet<String>,
    /// The parts of each statement that no reading rule read.
    #[serde(skip)]
    pub unread: Vec<(SpecRef, crate::reading::key::Unread)>,
    /// The parts of each key of an action or of an event, by the text of the key.
    #[serde(skip)]
    pub keys: BTreeMap<String, Vec<crate::reading::key::Part>>,
    /// The reading over individuals of a set that declares the types of its
    /// individuals: the meaning of each typed statement and its instances.
    pub individuals: Option<crate::reading::ground::Individuals>,
}

/// How much a model holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Extent {
    /// The contracts that are no axioms.
    pub entries: usize,
    /// The atoms of the contracts and of the background.
    pub atoms: usize,
    /// The atoms that an axiom, a definition or the arithmetic constrains.
    pub constrained_atoms: usize,
}

impl Model {
    /// The entries and the atoms of this model, and how many of its atoms
    /// something constrains beyond the statement that holds them.
    pub fn extent(&self) -> Extent {
        let (mut atoms, mut constrained) = (BTreeSet::new(), BTreeSet::new());
        let mut entries = 0;
        for constraint in &self.constraints {
            let axiom = constraint.kind.is_axiom();
            entries += usize::from(!axiom);
            for formula in [&constraint.assume, &constraint.guarantee] {
                formula.atoms(true, &mut |atom, _| {
                    let name = atom.to_string();
                    if axiom || matches!(atom, Atom::Num { .. } | Atom::Lin { .. }) {
                        constrained.insert(name.clone());
                    }
                    atoms.insert(name);
                });
            }
        }
        for formula in &self.background {
            formula.atoms(true, &mut |atom, _| {
                constrained.insert(atom.to_string());
                atoms.insert(atom.to_string());
            });
        }
        Extent { entries, atoms: atoms.len(), constrained_atoms: constrained.len() }
    }

    /// Takes over what the keys of one statement left behind.
    pub(crate) fn absorb(&mut self, at: &SpecRef, sink: crate::reading::key::Sink) {
        self.unread.extend(sink.unread.into_iter().map(|unread| (at.clone(), unread)));
        for (name, parts) in sink.keys {
            self.keys.entry(name).or_insert(parts);
        }
    }
}

/// The words of a noun phrase, owner first: `the X of the API` reads as
/// `API X`, the same as `the API X`.
pub(super) fn np_words(np: &Np) -> Vec<String> {
    let mut words = np.of.as_ref().map(|of| np_words(of)).unwrap_or_default();
    // The owners of a coordinated `of` complement stand together before the head.
    for owner in &np.of_also {
        words.push(if np.of_conj == Some(Conj::And) { "and".to_string() } else { "or".to_string() });
        words.extend(np_words(owner));
    }
    words.extend(np.modifiers.iter().filter(|w| !is_article(w)).map(|w| strip_backticks(w).to_string()));
    words.push(strip_backticks(&np.head).to_string());
    if let Some(relative) = &np.relative {
        words.push(relative_text(relative));
    }
    words
}

fn relative_text(relative: &Relative) -> String {
    relative.render()
}

/// The name of one value of an enumeration or of a state.
pub(crate) fn value_name(value: &str, lex: &Lexicon) -> String {
    crate::reading::key::text(&crate::reading::key::word_parts(&[value.to_string()], crate::reading::key::Place::Value, lex))
}

pub fn np_key(np: &Np, lex: &Lexicon) -> String {
    let name = crate::reading::key::text(&crate::reading::key::np_parts(np, lex));
    lex.resolve(&name)
}

fn group_parts(group: &NpGroup) -> (Vec<&Np>, Option<Conj>) {
    match group {
        NpGroup::Single(np) => (vec![np], None),
        NpGroup::Coordinated { conj, items, .. } => (items.iter().collect(), Some(*conj)),
    }
}

/// Every noun phrase carried by a thematic role.
pub(super) fn role_nps(role: &RolePp) -> Vec<&Np> {
    if frequency(role).is_some() || crate::reading::temporal::is_time_role(role) {
        return Vec::new();
    }
    match role {
        RolePp::Recipient(g) | RolePp::Topic(g) | RolePp::Source(g) | RolePp::Agent(g) | RolePp::Goal(g) | RolePp::Means { np: g, .. } | RolePp::Location { np: g, .. } | RolePp::Other { np: g, .. } => group_parts(g).0,
        _ => Vec::new(),
    }
}

/// The share of a population in a verb phrase: the measure in percent and
/// the population after `of`.
pub(crate) fn proportion(vp: &Vp) -> Option<(&Measure, String)> {
    let at = vp.roles.iter().position(|role| matches!(role, RolePp::Duration(Measure::Quantity { unit: Some(u), .. } | Measure::Bounded { unit: Some(u), .. }) if u.eq_ignore_ascii_case("percent") || u == "%"))?;
    let RolePp::Duration(measure) = &vp.roles[at] else { return None };
    let RolePp::Other { preposition, np } = vp.roles.get(at + 1)? else { return None };
    if !preposition.eq_ignore_ascii_case("of") {
        return None;
    }
    let name = np.render();
    let name = name.strip_prefix("the ").or_else(|| name.strip_prefix("all ")).unwrap_or(&name).to_lowercase();
    Some((measure, name))
}

/// The sentence without the bound on a share: what the statement requires
/// of one activation.
pub(crate) fn without_share(sentence: &mut Sentence) {
    let Core::Deontic { vp: VpGroup::Single(vp), .. } = &mut sentence.core else { return };
    if proportion(vp).is_none() {
        return;
    }
    if let Some(at) = vp.roles.iter().position(|role| matches!(role, RolePp::Duration(m) if !is_time_measure(m))) {
        vp.roles.drain(at..(at + 2).min(vp.roles.len()));
    }
}

/// How often an action occurs in one activation: `at most 3 times`.
pub(crate) fn frequency(role: &RolePp) -> Option<(Cmp, i64)> {
    let RolePp::Other { preposition, np: NpGroup::Single(np) } = role else { return None };
    if np.head != "times" || np.det.is_some() || np.modifiers.len() != 1 {
        return None;
    }
    let cmp = match preposition.as_str() {
        "at most" => Cmp::Le,
        "at least" => Cmp::Ge,
        "exactly" => Cmp::Eq,
        _ => return None,
    };
    Some((cmp, np.modifiers[0].parse::<i64>().ok()?))
}

/// `true` for a role that says when the action happens, not what it is.
pub(crate) fn is_timing(role: &RolePp) -> bool {
    if frequency(role).is_some() || crate::reading::temporal::is_time_role(role) {
        return true;
    }
    match role {
        RolePp::Deadline(measure) | RolePp::Duration(measure) => is_time_measure(measure),
        RolePp::Before(_) | RolePp::After(_) | RolePp::Until(_) => true,
        RolePp::Other { preposition, np: NpGroup::Single(np) } => preposition == "after" && np_quantity(np).is_some(),
        _ => false,
    }
}

/// The action that a verb phrase names, without the words that say when it
/// happens: `eventually respond` and `respond within 5 seconds` name `respond`.
pub(crate) fn timeless(vp: &Vp) -> Vp {
    let mut plain = vp.clone();
    if plain.verb.eq_ignore_ascii_case("eventually") {
        if let Some(NpGroup::Single(np)) = &plain.object {
            if np.det.is_none() && np.of.is_none() && np.relative.is_none() {
                let mut words = np.modifiers.clone();
                words.push(np.head.clone());
                plain.verb = words.remove(0);
                plain.object = words.pop().map(|head| NpGroup::Single(Np { det: None, modifiers: words, head, of: None, relative: None, of_also: Vec::new(), of_conj: None }));
            }
        }
    }
    plain.manner.retain(|word| !crate::reading::temporal::is_time_manner(word));
    // The share of a population is a bound on a quantity, not a part of the action.
    if proportion(vp).is_some() {
        let at = plain.roles.iter().position(|role| matches!(role, RolePp::Duration(m) if !is_time_measure(m)));
        if let Some(at) = at {
            plain.roles.drain(at..(at + 2).min(plain.roles.len()));
        }
    }
    // `within 5 seconds of the last retry`: the phrase after the deadline
    // names where the time is measured from, not what the action is.
    if vp.roles.iter().any(|role| matches!(role, RolePp::Deadline(measure) if is_time_measure(measure))) {
        plain.roles.retain(|role| !matches!(role, RolePp::Other { preposition, .. } if preposition.eq_ignore_ascii_case("of")));
    }
    plain.roles.retain(|role| !is_timing(role));
    // `the same response for the same request` relates two runs: its two
    // `same` stay, so that the relation is reported and not read away.
    let render = plain.render().to_lowercase();
    let correlated = render.matches(" same ").count() + usize::from(render.starts_with("same ")) >= 2;
    if let Some(object) = &mut plain.object {
        general_group(object, correlated);
    }
    for role in &mut plain.roles {
        match role {
            RolePp::Recipient(g) | RolePp::Topic(g) | RolePp::Source(g) | RolePp::Agent(g) | RolePp::Goal(g) | RolePp::Means { np: g, .. } | RolePp::Location { np: g, .. } | RolePp::Other { np: g, .. } => general_group(g, correlated),
            _ => {}
        }
    }
    plain
}

/// An action on `each block`, on `every block` and on `the same block` is the
/// action on `the block`: the determiner says how many things the action
/// reaches, not which action it is.
fn general_group(group: &mut NpGroup, keep_same: bool) {
    match group {
        NpGroup::Single(np) => general_np(np, keep_same),
        NpGroup::Coordinated { items, .. } => items.iter_mut().for_each(|np| general_np(np, keep_same)),
    }
}

fn general_np(np: &mut Np, keep_same: bool) {
    // `all the files` are the files: the article goes with the determiner.
    if matches!(np.det, Some(Det::All)) && np.modifiers.first().is_some_and(|w| is_article(w)) {
        np.modifiers.remove(0);
    }
    if matches!(np.det, Some(Det::Each | Det::Every | Det::All | Det::Any)) {
        np.det = None;
    }
    if !keep_same && matches!(np.det, None | Some(Det::The)) && np.modifiers.first().is_some_and(|w| w.eq_ignore_ascii_case("same")) {
        np.modifiers.remove(0);
    }
    if let Some(of) = &mut np.of {
        general_np(of, keep_same);
    }
}

/// A class is named without the determiner that counts its members.
pub(crate) fn general_class(np: &mut Np) {
    general_np(np, false);
    if matches!(np.det, Some(Det::A | Det::An | Det::The | Det::No)) {
        np.det = None;
    }
}

pub(crate) fn action_key(subject: &str, vp: &Vp, lex: &Lexicon) -> String {
    let plain = timeless(vp);
    let name = crate::reading::key::action(subject, &plain, lex);
    name
}


fn parse_decimal(number: &str) -> Option<i64> {
    if let Some(n) = crate::syntax::words::number_word(number) {
        return Some(n as i64 * NUMERIC_SCALE);
    }
    let (int, frac) = number.split_once('.').unwrap_or((number, ""));
    if frac.len() > 3 {
        return None;
    }
    let scaled = int.parse::<i64>().ok()?.checked_mul(NUMERIC_SCALE)?;
    let padded = format!("{frac:0<3}");
    scaled.checked_add(padded.parse::<i64>().ok()?)
}

/// Reduces a unit to a base unit, so `1 minute` compares with `30 seconds`.
/// `within 5 seconds` is a time; `within the namespace` is a place.
pub(crate) fn is_time_measure(measure: &Measure) -> bool {
    match measure {
        Measure::Quantity { unit: Some(unit), .. } | Measure::Bounded { unit: Some(unit), .. } => canonical_unit(unit).1 == "ms",
        _ => false,
    }
}

fn canonical_unit(unit: &str) -> (i64, String) {
    let lower = unit.to_ascii_lowercase();
    let factor_of = |table: &[(&str, i64)]| table.iter().find(|(name, _)| *name == lower).map(|(_, f)| *f);
    const TIME: [(&str, i64); 18] = [("ms", 1), ("millisecond", 1), ("milliseconds", 1), ("s", 1000), ("sec", 1000), ("secs", 1000), ("second", 1000), ("seconds", 1000), ("min", 60_000), ("mins", 60_000), ("minute", 60_000), ("minutes", 60_000), ("h", 3_600_000), ("hour", 3_600_000), ("hours", 3_600_000), ("d", 86_400_000), ("day", 86_400_000), ("days", 86_400_000)];
    const SIZE: [(&str, i64); 10] = [("b", 1), ("byte", 1), ("bytes", 1), ("kb", 1000), ("mb", 1_000_000), ("gb", 1_000_000_000), ("kib", 1024), ("mib", 1_048_576), ("gib", 1_073_741_824), ("tb", 1_000_000_000_000)];
    if let Some(f) = factor_of(&TIME) {
        return (f, "ms".to_string());
    }
    if let Some(f) = factor_of(&SIZE) {
        return (f, "byte".to_string());
    }
    if lower == "%" || lower == "percent" {
        return (1, "percent".to_string());
    }
    let singular = lower.strip_suffix("ies").map(|h| format!("{h}y")).or_else(|| lower.strip_suffix('s').filter(|h| !h.is_empty()).map(str::to_string)).unwrap_or(lower);
    (1, singular)
}

fn measure_value(m: &Measure, default_unit: Option<&str>) -> Option<(i64, String)> {
    let Measure::Quantity { number, unit } = m else {
        return None;
    };
    let value = parse_decimal(number)?;
    let (factor, base) = canonical_unit(unit.as_deref().or(default_unit).unwrap_or(""));
    Some((value.checked_mul(factor)?, base))
}

/// One side of a comparison: a number with its unit, or a sum of quantities
/// over a common denominator.
enum Side {
    Number(i64, String),
    Sum(Vec<(String, i64)>, i64),
}

/// The quantities that a noun phrase adds up: `the limit`, `twice the limit`,
/// `half the limit`, `3 times the limit`, `the timeout plus the delay`,
/// `the limit minus the margin`. The second value is the common denominator.
/// `None` when the phrase is not such a sum.
pub(crate) fn linear_np(np: &Np, lex: &Lexicon) -> Option<(Vec<(String, i64)>, i64)> {
    if np.relative.is_some() {
        return None;
    }
    let mut words: Vec<&str> = np.modifiers.iter().map(String::as_str).collect();
    words.push(&np.head);
    let plain = !words.iter().any(|w| ["plus", "minus", "twice", "half", "times"].contains(&w.to_ascii_lowercase().as_str()));
    if plain {
        return Some((vec![(subject_key(np, lex), 1)], 1));
    }
    let mut segments: Vec<(i64, Vec<&str>)> = vec![(1, Vec::new())];
    for word in words {
        match word.to_ascii_lowercase().as_str() {
            "plus" => segments.push((1, Vec::new())),
            "minus" => segments.push((-1, Vec::new())),
            _ => segments.last_mut()?.1.push(word),
        }
    }
    let article = |w: &str| crate::syntax::words::is_article(w);
    let last = segments.len() - 1;
    let mut parts: Vec<(String, i64, i64)> = Vec::new();
    for (i, (sign, mut words)) in segments.into_iter().enumerate() {
        let (mut num, mut den) = (sign, 1);
        match words.first().map(|w| w.to_ascii_lowercase()).as_deref() {
            Some("twice") => {
                num *= 2;
                words.remove(0);
            }
            Some("half") => {
                den = 2;
                words.remove(0);
                if words.first().is_some_and(|w| w.eq_ignore_ascii_case("of")) {
                    words.remove(0);
                }
            }
            Some(first) if words.get(1).is_some_and(|w| w.eq_ignore_ascii_case("times")) => {
                let factor = parse_decimal(first)?;
                if factor % NUMERIC_SCALE != 0 {
                    return None;
                }
                num *= factor / NUMERIC_SCALE;
                words.drain(..2);
            }
            _ => {}
        }
        while words.first().is_some_and(|w| article(w)) {
            words.remove(0);
        }
        let head = words.pop()?;
        if head.eq_ignore_ascii_case("times") || words.iter().any(|w| w.eq_ignore_ascii_case("times")) {
            return None;
        }
        let part = Np { det: None, modifiers: words.iter().map(|w| w.to_string()).collect(), head: head.to_string(), of: if i == last { np.of.clone() } else { None }, relative: None, of_also: Vec::new(), of_conj: None };
        parts.push((np_key(&part, lex), num, den));
    }
    let denominator = parts.iter().map(|(_, _, den)| *den).max().unwrap_or(1);
    Some((parts.into_iter().map(|(key, num, den)| (key, num * (denominator / den))).collect(), denominator))
}

fn measure_side(m: &Measure, default_unit: Option<&str>, lex: &Lexicon) -> Option<Side> {
    if let Measure::Np { np } = m {
        let NpGroup::Single(np) = np.as_ref() else { return None };
        if let Some((n, unit)) = np_quantity(np) {
            return Some(Side::Number(n, unit));
        }
        return linear_np(np, lex).map(|(terms, den)| Side::Sum(terms, den));
    }
    measure_value(m, default_unit).map(|(n, unit)| Side::Number(n, unit))
}

/// `left cmp right` as one atom: a bound on one quantity when `left` is one
/// quantity and `right` is a number, and a relation between quantities otherwise.
fn relate_sides(left: &(Vec<(String, i64)>, i64), cmp: Cmp, right: &Side) -> Option<Formula> {
    let (terms, left_den) = left;
    match right {
        Side::Number(n, unit) => match terms.as_slice() {
            [(attr, 1)] if *left_den == 1 => Some(Formula::atom(Atom::Num { attr: attr.clone(), unit: unit.clone(), cmp, n: *n })),
            _ => Some(Formula::atom(Atom::Lin { terms: terms.clone(), unit: unit.clone(), cmp, n: n.checked_mul(*left_den)? })),
        },
        Side::Sum(other, right_den) => {
            // left / left_den cmp other / right_den, cleared of denominators.
            let mut all: BTreeMap<String, i64> = BTreeMap::new();
            for (attr, coef) in terms {
                *all.entry(attr.clone()).or_insert(0) += coef.checked_mul(*right_den)?;
            }
            for (attr, coef) in other {
                *all.entry(attr.clone()).or_insert(0) -= coef.checked_mul(*left_den)?;
            }
            all.retain(|_, coef| *coef != 0);
            if all.is_empty() {
                // `x` against `x`: true or false whatever `x` is.
                let holds = matches!(cmp, Cmp::Eq | Cmp::Ge | Cmp::Le);
                return Some(if holds { Formula::True } else { Formula::not(Formula::True) });
            }
            Some(Formula::atom(Atom::Lin { terms: all.into_iter().collect(), unit: String::new(), cmp, n: 0 }))
        }
    }
}

/// The numeric reading of a comparison. `None` leaves it opaque. `subject`
/// is the sum that the subject names when it names more than one quantity.
fn comparison_formula(attr: &str, subject: Option<(Vec<(String, i64)>, i64)>, c: &Comparison, lex: &Lexicon) -> Option<Formula> {
    // In `between 1 and 3 bytes` the unit is written only on the upper bound.
    let upper_unit = c.upper.as_ref().and_then(|m| match m {
        Measure::Quantity { unit, .. } => unit.as_deref(),
        _ => None,
    });
    let left = subject.unwrap_or_else(|| (vec![(attr.to_string(), 1)], 1));
    let value = measure_side(&c.value, upper_unit, lex)?;
    match bound_cmp(c.op) {
        Some(cmp) => relate_sides(&left, cmp, &value),
        None => {
            let upper = measure_side(c.upper.as_ref()?, None, lex)?;
            Some(Formula::And(vec![relate_sides(&left, Cmp::Ge, &value)?, relate_sides(&left, Cmp::Le, &upper)?]))
        }
    }
}

/// The sum that a subject names, when it names more than one quantity.
/// The bound that a comparison puts on one quantity.
pub(crate) fn comparison_bound(attr: &str, c: &Comparison, lex: &Lexicon) -> Option<Formula> {
    comparison_formula(attr, None, c, lex)
}

fn subject_sum(np: &Np, lex: &Lexicon) -> Option<(Vec<(String, i64)>, i64)> {
    linear_np(np, lex).filter(|(terms, den)| terms.len() > 1 || *den != 1 || terms.iter().any(|(_, coef)| *coef != 1))
}

/// The key of a subject. `a`, `the`, `each`, `every`, `all` and `any` all read
/// as the term itself, and `at least 1` as its plain existence. A bounded
/// quantifier is a different claim, so it stays in the key.
pub fn subject_key(np: &Np, lex: &Lexicon) -> String {
    let key = np_key(np, lex);
    match &np.det {
        Some(Det::AtLeast { n } | Det::Cardinal { n, .. }) if *n > 1 => format!("at least {n} {key}"),
        Some(Det::AtMost { n }) => format!("at most {n} {key}"),
        Some(Det::Exactly { n }) => format!("exactly {n} {key}"),
        _ => key,
    }
}

/// Past participles that do not end in `ed`, with their base forms.
const IRREGULAR_PARTICIPLES: [(&str, &str); 24] = [("sent", "send"), ("held", "hold"), ("taken", "take"), ("given", "give"), ("written", "write"), ("built", "build"), ("kept", "keep"), ("paid", "pay"), ("sold", "sell"), ("shown", "show"), ("seen", "see"), ("made", "make"), ("found", "find"), ("told", "tell"), ("known", "know"), ("lost", "lose"), ("put", "put"), ("set", "set"), ("run", "run"), ("read", "read"), ("begun", "begin"), ("done", "do"), ("shut", "shut"), ("spent", "spend")];

pub(crate) fn is_participle(word: &str) -> bool {
    word.chars().next().is_some_and(char::is_lowercase) && (word.ends_with("ed") || IRREGULAR_PARTICIPLES.iter().any(|(p, _)| *p == word))
}

/// The base form of a past participle, preferring a verb the specifications
/// use, so that `rejected` meets `reject` and `saved` meets `save`.
pub(crate) fn participle_base(word: &str, lex: &Lexicon) -> String {
    if let Some((_, base)) = IRREGULAR_PARTICIPLES.iter().find(|(p, _)| *p == word) {
        return (*base).to_string();
    }
    let Some(stem) = word.strip_suffix("ed") else { return word.to_string() };
    let mut candidates = vec![stem.to_string(), format!("{stem}e")];
    if let Some(y) = stem.strip_suffix('i') {
        candidates.push(format!("{y}y"));
    }
    let bytes = stem.as_bytes();
    if bytes.len() >= 2 && bytes[bytes.len() - 1] == bytes[bytes.len() - 2] {
        candidates.push(stem[..stem.len() - 1].to_string());
    }
    candidates.iter().find(|c| lex.verbs.contains(*c)).cloned().unwrap_or_else(|| stem.to_string())
}

/// The number and unit that open a noun phrase such as `85 degrees`.
fn np_quantity(np: &Np) -> Option<(i64, String)> {
    let mut words: Vec<&str> = np.modifiers.iter().map(String::as_str).collect();
    words.push(&np.head);
    // `85 degrees`: the cardinal before a unit is the number of the measure.
    if let Some(Det::Cardinal { word, .. }) = &np.det {
        words.insert(0, word);
    }
    let value = parse_decimal(words[0])?;
    // `3 times the limit` is a multiple of a quantity, not a number of `times`.
    if words.get(1).is_some_and(|w| w.eq_ignore_ascii_case("times")) {
        return None;
    }
    let (factor, unit) = canonical_unit(&words[1..].join(" "));
    Some((value.checked_mul(factor)?, unit))
}

/// Reads a verbal condition that states a bound: `the size exceeds 100`.
fn verbal_comparison(np: &Np, verb: &str, object: &Option<NpGroup>, roles: &[RolePp], lex: &Lexicon) -> Option<Formula> {
    let located = |wanted: &str| match roles {
        [RolePp::Location { preposition, np: NpGroup::Single(n) }] if preposition.eq_ignore_ascii_case(wanted) => Some(n),
        _ => None,
    };
    let (cmp, measure) = match (base_verb(verb).as_str(), object) {
        ("exceed" | "surpass", Some(NpGroup::Single(n))) => (Cmp::Gt, n),
        ("reach" | "hit", Some(NpGroup::Single(n))) => (Cmp::Ge, n),
        ("drop" | "fall" | "dip" | "go", None) if located("below").is_some() => (Cmp::Lt, located("below")?),
        ("rise" | "climb" | "go", None) if located("above").is_some() => (Cmp::Gt, located("above")?),
        _ => return None,
    };
    let left = linear_np(np, lex)?;
    if let Some((n, unit)) = np_quantity(measure) {
        return relate_sides(&left, cmp, &Side::Number(n, unit));
    }
    // `the timeout exceeds the limit`: a relation between two quantities.
    let (other, den) = linear_np(measure, lex)?;
    // `exceeds the limit by 5 seconds` states the difference itself.
    let by = match roles {
        [RolePp::Other { preposition, np: NpGroup::Single(amount) }] if preposition.eq_ignore_ascii_case("by") => Some(np_quantity(amount)?),
        _ => None,
    };
    match (by, cmp) {
        (Some((n, unit)), Cmp::Gt) if den == 1 && left.1 == 1 => {
            let mut terms = left.0.clone();
            terms.extend(other.iter().map(|(attr, coef)| (attr.clone(), -coef)));
            Some(Formula::atom(Atom::Lin { terms, unit, cmp: Cmp::Eq, n }))
        }
        (Some(_), _) => None,
        (None, _) => relate_sides(&left, cmp, &Side::Sum(other, den)),
    }
}

fn drop_general_det(np: &mut Np) -> bool {
    match np.det {
        Some(Det::No) => {
            np.det = None;
            true
        }
        Some(Det::AtMost { .. } | Det::Exactly { .. }) => false,
        Some(Det::AtLeast { n } | Det::Cardinal { n, .. }) if n > 1 => false,
        _ => {
            np.det = None;
            false
        }
    }
}

/// The key of a verbal condition, in one form whatever the determiner and the
/// inflection, and whether the condition is denied by `no`.
fn event_key(clause: &Clause, lex: &Lexicon) -> (String, bool) {
    let mut normal = clause.clone();
    let mut denied = match &mut normal.subject {
        NpGroup::Single(np) => drop_general_det(np),
        NpGroup::Coordinated { items, .. } => items.iter_mut().fold(false, |any, np| drop_general_det(np) || any),
    };
    if let ClauseBody::Verbal { verb, negation, .. } = &mut normal.body {
        let perfect = negation.as_deref().is_some_and(|n| n.starts_with("ha"));
        *verb = if perfect { participle_base(verb, lex) } else { base_verb(verb) };
        if negation.take().is_some() {
            denied = !denied;
        }
    }
    if let ClauseBody::Verbal { object, roles, .. } = &mut normal.body {
        if let Some(object) = object {
            general_group(object, false);
        }
        for role in roles.iter_mut() {
            match role {
                RolePp::Recipient(g) | RolePp::Topic(g) | RolePp::Source(g) | RolePp::Agent(g) | RolePp::Goal(g) | RolePp::Means { np: g, .. } | RolePp::Location { np: g, .. } | RolePp::Other { np: g, .. } => general_group(g, false),
                _ => {}
            }
        }
    }
    let mut parts = crate::reading::key::clause_parts(&normal, lex);
    let mut key = crate::reading::key::text(&parts);
    // An action and its event have one key: the subject is resolved as the
    // subject of an action is.
    if let NpGroup::Single(np) = &normal.subject {
        let name = crate::reading::key::np_parts(np, lex);
        let plain = crate::reading::key::text(&name);
        let resolved = lex.resolve(&plain);
        if resolved != plain && key.starts_with(&plain) && parts.starts_with(&name) {
            key = format!("{resolved}{}", &key[plain.len()..]);
            parts = crate::reading::key::with_resolved_subject(&parts, name.len(), &resolved);
        }
    }
    crate::reading::key::register_event(&key, &parts);
    (key, denied)
}

pub(crate) fn clause_formula(clause: &Clause, lex: &Lexicon) -> Formula {
    let (subjects, conj) = group_parts(&clause.subject);
    match &clause.body {
        ClauseBody::Copular { predicate, agent, roles, .. } => {
            let parts = subjects
                .iter()
                .map(|np| {
                    let attr = subject_key(np, lex);
                    let denied_subject = matches!(np.det, Some(Det::No));
                    if let Predicate::Comparison(c) = predicate {
                        if let Some(f) = comparison_formula(&attr, subject_sum(np, lex), c, lex) {
                            return if denied_subject { Formula::not(f) } else { f };
                        }
                    }
                    if let Predicate::Enumeration { conj, values, .. } = predicate {
                        let parts = values.iter().map(|v| Formula::atom(Atom::Val { attr: attr.clone(), value: value_name(v, lex) })).collect();
                        let listed = combine(Some(*conj), parts);
                        return if denied_subject { Formula::not(listed) } else { listed };
                    }
                    let (value, had_marker) = crate::reading::key::denied_value(crate::reading::key::value_parts(predicate, agent.as_ref(), roles, lex));
                    let negated = denied_subject ^ had_marker;
                    let atom = Formula::atom(Atom::Val { attr, value: crate::reading::key::text(&value) });
                    if negated {
                        Formula::not(atom)
                    } else {
                        atom
                    }
                })
                .collect();
            combine(conj, parts)
        }
        ClauseBody::Verbal { verb, object, roles, negation, .. } => {
            if let ([np], None) = (subjects.as_slice(), negation) {
                if let Some(bound) = verbal_comparison(np, verb, object, roles, lex) {
                    return if matches!(np.det, Some(Det::No)) { Formula::not(bound) } else { bound };
                }
            }
            // `exceeds` compares two quantities. Where the sides are no
            // quantities, the comparison has no reading as an event.
            if matches!(base_verb(verb).as_str(), "exceed" | "surpass") {
                crate::reading::key::unread_node(verb, "a comparison", "that is no relation between two quantities");
            }
            let (key, denied) = event_key(clause, lex);
            let event = Formula::atom(Atom::Event { key });
            if denied {
                Formula::not(event)
            } else {
                event
            }
        }
    }
}

pub fn group_formula(group: &ClauseGroup, lex: &Lexicon) -> Formula {
    combine(group.conj, group.items.iter().map(|c| clause_formula(c, lex)).collect())
}

/// A condition under its frame keyword. `Until X` holds while X does not, and
/// `Before X` is its own moment, distinct from X having happened.
pub(crate) fn frame_formula(keyword: &str, group: &ClauseGroup, lex: &Lexicon) -> Formula {
    match keyword.to_ascii_lowercase().as_str() {
        // A feature scope selects configurations: `Where the device includes a
        // cache` is a fact about the configuration, not something that occurs.
        "where" => group_formula(group, lex).map_atoms(&|atom| match atom {
            Atom::Event { key } => Atom::Config { key },
            other => other,
        }),
        "until" => Formula::not(group_formula(group, lex)),
        "before" => {
            let text: Vec<String> = group.items.iter().map(|clause| crate::reading::key::text(&crate::reading::key::clause_parts(clause, lex))).collect();
            Formula::atom(Atom::Event { key: format!("before {}", text.join(" and ")) })
        }
        _ => group_formula(group, lex),
    }
}

fn guard_formula(s: &Sentence, lex: &Lexicon) -> Formula {
    let mut parts: Vec<Formula> = s.frames.scopes.iter().chain(&s.frames.states).map(|f| frame_formula(&f.keyword, &f.clause, lex)).collect();
    if let Some(trigger) = &s.frames.trigger {
        parts.push(frame_formula(&trigger.keyword, &trigger.clause, lex));
    }
    if let Some(exception) = &s.exception {
        parts.push(Formula::not(clause_formula(exception, lex)));
    }
    match parts.len() {
        0 => Formula::True,
        1 => parts.remove(0),
        _ => Formula::And(parts),
    }
}

fn action_formula(modal: Modal, negated: bool, key: &str) -> Formula {
    let act = Formula::atom(Atom::Act { key: key.to_string() });
    let forbid = Formula::atom(Atom::Forbid { key: key.to_string() });
    let discouraged = Formula::atom(Atom::Discouraged { key: key.to_string() });
    match (modal, negated) {
        (Modal::Shall | Modal::Must, false) => Formula::And(vec![act, Formula::not(forbid), Formula::not(discouraged)]),
        (Modal::Shall | Modal::Must, true) => Formula::And(vec![Formula::not(act), forbid]),
        (Modal::Should, false) => Formula::And(vec![Formula::not(forbid), Formula::not(discouraged)]),
        // Advice against an action: weaker than a prohibition, but it does
        // conflict with an obligation or with advice to do the action.
        (Modal::Should, true) => discouraged,
        (Modal::May, false) => Formula::not(forbid),
        // The parser rejects `may not`.
        (Modal::May, true) => Formula::True,
    }
}

/// The active form of `shall be rejected by the API`: the agent, and the verb
/// phrase it performs on the subject.
pub(crate) fn active_voice(subject: &Np, vp: &Vp, lex: &Lexicon) -> Option<(String, Vp)> {
    if !vp.verb.eq_ignore_ascii_case("be") {
        return None;
    }
    let Some(Predicate::Words { words }) = &vp.complement else { return None };
    let [participle] = words.as_slice() else { return None };
    if !is_participle(participle) {
        return None;
    }
    let agent = vp.roles.iter().find_map(|r| match r {
        RolePp::Agent(NpGroup::Single(np)) => Some(np),
        _ => None,
    })?;
    let mut object = subject.clone();
    object.det = None;
    let roles = vp.roles.iter().filter(|r| !matches!(r, RolePp::Agent(_))).cloned().collect();
    Some((subject_key(agent, lex), Vp { verb: participle_base(participle, lex), particle: None, manner: vp.manner.clone(), object: Some(NpGroup::Single(object)), roles, complement: None, content: None }))
}

/// Reads `shall be Open` and `shall become Paid` as the state they require. A
/// bare participle is an action unless the specifications use it as a value:
/// `shall be logged` and `shall be rejected` do not exclude each other.
fn state_formula(attr: &str, vp: &Vp, universe: &BTreeMap<String, BTreeSet<String>>, lex: &Lexicon) -> Option<Formula> {
    if !vp.roles.is_empty() {
        return None;
    }
    let val = |value: &str| Formula::atom(Atom::Val { attr: attr.to_string(), value: value.to_string() });
    // A bare participle after `be` is the passive of its action, whatever
    // other statements hold: where they use it as a value of the subject,
    // the action establishes that value, and that is a relation between them.
    let _ = universe;
    let is_value = |value: &str| value == "closed" || !is_participle(value);
    if vp.verb.eq_ignore_ascii_case("become") {
        let Some(NpGroup::Single(np)) = &vp.object else { return None };
        return (np.det.is_none() && np.modifiers.is_empty() && np.of.is_none() && np.relative.is_none()).then(|| val(&value_name(&np.head, lex)));
    }
    if !vp.verb.eq_ignore_ascii_case("be") {
        return None;
    }
    match vp.complement.as_ref()? {
        Predicate::Comparison(c) => comparison_formula(attr, None, c, lex),
        Predicate::Words { words } => {
            let value = crate::reading::key::text(&crate::reading::key::predicate_word_parts(words, lex));
            is_value(&value).then(|| val(&value))
        }
        Predicate::Enumeration { conj, values, .. } => {
            let values: Vec<String> = values.iter().map(|v| value_name(v, lex)).collect();
            values.iter().all(|v| is_value(v)).then(|| combine(Some(*conj), values.iter().map(|v| val(v)).collect()))
        }
        _ => None,
    }
}

/// The noun phrases of a nominal predicate, each named with its owners
/// first, and the conjunction that joins them. `None` when the predicate is
/// no list of noun phrases that begin with an article.
pub(crate) fn predicate_nominals(text: &str) -> Option<(Vec<String>, Conj)> {
    let article = |w: &str| crate::syntax::words::is_article(w);
    let words: Vec<&str> = text.split_whitespace().collect();
    if !words.first().is_some_and(|w| article(w)) || text.contains('"') {
        return None;
    }
    let mut parts: Vec<Vec<&str>> = vec![Vec::new()];
    let mut conj = None;
    let mut i = 0;
    while i < words.len() {
        let word = words[i];
        let joins = (word == "or" || word == "and") && words.get(i + 1).is_some_and(|w| article(w));
        if joins {
            let found = if word == "or" { Conj::Or } else { Conj::And };
            if conj.is_some_and(|c| c != found) {
                return None;
            }
            conj = Some(found);
            parts.push(Vec::new());
        } else if let Some(stripped) = word.strip_suffix(',') {
            parts.last_mut()?.push(stripped);
            if words.get(i + 1).is_some_and(|w| article(w)) {
                parts.push(Vec::new());
            }
        } else {
            parts.last_mut()?.push(word);
        }
        i += 1;
    }
    let named: Vec<String> = parts
        .iter()
        .filter(|part| !part.is_empty())
        .map(|part| {
            // `the name of the owner of the room` is named `room owner name`.
            let mut links: Vec<Vec<&str>> = vec![Vec::new()];
            for word in part {
                if word.eq_ignore_ascii_case("of") {
                    links.push(Vec::new());
                } else if !article(word) {
                    links.last_mut().expect("a link").push(word);
                }
            }
            links.iter().rev().map(|link| link.join(" ")).collect::<Vec<_>>().join(" ")
        })
        .collect();
    let single_plain = named.len() == 1 && !text.split_whitespace().any(|w| w.eq_ignore_ascii_case("of"));
    if named.is_empty() || single_plain || named.iter().any(String::is_empty) {
        return None;
    }
    Some((named, conj.unwrap_or(Conj::And)))
}

fn bound_cmp(op: ComparisonOp) -> Option<Cmp> {
    match op {
        ComparisonOp::GreaterThan => Some(Cmp::Gt),
        ComparisonOp::LessThan => Some(Cmp::Lt),
        ComparisonOp::AtLeast => Some(Cmp::Ge),
        ComparisonOp::AtMost => Some(Cmp::Le),
        ComparisonOp::EqualTo => Some(Cmp::Eq),
        ComparisonOp::Between => None,
    }
}

/// The numeric limits an obligation states on its action.
fn action_bounds(key: &str, vp: &Vp) -> Vec<Formula> {
    let num = |suffix: &str, unit: String, cmp, n| Formula::atom(Atom::Num { attr: format!("{key} {suffix}"), unit, cmp, n });
    let mut out = Vec::new();
    // `for at least 99.9 percent of requests`: the share of a declared
    // population for which the action is as stated is one quantity.
    if let Some((measure, population)) = proportion(vp) {
        // What is bounded for that share stays with the share: `within 200
        // ms for 99.9 percent of requests` says nothing about the other requests.
        let qualified: Vec<String> = vp.roles.iter().filter(|role| is_timing(role)).map(RolePp::render).collect();
        let share = if qualified.is_empty() { format!("{key} share of {population}") } else { format!("{key} {} share of {population}", qualified.join(" ")) };
        let percent = |number: &String| parse_decimal(number);
        match measure {
            Measure::Quantity { number, .. } => out.extend(percent(number).map(|n| Formula::atom(Atom::Num { attr: share.clone(), unit: "percent".to_string(), cmp: Cmp::Ge, n }))),
            Measure::Bounded { op, number, upper, .. } => match (bound_cmp(*op), upper) {
                (Some(cmp), _) => out.extend(percent(number).map(|n| Formula::atom(Atom::Num { attr: share.clone(), unit: "percent".to_string(), cmp, n }))),
                (None, Some(upper)) => {
                    out.extend(percent(number).map(|n| Formula::atom(Atom::Num { attr: share.clone(), unit: "percent".to_string(), cmp: Cmp::Ge, n })));
                    out.extend(percent(upper).map(|n| Formula::atom(Atom::Num { attr: share.clone(), unit: "percent".to_string(), cmp: Cmp::Le, n })));
                }
                (None, None) => {}
            },
            _ => {}
        }
        return out;
    }
    let percent = |m: &Measure| matches!(m, Measure::Quantity { unit: Some(u), .. } | Measure::Bounded { unit: Some(u), .. } if u.eq_ignore_ascii_case("percent") || u == "%");
    for role in &vp.roles {
        // A share is read above; it is no duration.
        if matches!(role, RolePp::Duration(m) if percent(m)) {
            continue;
        }
        // The occurrences of the action in one activation are one quantity.
        if let Some((cmp, n)) = frequency(role) {
            out.push(num("occurrences", "times".to_string(), cmp, n * NUMERIC_SCALE));
            continue;
        }
        match role {
            // A deadline and a delay measure one quantity: the time from the
            // activation to the completion of the action.
            RolePp::Deadline(m) => out.extend(measure_value(m, None).map(|(n, unit)| num("elapsed", unit, Cmp::Le, n))),
            RolePp::Duration(m @ Measure::Quantity { .. }) => out.extend(measure_value(m, None).map(|(n, unit)| num("duration", unit, Cmp::Eq, n))),
            RolePp::Duration(Measure::Bounded { op, number, unit, upper }) => {
                let plain = |number: &String| measure_value(&Measure::Quantity { number: number.clone(), unit: unit.clone() }, None);
                match (bound_cmp(*op), upper) {
                    (Some(cmp), _) => out.extend(plain(number).map(|(n, u)| num("duration", u, cmp, n))),
                    (None, Some(upper)) => {
                        out.extend(plain(number).map(|(n, u)| num("duration", u, Cmp::Ge, n)));
                        out.extend(plain(upper).map(|(n, u)| num("duration", u, Cmp::Le, n)));
                    }
                    (None, None) => {}
                }
            }
            RolePp::Other { preposition, np: NpGroup::Single(np) } => {
                let (suffix, cmp) = match preposition.as_str() {
                    "after" => ("elapsed", Cmp::Eq),
                    "up-to" => ("limit", Cmp::Le),
                    // `at least 2 seconds after the first failure`: a bound
                    // on the time from the named origin to the completion.
                    "at least" | "at most" | "exactly" if crate::reading::temporal::is_time_role(role) => ("elapsed", if preposition == "at least" { Cmp::Ge } else if preposition == "at most" { Cmp::Le } else { Cmp::Eq }),
                    _ => continue,
                };
                out.extend(np_quantity(np).map(|(n, unit)| num(suffix, unit, cmp, n)));
            }
            _ => {}
        }
    }
    // `at most 1 step for each step name` counts the steps of one name: it
    // bounds no total, and the reading over individuals holds the count.
    let per_thing = vp.roles.iter().any(|role| role_nps(role).iter().any(|np| matches!(np.det, Some(Det::Each | Det::Every)) || np.modifiers.iter().any(|m| m.eq_ignore_ascii_case("same"))));
    if let (Some(NpGroup::Single(object)), false) = (&vp.object, per_thing) {
        let bound = match object.det {
            Some(Det::AtLeast { n } | Det::Cardinal { n, .. }) => Some((Cmp::Ge, n)),
            Some(Det::AtMost { n }) => Some((Cmp::Le, n)),
            Some(Det::Exactly { n }) => Some((Cmp::Eq, n)),
            Some(Det::OneOrMore) => Some((Cmp::Ge, 1)),
            _ => None,
        };
        if let Some((cmp, n)) = bound {
            out.push(num("count", "count".to_string(), cmp, n as i64 * NUMERIC_SCALE));
        }
    }
    out
}

/// The same action without its circumstances: an obligation to do something
/// in some way is an obligation to do it.
fn base_action(vp: &Vp) -> Vp {
    let mut base = vp.clone();
    base.roles.clear();
    base.manner.clear();
    if let Some(NpGroup::Single(object)) = &mut base.object {
        if matches!(object.det, Some(Det::AtLeast { .. } | Det::Cardinal { .. } | Det::AtMost { .. } | Det::Exactly { .. } | Det::ZeroOrMore | Det::OneOrMore)) {
            object.det = None;
        }
    }
    base
}

/// The formula of one verb phrase of an obligation, prohibition, advice or permission.
fn item_formula(subject: &Np, item: &Vp, modal: Modal, negated: bool, universe: &BTreeMap<String, BTreeSet<String>>, lex: &Lexicon) -> Formula {
    // `support A, B, and C` is one action for each object, as coordinated
    // verbs are one action for each verb.
    if let Some((objects, conj)) = coordinated_objects(item) {
        let parts = objects.into_iter().map(|one| item_formula(subject, &one, modal, negated, universe, lex)).collect();
        // Only a required action leaves a choice between alternatives: a
        // prohibition, advice or a permission reaches each object.
        let choice = conj == Conj::Or && !negated && matches!(modal, Modal::Shall | Modal::Must);
        return combine(Some(if choice { Conj::Or } else { Conj::And }), parts);
    }
    // `accept no connections` denies the action.
    let mut item = item.clone();
    let denied_object = match &mut item.object {
        Some(NpGroup::Single(object)) if matches!(object.det, Some(Det::No)) => {
            object.det = None;
            true
        }
        _ => false,
    };
    let negated = negated ^ denied_object;
    let (actor, item) = active_voice(subject, &item, lex).unwrap_or_else(|| (subject_key(subject, lex), item));
    let binding = matches!(modal, Modal::Shall | Modal::Must);
    if binding {
        if let Some(state) = state_formula(&actor, &item, universe, lex) {
            return if negated { Formula::not(state) } else { state };
        }
    }
    // `shall not respond within 2 seconds` denies the timing, not the action.
    if binding && negated && timeless(&item) != item {
        let key = action_key(&actor, &item, lex);
        let bounds = action_bounds(&action_key(&actor, &base_action(&item), lex), &item);
        if !bounds.is_empty() {
            return Formula::implies(Formula::atom(Atom::Act { key }), Formula::not(Formula::And(bounds)));
        }
    }
    let mut parts = vec![action_formula(modal, negated, &action_key(&actor, &item, lex))];
    if binding && !negated {
        let base = base_action(&item);
        let base_key = action_key(&actor, &base, lex);
        if base != item {
            parts.push(Formula::atom(Atom::Act { key: base_key.clone() }));
            parts.push(Formula::not(Formula::atom(Atom::Forbid { key: base_key.clone() })));
        }
        parts.extend(action_bounds(&base_key, &item));
        // `shall enter safe mode` puts the subject in safe mode.
        if item.verb.eq_ignore_ascii_case("enter") {
            if let Some(object) = item.object.iter().find_map(single_np) {
                parts.push(Formula::atom(Atom::Val { attr: actor.clone(), value: format!("in {}", np_key(object, lex)) }));
            }
        }
    }
    combine(None, parts)
}

/// The verb phrase once for each object of a coordinated object, with the
/// conjunction that joins them.
fn coordinated_objects(item: &Vp) -> Option<(Vec<Vp>, Conj)> {
    let Some(NpGroup::Coordinated { conj, items, .. }) = &item.object else { return coordinated_role(item) };
    let each = items
        .iter()
        .map(|np| {
            let mut one = item.clone();
            one.object = Some(NpGroup::Single(np.clone()));
            one
        })
        .collect();
    Some((each, *conj))
}

/// The noun phrases of a role phrase that names things, with the place to
/// put one of them back. A role of time or of rate names no thing.
fn role_group(role: &mut RolePp) -> Option<&mut NpGroup> {
    match role {
        RolePp::Recipient(np) | RolePp::Topic(np) | RolePp::Source(np) | RolePp::Goal(np) | RolePp::Agent(np) => Some(np),
        RolePp::Means { np, .. } => Some(np),
        // `between A and B` and `among A and B` name one place by two things.
        RolePp::Location { preposition, np } | RolePp::Other { preposition, np } => (!["between", "among"].contains(&preposition.to_lowercase().as_str())).then_some(np),
        RolePp::Deadline(_) | RolePp::Duration(_) | RolePp::Rate { .. } | RolePp::Before(_) | RolePp::After(_) | RolePp::Until(_) => None,
    }
}

/// The verb phrase once for each noun phrase of its first coordinated role:
/// `rest on a declaration, a definition, or a stated relation` is one action
/// for each thing that the role names, joined as the role joins them.
fn coordinated_role(item: &Vp) -> Option<(Vec<Vp>, Conj)> {
    let mut probe = item.clone();
    let (index, conj, items) = probe.roles.iter_mut().enumerate().find_map(|(index, role)| match role_group(role)? {
        NpGroup::Coordinated { conj, items, .. } => Some((index, *conj, items.clone())),
        NpGroup::Single(_) => None,
    })?;
    let each = items
        .into_iter()
        .map(|np| {
            let mut one = item.clone();
            if let Some(group) = role_group(&mut one.roles[index]) {
                *group = NpGroup::Single(np);
            }
            one
        })
        .collect();
    Some((each, conj))
}

fn exists_formula(np: &Np, lex: &Lexicon) -> Formula {
    Formula::atom(Atom::Event { key: format!("exists {}", np_key(np, lex)) })
}

/// What a relation says of one instance of its subject.
fn relation_item(subject: &Np, item: &Vp, lex: &Lexicon) -> Formula {
    if let Some((objects, conj)) = coordinated_objects(item) {
        return combine(Some(conj), objects.iter().map(|one| relation_item(subject, one, lex)).collect());
    }
    let actor = subject_key(subject, lex);
    let denied = matches!(item.object.as_ref().and_then(single_np).and_then(|o| o.det.as_ref()), Some(Det::No));
    // `belongs to exactly one namespace` has no object: its role phrases say what holds.
    let base = if item.object.is_none() && !item.roles.is_empty() { item.clone() } else { base_action(item) };
    let mut base_without_no = base.clone();
    if let Some(NpGroup::Single(object)) = &mut base_without_no.object {
        if matches!(object.det, Some(Det::No)) {
            object.det = None;
        }
    }
    // `belongs to exactly one namespace`: the count of a relation without an
    // object stands in its one role phrase, and bounds the relation as the
    // count of an object does.
    let mut role_count = None;
    if item.object.is_none() {
        if let [RolePp::Recipient(NpGroup::Single(np)) | RolePp::Source(NpGroup::Single(np)) | RolePp::Goal(NpGroup::Single(np)) | RolePp::Topic(NpGroup::Single(np)) | RolePp::Location { np: NpGroup::Single(np), .. } | RolePp::Other { np: NpGroup::Single(np), .. }] = base_without_no.roles.as_mut_slice() {
            role_count = match np.det {
                Some(Det::AtLeast { n } | Det::Cardinal { n, .. }) => Some((Cmp::Ge, n)),
                Some(Det::AtMost { n }) => Some((Cmp::Le, n)),
                Some(Det::Exactly { n }) => Some((Cmp::Eq, n)),
                Some(Det::OneOrMore) => Some((Cmp::Ge, 1)),
                _ => None,
            };
            if role_count.is_some() {
                np.det = None;
            }
        }
    }
    let key = action_key(&actor, &base_without_no, lex);
    if denied {
        return Formula::not(Formula::atom(Atom::Act { key }));
    }
    if matches!(item.object.as_ref().and_then(single_np).and_then(|o| o.det.as_ref()), Some(Det::ZeroOrMore)) {
        return Formula::True;
    }
    let mut parts = vec![Formula::atom(Atom::Act { key: key.clone() })];
    parts.extend(action_bounds(&key, item));
    if let Some((cmp, n)) = role_count {
        parts.push(Formula::atom(Atom::Num { attr: format!("{key} count"), unit: "count".to_string(), cmp, n: n as i64 * NUMERIC_SCALE }));
    }
    combine(None, parts)
}

/// Reads a composition as the pattern of behavior it requires.
struct Composer<'a> {
    subject: &'a Np,
    composition: &'a Composition,
    universe: &'a BTreeMap<String, BTreeSet<String>>,
    lex: &'a Lexicon,
    /// Keeps the reachability of one statement's flow apart from another's.
    scope: &'a str,
}

impl Composer<'_> {
    fn key(&self, index: usize) -> String {
        let vp = &self.composition.leaves[index];
        let (actor, item) = active_voice(self.subject, vp, self.lex).unwrap_or_else(|| (subject_key(self.subject, self.lex), vp.clone()));
        action_key(&actor, &item, self.lex)
    }

    fn leaves(&self, node: &CompNode, out: &mut Vec<usize>) {
        match node {
            CompNode::Leaf { index, .. } => out.push(*index),
            CompNode::All { items } | CompNode::Some { items } | CompNode::One { items } | CompNode::Sequence { items } => items.iter().for_each(|item| self.leaves(item, out)),
            CompNode::Flow(flow) => flow.steps.iter().for_each(|step| self.leaves(&step.node, out)),
        }
    }

    fn acts(&self, node: &CompNode) -> Formula {
        let mut found = Vec::new();
        self.leaves(node, &mut found);
        Formula::And(found.into_iter().map(|i| Formula::atom(Atom::Act { key: self.key(i) })).collect())
    }

    fn sequence(&self, items: &[&CompNode]) -> Formula {
        let mut parts: Vec<Formula> = items.iter().map(|item| self.node(item)).collect();
        parts.extend(items.windows(2).flat_map(|pair| self.order(pair[0], pair[1])));
        Formula::And(parts)
    }

    /// Each action of `first` completes before any action of `second` starts.
    fn order(&self, first: &CompNode, second: &CompNode) -> Vec<Formula> {
        let (mut before, mut after) = (Vec::new(), Vec::new());
        self.leaves(first, &mut before);
        self.leaves(second, &mut after);
        before.iter().flat_map(|a| after.iter().map(move |b| (*a, *b))).map(|(a, b)| Formula::atom(Atom::Before { first: self.key(a), second: self.key(b) })).collect()
    }

    fn reach(&self, step: &str) -> Formula {
        Formula::atom(Atom::Event { key: format!("reach {step} in {}", self.scope) })
    }

    fn flow(&self, flow: &Flow) -> Formula {
        let step_node = |name: &str| flow.steps.iter().find(|s| s.name == name).map(|s| &s.node);
        if flow.choices.is_empty() {
            let mut path = vec![flow.start.as_str()];
            while let Some((_, next)) = path.last().and_then(|at| flow.edges.iter().find(|(from, _)| from == at)) {
                if path.contains(&next.as_str()) {
                    break;
                }
                path.push(next);
            }
            let nodes: Vec<&CompNode> = path.iter().filter_map(|name| step_node(name)).collect();
            return self.sequence(&nodes);
        }
        let mut parts = vec![self.reach(&flow.start)];
        // A step is designated exactly when some path selects it.
        let mut incoming: BTreeMap<&str, Vec<Formula>> = BTreeMap::new();
        for step in &flow.steps {
            parts.push(Formula::implies(self.reach(&step.name), self.node(&step.node)));
        }
        for (from, to) in &flow.edges {
            parts.push(Formula::implies(self.reach(from), self.reach(to)));
            if let (Some(a), Some(b)) = (step_node(from), step_node(to)) {
                parts.extend(self.order(a, b).into_iter().map(|before| Formula::implies(self.reach(from), before)));
            }
            incoming.entry(to).or_default().push(self.reach(from));
        }
        for choice in &flow.choices {
            let mut none_taken = vec![self.reach(&choice.after)];
            for (guard, target) in &choice.arms {
                let guard = group_formula(guard, self.lex);
                let taken = Formula::And(vec![self.reach(&choice.after), guard.clone()]);
                parts.push(Formula::implies(taken.clone(), self.reach(target)));
                incoming.entry(target).or_default().push(taken);
                none_taken.push(Formula::not(guard));
            }
            if let Some(target) = &choice.otherwise {
                let taken = Formula::And(none_taken);
                parts.push(Formula::implies(taken.clone(), self.reach(target)));
                incoming.entry(target).or_default().push(taken);
            }
        }
        for step in &flow.steps {
            if step.name != flow.start {
                let sources = incoming.remove(step.name.as_str()).unwrap_or_default();
                parts.push(Formula::implies(self.reach(&step.name), Formula::Or(sources)));
            }
        }
        Formula::And(parts)
    }

    fn node(&self, node: &CompNode) -> Formula {
        match node {
            CompNode::Leaf { index, exception } => {
                let action = item_formula(self.subject, &self.composition.leaves[*index], Modal::Shall, false, self.universe, self.lex);
                match exception {
                    Some(clause) => Formula::Or(vec![clause_formula(clause, self.lex), action]),
                    None => action,
                }
            }
            CompNode::All { items } => Formula::And(items.iter().map(|item| self.node(item)).collect()),
            CompNode::Some { items } => Formula::Or(items.iter().map(|item| self.node(item)).collect()),
            CompNode::One { items } => {
                let chosen = items.iter().enumerate().map(|(i, item)| {
                    let mut parts = vec![self.node(item)];
                    parts.extend(items.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, other)| Formula::not(self.acts(other))));
                    Formula::And(parts)
                });
                Formula::Or(chosen.collect())
            }
            CompNode::Sequence { items } => self.sequence(&items.iter().collect::<Vec<_>>()),
            CompNode::Flow(flow) => self.flow(flow),
        }
    }

    /// The action that a pattern is as a whole, and what forbids it: an
    /// item of a list that holds as a whole, or every alternative of a
    /// choice. `None` for a flow, whose paths are not listed here.
    fn whole(&self, node: &CompNode) -> Option<(String, Formula)> {
        let of = |kind: &'static str, items: &[CompNode], all: bool| {
            let parts: Vec<(String, Formula)> = items.iter().map(|item| self.whole(item)).collect::<Option<_>>()?;
            let actor = subject_key(self.subject, self.lex);
            let names: Vec<String> = parts.iter().map(|(name, _)| name.split_once('|').map_or(name.clone(), |(_, action)| action.to_string())).collect();
            let blocked: Vec<Formula> = parts.into_iter().map(|(_, blocked)| blocked).collect();
            Some((crate::reading::key::composed(&actor, kind, &names), if all { Formula::Or(blocked) } else { Formula::And(blocked) }))
        };
        match node {
            CompNode::Leaf { index, exception: None } => {
                let key = self.key(*index);
                Some((key.clone(), Formula::atom(Atom::Forbid { key })))
            }
            // An item with an exception may be left out: nothing forbids the whole through it.
            CompNode::Leaf { exception: Some(_), .. } => None,
            CompNode::All { items } => of("all of", items, true),
            CompNode::Sequence { items } => of("in order", items, true),
            CompNode::Some { items } => of("one or more of", items, false),
            CompNode::One { items } => of("exactly one of", items, false),
            CompNode::Flow(_) => None,
        }
    }

    /// The modal applies outside the whole pattern.
    fn formula(&self, modal: Modal, negated: bool) -> Formula {
        let mut found = Vec::new();
        self.leaves(&self.composition.root, &mut found);
        // A permission for a composed response is one permission of the
        // response as a whole. What forbids a part that the whole needs
        // forbids the whole; the permission of the whole permits no part alone.
        if let (Modal::May, false, Some((whole, blocked))) = (modal, negated, self.whole(&self.composition.root)) {
            if !matches!(self.composition.root, CompNode::Leaf { .. }) {
                let forbidden = Formula::atom(Atom::Forbid { key: whole });
                return Formula::And(vec![Formula::not(forbidden.clone()), Formula::implies(blocked, forbidden)]);
            }
        }
        match (modal, negated) {
            (Modal::Shall | Modal::Must, false) => self.node(&self.composition.root),
            (Modal::Shall | Modal::Must, true) => Formula::not(self.node(&self.composition.root)),
            (modal, negated) => Formula::And(found.into_iter().map(|i| item_formula(self.subject, &self.composition.leaves[i], modal, negated, self.universe, self.lex)).collect()),
        }
    }
}

fn core_formula(core: &Core, scope: &str, guarded: bool, universe: &BTreeMap<String, BTreeSet<String>>, lex: &Lexicon) -> Option<Formula> {
    match core {
        Core::Definition { .. } => None,
        Core::Conjoined { items } => Some(Formula::And(items.iter().filter_map(|item| core_formula(item, scope, guarded, universe, lex)).collect())),
        Core::Existence { subject } => Some(Formula::And(group_parts(subject).0.into_iter().map(|np| exists_formula(np, lex)).collect())),
        Core::Relation { subject, vp } => {
            // `The timeout exceeds the retry interval.` relates two quantities.
            if let (NpGroup::Single(np), VpGroup::Single(item)) = (subject, vp) {
                if let Some(bound) = verbal_comparison(np, &item.verb, &item.object, &item.roles, lex) {
                    return Some(bound);
                }
            }
            let parts = group_parts(subject).0.into_iter().map(|np| {
                // `No user sends a message.` denies the action of every such
                // subject, under the name that an obligation gives the action.
                // `No two rooms have the same name.` denies a pair: it says
                // nothing of one room alone, and the reading over individuals
                // tells the rooms apart. A pair of things that belong to an
                // owner, or a pair without `the same`, has no reading.
                if matches!(np.det, Some(Det::No)) && np.modifiers.first().is_some_and(|m| m.eq_ignore_ascii_case("two")) {
                    let shared = match vp {
                        VpGroup::Single(item) => matches!(&item.object, Some(NpGroup::Single(object)) if object.modifiers.iter().any(|m| m.eq_ignore_ascii_case("same")) && object.of.is_none() && object.relative.is_none()),
                        _ => false,
                    };
                    if !shared || np.of.is_some() || np.relative.is_some() {
                        crate::reading::key::unread_node("no two", "a denial of a pair", "that does not have the form `No two rooms have the same name.`: for the things of an owner, bound their number, as in `Each flow has at most 1 step for each step name.`");
                    }
                    return Formula::True;
                }
                if matches!(np.det, Some(Det::No)) {
                    let mut plain = np.clone();
                    plain.det = None;
                    let actor = subject_key(&plain, lex);
                    return Formula::And(vp.items().iter().map(|item| {
                        let mut base = base_action(&timeless(item));
                        base.verb = base_verb(&base.verb);
                        Formula::not(Formula::atom(Atom::Act { key: action_key(&actor, &base, lex) }))
                    }).collect());
                }
                // `Some room has no owner.` speaks about one individual, and
                // the representative of the type is not that individual: of
                // the type the sentence claims that such a thing exists.
                // What it says of the individual is read over individuals.
                if matches!(np.det, Some(Det::Some)) {
                    return exists_formula(np, lex);
                }
                let held = Formula::And(vp.items().iter().map(|item| relation_item(np, item, lex)).collect());
                // `The checker reports the diagnostic.` names its subject: the
                // statement speaks of that thing, as a rule about `the checker`
                // does. A universal subject asserts no instance, and its
                // relation constrains what exists.
                if matches!(np.det, Some(Det::The)) && np.relative.is_none() {
                    return held;
                }
                Formula::implies(exists_formula(np, lex), held)
            });
            Some(Formula::And(parts.collect()))
        }
        Core::Description { subject, adverb, predicate, agent, roles, .. } => {
            let negated = *adverb == Some(DescriptionAdverb::Never);
            let (subjects, conj) = group_parts(subject);
            let parts = subjects
                .iter()
                .map(|np| {
                    // `No member is the owner` denies the claim of every member.
                    let negated = negated ^ matches!(np.det, Some(Det::No));
                    let attr = subject_key(np, lex);
                    let atom_of = |value: &str| {
                        let (attr, value) = (attr.clone(), value.to_string());
                        if guarded {
                            Atom::Val { attr, value }
                        } else {
                            Atom::Dom { attr, value }
                        }
                    };
                    let flip = |f: Formula| if negated { Formula::not(f) } else { f };
                    if let Predicate::Comparison(c) = predicate {
                        if let Some(f) = comparison_formula(&attr, subject_sum(np, lex), c, lex) {
                            return flip(f);
                        }
                    }
                    if let Predicate::Enumeration { values, conj: joined, .. } = predicate {
                        let normalized: Vec<String> = values.iter().map(|v| value_name(v, lex)).collect();
                        // `No specification is both consistent and inconsistent`
                        // denies that one thing is both; `is A or B` denied
                        // denies each.
                        if negated && *joined == Conj::And {
                            return Formula::not(Formula::And(normalized.iter().map(|v| Formula::atom(atom_of(v))).collect()));
                        }
                        if negated {
                            return Formula::And(normalized.iter().map(|v| Formula::not(Formula::atom(atom_of(v)))).collect());
                        }
                        if guarded {
                            return Formula::Or(normalized.iter().map(|v| Formula::atom(atom_of(v))).collect());
                        }
                        // An enumeration declares the whole domain: nothing else belongs to it.
                        let mut parts: Vec<Formula> = normalized.iter().map(|v| Formula::atom(atom_of(v))).collect();
                        if let Some(all) = universe.get(&attr) {
                            parts.extend(all.iter().filter(|v| !normalized.contains(v)).map(|v| Formula::not(Formula::atom(atom_of(v)))));
                        }
                        // And it says what it says: the subject is one of the
                        // listed values, at each moment. Without this the
                        // prohibitions of each value were consistent.
                        parts.push(Formula::Or(normalized.iter().map(|v| Formula::atom(Atom::Val { attr: attr.clone(), value: v.clone() })).collect()));
                        return Formula::And(parts);
                    }
                    // `is a document of the trion language`, `is a verb phrase or a
                    // nested action list`: each noun phrase of the predicate is
                    // named as that noun phrase is named elsewhere.
                    if let (Predicate::Words { .. }, None, true) = (predicate, agent, roles.is_empty()) {
                        if let Some((nominals, conj)) = predicate_nominals(&predicate.render()) {
                            let parts: Vec<Formula> = nominals.iter().map(|n| Formula::atom(atom_of(&crate::reading::key::text(&crate::reading::key::predicate_word_parts(&split_words(n), lex))))).collect();
                            return flip(combine(Some(conj), parts));
                        }
                    }
                    flip(Formula::atom(atom_of(&crate::reading::key::text(&crate::reading::key::value_parts(predicate, agent.as_ref(), roles, lex)))))
                })
                .collect();
            Some(combine(conj, parts))
        }
        Core::Deontic { subject, modal, negated, vp } => {
            let (subjects, conj) = group_parts(subject);
            let parts = subjects
                .iter()
                .map(|np| {
                    // `No client shall X` denies X of every client.
                    let negated = *negated || matches!(np.det, Some(Det::No));
                    if let VpGroup::Composite(composition) = vp {
                        return Composer { subject: np, composition, universe, lex, scope }.formula(*modal, negated);
                    }
                    let polarity = |i: usize| match vp {
                        VpGroup::All { negated: each, .. } => each[i] || matches!(np.det, Some(Det::No)),
                        _ => negated,
                    };
                    let formulas: Vec<Formula> = vp.items().iter().enumerate().map(|(i, item)| item_formula(np, item, *modal, polarity(i), universe, lex)).collect();
                    // Alternatives are a choice only when the action is required.
                    let is_choice = matches!(vp, VpGroup::Alternatives { .. }) && matches!(modal, Modal::Shall | Modal::Must) && !negated;
                    combine(if is_choice { Some(Conj::Or) } else { Some(Conj::And) }, formulas)
                })
                .collect();
            // `A, B, or C shall not X` denies X of each of them.
            let conj = if *negated && conj == Some(Conj::Or) { Some(Conj::And) } else { conj };
            Some(combine(conj, parts))
        }
    }
}

/// The guarantee of a sentence. A definition establishes vocabulary and
/// guarantees nothing.
fn claim_formula(s: &Sentence, universe: &BTreeMap<String, BTreeSet<String>>, lex: &Lexicon) -> Option<Formula> {
    let guarded = !s.frames.is_empty() || s.exception.is_some() || s.iff.is_some() || s.necessary.is_some();
    // What a necessary condition says of a claim where the condition fails.
    // Of an action it is the prohibition of the action (advice against it
    // under `should`): `shall stop only when the door is open` forbids
    // stopping while the door is not open. The claim itself implying the
    // condition would say less: a required action is one that completes
    // and is not forbidden, so a completion that is marked forbidden would
    // satisfy the implication without the condition. Of a state it is that
    // the state does not hold.
    let outside = |core: &Core, cond: &Formula| -> Option<Formula> {
        if let Core::Deontic { subject, modal, negated: false, vp } = core {
            let vp = match vp {
                VpGroup::All { items, negated } => VpGroup::All { items: items.clone(), negated: vec![true; negated.len()] },
                other => other.clone(),
            };
            let modal = if matches!(modal, Modal::Should) { Modal::Should } else { Modal::Shall };
            let denied = core_formula(&Core::Deontic { subject: subject.clone(), modal, negated: true, vp }, &s.source, guarded, universe, lex)?;
            return Some(Formula::Or(vec![cond.clone(), denied]));
        }
        Some(Formula::implies(core_formula(core, &s.source, guarded, universe, lex)?, cond.clone()))
    };
    if let Some(cond) = &s.iff {
        let claim = core_formula(&s.core, &s.source, guarded, universe, lex)?;
        let cond = group_formula(cond, lex);
        return Some(Formula::And(vec![Formula::implies(cond.clone(), claim), outside(&s.core, &cond)?]));
    }
    if let Some(cond) = &s.necessary {
        let cond = group_formula(cond, lex);
        // In `shall A and shall be B only when C` the condition belongs to B.
        if let Core::Deontic { subject, modal, negated, vp: VpGroup::All { items, negated: polarity } } = &s.core {
            if let (Some((last, first)), Some((last_negated, first_negated))) = (items.split_last(), polarity.split_last()) {
                let core_of = |vp: VpGroup| Core::Deontic { subject: subject.clone(), modal: *modal, negated: *negated, vp };
                let opening = core_formula(&core_of(VpGroup::All { items: first.to_vec(), negated: first_negated.to_vec() }), &s.source, guarded, universe, lex)?;
                let closing = outside(&core_of(VpGroup::All { items: vec![last.clone()], negated: vec![*last_negated] }), &cond)?;
                return Some(Formula::And(vec![opening, closing]));
            }
        }
        return outside(&s.core, &cond);
    }
    core_formula(&s.core, &s.source, guarded, universe, lex)
}

/// Matches pattern words against actual words. A `$variable` takes one word,
/// and a final `$variable` takes all the remaining words.
fn match_words(pattern: &[String], actual: &[String], bound: &mut BTreeMap<String, String>) -> bool {
    let tail_variable = pattern.last().is_some_and(|w| w.starts_with('$'));
    if pattern.len() > actual.len() || (pattern.len() < actual.len() && !tail_variable) {
        return false;
    }
    for (i, p) in pattern.iter().enumerate() {
        let is_last = i + 1 == pattern.len();
        let value = if is_last { actual[i..].join(" ") } else { actual[i].clone() };
        if p.starts_with('$') {
            if bound.get(p).is_some_and(|existing| existing != &value) {
                return false;
            }
            bound.insert(p.clone(), value);
        } else if p != &value {
            return false;
        }
    }
    true
}

fn single_np(group: &NpGroup) -> Option<&Np> {
    match group {
        NpGroup::Single(np) => Some(np),
        NpGroup::Coordinated { .. } => None,
    }
}

fn is_wildcard_verb(vp: &Vp) -> bool {
    vp.verb.starts_with('$')
}

fn match_vp(pattern: &Vp, actual: &Vp, bound: &mut BTreeMap<String, String>) -> bool {
    if is_wildcard_verb(pattern) {
        bound.insert(pattern.verb.clone(), actual.render());
        return true;
    }
    let objects = match (&pattern.object, &actual.object) {
        (Some(p), Some(a)) => match (single_np(p), single_np(a)) {
            (Some(p), Some(a)) => match_words(&np_words(p), &np_words(a), bound),
            _ => false,
        },
        (None, None) => true,
        _ => false,
    };
    pattern.verb == actual.verb && pattern.particle == actual.particle && objects && pattern.roles.len() == actual.roles.len() && pattern.roles.iter().zip(&actual.roles).all(|(p, a)| p.render() == a.render())
}

/// Every way a sentence pattern matches a core. Coordinated subjects and
/// alternatives are checked item by item, so coordination cannot hide one.
pub fn match_core(pattern: &Core, actual: &Core) -> Vec<BTreeMap<String, String>> {
    let mut all = Vec::new();
    match (pattern, actual) {
        (Core::Deontic { subject: ps, vp: pv, .. }, Core::Deontic { subject: asub, vp: av, .. }) => {
            let (Some(ps), Some(pvp)) = (single_np(ps), pv.single()) else {
                return all;
            };
            for np in group_parts(asub).0 {
                for item in av.items() {
                    let mut bound = BTreeMap::new();
                    if match_words(&np_words(ps), &np_words(np), &mut bound) && match_vp(pvp, item, &mut bound) {
                        all.push(bound);
                    }
                }
            }
        }
        (Core::Description { subject: ps, predicate: pp, .. }, Core::Description { subject: asub, predicate: ap, .. }) => {
            let Some(ps) = single_np(ps) else {
                return all;
            };
            for np in group_parts(asub).0 {
                let mut bound = BTreeMap::new();
                if match_words(&np_words(ps), &np_words(np), &mut bound) && match_words(&split_words(&pp.render()), &split_words(&ap.render()), &mut bound) {
                    all.push(bound);
                }
            }
        }
        _ => {}
    }
    all
}

/// Matches a wildcard-verb pattern against the subjects of a sentence's
/// conditions, so a name used only in a condition is still checked.
fn match_clauses(pattern: &Core, s: &Sentence) -> Vec<BTreeMap<String, String>> {
    let Core::Deontic { subject, vp, .. } = pattern else {
        return Vec::new();
    };
    let (Some(ps), Some(pvp)) = (single_np(subject), vp.single()) else {
        return Vec::new();
    };
    if !is_wildcard_verb(pvp) {
        return Vec::new();
    }
    let groups = s.frames.scopes.iter().chain(&s.frames.states).map(|f| &f.clause).chain(s.frames.trigger.iter().map(|t| &t.clause));
    let clauses = groups.flat_map(|g| &g.items).chain(s.exception.iter());
    let mut all = Vec::new();
    for clause in clauses {
        for np in group_parts(&clause.subject).0 {
            let mut bound = BTreeMap::new();
            if match_words(&np_words(ps), &np_words(np), &mut bound) {
                all.push(bound);
            }
        }
    }
    all
}

fn split_words(text: &str) -> Vec<String> {
    text.split_whitespace().map(str::to_string).collect()
}

pub const SUBJECT_VARIABLE: &str = "$subject";

struct RoleInfo<'a> {
    qualified: String,
    role: &'a Role,
}

/// The namespace name that prefixes a document's roles.
pub fn role_prefix<'a>(package: &'a str, namespace: &'a str) -> &'a str {
    if namespace.is_empty() {
        package
    } else {
        namespace
    }
}

fn collect_roles(set: &SpecSet) -> Vec<RoleInfo<'_>> {
    set.packages
        .iter()
        .flat_map(|pkg| pkg.documents.iter().flat_map(move |doc| doc.roles.iter().map(move |role| RoleInfo { qualified: format!("{}.{}", role_prefix(&pkg.name, &doc.namespace), role.name), role })))
        .collect()
}

/// Every value mentioned for each attribute across the specification set.
/// The values that the statements name, attribute by attribute. `of_the_domain`
/// tells the instances whose claim is a relation or a kind of the domain:
/// their predicate names no value.
fn value_universe(set: &SpecSet, lex: &Lexicon, of_the_domain: &dyn Fn(&str) -> bool, of_a_share: &dyn Fn(&str) -> bool) -> BTreeMap<String, BTreeSet<String>> {
    let empty = BTreeMap::new();
    let mut universe: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (pkg, doc) in set.packages.iter().flat_map(|p| p.documents.iter().map(move |d| (p, d))) {
        let lex = lex.in_document(doc);
        for spec in &doc.specs {
            let display = if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) };
            // A bound on a share names no state of one thing: its conditions select a population.
            if of_a_share(&display) {
                continue;
            }
            let guard = guard_formula(&spec.sentence, &lex);
            let claim = if of_the_domain(&display) { None } else { claim_formula(&spec.sentence, &empty, &lex) };
            for f in std::iter::once(&guard).chain(claim.iter()) {
                f.atoms(true, &mut |a, _| {
                    if let Atom::Dom { attr, value } | Atom::Val { attr, value } = a {
                        universe.entry(attr.clone()).or_default().insert(value.clone());
                    }
                });
            }
        }
    }
    universe
}

fn background(universe: &BTreeMap<String, BTreeSet<String>>) -> Vec<Formula> {
    let mut out = Vec::new();
    for (attr, values) in universe {
        let vals: Vec<&String> = values.iter().collect();
        for (i, v) in vals.iter().enumerate() {
            let val = Formula::atom(Atom::Val { attr: attr.clone(), value: (*v).clone() });
            out.push(Formula::implies(val.clone(), Formula::atom(Atom::Dom { attr: attr.clone(), value: (*v).clone() })));
            for w in &vals[i + 1..] {
                let other = Formula::atom(Atom::Val { attr: attr.clone(), value: (*w).clone() });
                out.push(Formula::not(Formula::And(vec![val.clone(), other])));
            }
        }
    }
    out
}

fn compiled(pattern: &str) -> Option<Regex> {
    Regex::new(pattern).ok()
}

/// Composes the whole specification set into one model.
/// Gives each relation between quantities the unit of its quantities. A
/// quantity gets its unit from a bound that states one, and a relation
/// carries the unit from one of its quantities to the others. A relation
/// between quantities of different units keeps no unit, and is reported.
fn resolve_units(model: &mut Model) {
    let mut units: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut relations: Vec<(Vec<String>, String)> = Vec::new();
    {
        let mut visit = |a: &Atom, _: bool| match a {
            Atom::Num { attr, unit, .. } => {
                units.entry(attr.clone()).or_default().insert(unit.clone());
            }
            Atom::Lin { terms, unit, .. } => relations.push((terms.iter().map(|(attr, _)| attr.clone()).collect(), unit.clone())),
            _ => {}
        };
        for c in &model.constraints {
            c.assume.atoms(true, &mut visit);
            c.guarantee.atoms(true, &mut visit);
        }
    }
    if relations.is_empty() {
        return;
    }
    loop {
        let mut changed = false;
        for (attrs, stated) in &relations {
            let mut known: BTreeSet<String> = attrs.iter().filter_map(|a| units.get(a)).flatten().cloned().collect();
            if !stated.is_empty() {
                known.insert(stated.clone());
            }
            if known.len() != 1 {
                continue;
            }
            for attr in attrs {
                let entry = units.entry(attr.clone()).or_default();
                if entry.is_empty() {
                    entry.extend(known.iter().cloned());
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    let unit_of = |atom: Atom| match atom {
        Atom::Lin { terms, unit, cmp, n } => {
            let mut known: BTreeSet<&String> = terms.iter().filter_map(|(attr, _)| units.get(attr)).flatten().collect();
            if !unit.is_empty() {
                known.insert(&unit);
            }
            let unit = if known.len() == 1 { known.into_iter().next().cloned().unwrap_or_default() } else { String::new() };
            Atom::Lin { terms, unit, cmp, n }
        }
        other => other,
    };
    for c in &mut model.constraints {
        c.assume = std::mem::replace(&mut c.assume, Formula::True).map_atoms(&unit_of);
        c.guarantee = std::mem::replace(&mut c.guarantee, Formula::True).map_atoms(&unit_of);
    }
    model.quantity_units = units;
}

/// The measures of one action are related: the action lasts from its start
/// to its completion, and its completion is no earlier than its start, so
/// its duration is at most the time from its activation to its completion.
/// No measure is negative.
fn measure_axioms(model: &mut Model) {
    let mut measures: BTreeMap<String, BTreeMap<&'static str, String>> = BTreeMap::new();
    {
        let mut note = |attr: &String, unit: &String| {
            for suffix in ["elapsed", "duration"] {
                if let Some(action) = attr.strip_suffix(suffix).and_then(|a| a.strip_suffix(' ')).filter(|a| a.contains('|')) {
                    measures.entry(action.to_string()).or_default().insert(suffix, unit.clone());
                }
            }
        };
        let mut visit = |a: &Atom, _: bool| match a {
            Atom::Num { attr, unit, .. } => note(attr, unit),
            Atom::Lin { terms, unit, .. } => terms.iter().for_each(|(attr, _)| note(attr, unit)),
            _ => {}
        };
        for c in &model.constraints {
            c.assume.atoms(true, &mut visit);
            c.guarantee.atoms(true, &mut visit);
        }
    }
    let mut shares: BTreeSet<String> = BTreeSet::new();
    for c in &model.constraints {
        let mut visit = |a: &Atom, _: bool| {
            if let Atom::Num { attr, unit, .. } = a {
                if unit == "percent" && attr.contains(" share of ") {
                    shares.insert(attr.clone());
                }
            }
        };
        c.assume.atoms(true, &mut visit);
        c.guarantee.atoms(true, &mut visit);
    }
    // The shares of one action in one population are shares of one set of
    // cases. A case in which the action completes within 200 ms is a case
    // in which it completes within 500 ms, and a case in which it completes
    // within a deadline is a case in which it completes: the cases of the
    // smaller deadline are among those of the larger one, so their share is
    // no greater. Only a deadline tells two shares of one action apart
    // here; a share with any other qualification is related to none.
    let mut by_cases: BTreeMap<(String, String), Vec<(Option<i64>, String)>> = BTreeMap::new();
    for share in &shares {
        let Some((cases, population)) = share.rsplit_once(" share of ") else { continue };
        let (action, deadline) = match cases.rsplit_once(" within ") {
            Some((action, bound)) => {
                let words: Vec<&str> = bound.split(' ').collect();
                let [number, unit] = words.as_slice() else { continue };
                let (factor, base) = canonical_unit(unit);
                let Some(time) = parse_decimal(number).filter(|_| base == "ms").and_then(|n| n.checked_mul(factor)) else { continue };
                (action, Some(time))
            }
            None => (cases, None),
        };
        by_cases.entry((action.to_string(), population.to_string())).or_default().push((deadline, share.clone()));
    }
    for mut related in by_cases.into_values() {
        // No deadline is the largest one: every completion is within it.
        related.sort_by_key(|(deadline, _)| deadline.map_or((1, 0), |time| (0, time)));
        for pair in related.windows(2) {
            model.background.push(Formula::atom(Atom::difference(&pair[1].1, &pair[0].1, "percent", Cmp::Ge, 0)));
        }
    }
    for share in shares {
        model.background.push(Formula::atom(Atom::Num { attr: share.clone(), unit: "percent".to_string(), cmp: Cmp::Ge, n: 0 }));
        model.background.push(Formula::atom(Atom::Num { attr: share, unit: "percent".to_string(), cmp: Cmp::Le, n: 100 * NUMERIC_SCALE }));
    }
    for (action, found) in measures {
        for (suffix, unit) in &found {
            model.background.push(Formula::atom(Atom::Num { attr: format!("{action} {suffix}"), unit: unit.clone(), cmp: Cmp::Ge, n: 0 }));
        }
        if let (Some(elapsed), Some(duration)) = (found.get("elapsed"), found.get("duration")) {
            if elapsed == duration {
                model.background.push(Formula::atom(Atom::Lin { terms: vec![(format!("{action} duration"), 1), (format!("{action} elapsed"), -1)], unit: elapsed.clone(), cmp: Cmp::Le, n: 0 }));
            }
        }
    }
}

/// The conjuncts that `full` holds beyond `local`, where the two are one
/// formula read with and without the values that other statements name.
fn beyond(full: &Formula, local: &Formula) -> Vec<Formula> {
    if full == local {
        return Vec::new();
    }
    match (full, local) {
        (Formula::And(all), Formula::And(own)) if all.len() == own.len() => all.iter().zip(own).flat_map(|(a, b)| beyond(a, b)).collect(),
        (Formula::And(all), Formula::And(own)) if all.len() > own.len() && all[..own.len()] == own[..] => all[own.len()..].to_vec(),
        (Formula::And(all), own) if all.first() == Some(own) => all[1..].to_vec(),
        _ => vec![full.clone()],
    }
}

/// Adds what statements say about the atoms of other statements: a carried
/// constraint for each, and the relation to the statements that hold those
/// atoms.
pub(crate) fn carry_to_others(model: &mut Model, carried: Vec<(SpecRef, Formula, Vec<Formula>)>) {
    if carried.is_empty() {
        return;
    }
    let about = |a: &Atom| match a {
        Atom::Val { attr, value } | Atom::Dom { attr, value } => format!("value {attr} = {value}"),
        Atom::Act { key } | Atom::Forbid { key } | Atom::Discouraged { key } => format!("action {key}"),
        other => other.to_string(),
    };
    let mut owners: BTreeMap<String, Vec<SpecRef>> = BTreeMap::new();
    for c in &model.constraints {
        let Some(at) = c.refs.first() else { continue };
        let mut visit = |a: &Atom, _: bool| {
            let known = owners.entry(about(a)).or_default();
            if !known.iter().any(|k| k.id == at.id) {
                known.push(at.clone());
            }
        };
        c.assume.atoms(true, &mut visit);
        c.guarantee.atoms(true, &mut visit);
    }
    let mut grouped: Vec<(SpecRef, Formula, Vec<Formula>)> = Vec::new();
    for (at, assume, formulas) in carried {
        match grouped.iter_mut().find(|(known, guard, _)| known.id == at.id && *guard == assume) {
            Some((_, _, all)) => all.extend(formulas),
            None => grouped.push((at, assume, formulas)),
        }
    }
    for (at, assume, mut formulas) in grouped {
        let mut rests_on: Vec<SpecRef> = Vec::new();
        for formula in &formulas {
            formula.atoms(true, &mut |a: &Atom, _: bool| {
                for owner in owners.get(&about(a)).into_iter().flatten() {
                    if owner.id != at.id && !rests_on.iter().any(|r| r.id == owner.id) {
                        rests_on.push(owner.clone());
                    }
                }
            });
        }
        rests_on.sort_by(|a, b| a.id.cmp(&b.id));
        match model.applied.iter_mut().find(|a| a.kind == "applied" && a.subject.id == at.id) {
            Some(known) => {
                for r in rests_on {
                    if !known.rests_on.iter().any(|k| k.id == r.id) {
                        known.rests_on.push(r);
                    }
                }
                known.rests_on.sort_by(|a, b| a.id.cmp(&b.id));
            }
            None => model.applied.push(Applied { kind: "applied".to_string(), subject: at.clone(), rests_on }),
        }
        let guarantee = if formulas.len() == 1 { formulas.remove(0) } else { Formula::And(formulas) };
        model.constraints.push(Constraint { kind: ConstraintKind::Carried, assume, guarantee, refs: vec![at] });
    }
}

/// What a statement claims, as its sentence states it: the guarantee of its
/// contract, under the condition of the contract. What a declaration of
/// individuals makes of a statement is said beside its contract, as what
/// follows from this claim over the declared individuals.
pub(super) fn claim_of(model: &Model, id: &str) -> Option<Formula> {
    let contract = model.constraints.iter().find(|c| matches!(c.kind, ConstraintKind::Spec | ConstraintKind::Permission) && c.refs.first().is_some_and(|at| at.id == id))?;
    Some(if contract.assume == Formula::True { contract.guarantee.clone() } else { Formula::And(vec![contract.assume.clone(), contract.guarantee.clone()]) })
}

/// The atoms in which two formulas of one shape differ, pairwise, or
/// nothing when the formulas have different shapes.
fn renamed_atoms(plain: &Formula, named: &Formula, out: &mut BTreeSet<(Atom, Atom)>) -> bool {
    match (plain, named) {
        (Formula::True, Formula::True) => true,
        (Formula::Atom(a), Formula::Atom(b)) => {
            if a != b {
                out.insert((a.clone(), b.clone()));
            }
            true
        }
        (Formula::Not(a), Formula::Not(b)) => renamed_atoms(a, b, out),
        (Formula::And(a), Formula::And(b)) | (Formula::Or(a), Formula::Or(b)) => a.len() == b.len() && a.iter().zip(b).all(|(a, b)| renamed_atoms(a, b, out)),
        (Formula::Implies(a, c), Formula::Implies(b, d)) => renamed_atoms(a, b, out) && renamed_atoms(c, d, out),
        _ => false,
    }
}

/// What a sentence is read as: the kind of its contract, the condition
/// under which it holds, what it claims, and its temporal shape.
pub struct Reading {
    pub kind: ConstraintKind,
    pub condition: Formula,
    /// Nothing when the sentence states no claim that a contract holds.
    pub claim: Option<Formula>,
    pub temporal: Vec<crate::reading::temporal::Obligation>,
    /// `true` when the sentence bounds a share of its activations.
    pub bounds_a_share: bool,
}

/// Reads one sentence as its contract. The reading is a function of the
/// sentence, of the branch of a shared context that holds it, and of the
/// names that the lexicon gives its terms: no other statement and no
/// declaration of a set takes part in it.
pub fn read_sentence(sentence: &Sentence, otherwise: bool, reference: &SpecRef, lex: &Lexicon) -> Reading {
    let alone: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    // A bound on a share speaks about the activations as a whole: its
    // contract is the bound on the quantity of the share, under no
    // condition of a moment.
    if matches!(&sentence.core, Core::Deontic { vp, .. } if vp.items().iter().any(|vp| proportion(vp).is_some())) {
        let mut bounds: Vec<Formula> = Vec::new();
        if let Some(claim) = claim_formula(sentence, &alone, lex) {
            claim.atoms(true, &mut |atom, positive| {
                let about_a_share = match atom {
                    Atom::Num { attr, .. } => attr.contains(" share of "),
                    Atom::Lin { terms, .. } => terms.iter().all(|(attr, _)| attr.contains(" share of ")),
                    _ => false,
                };
                if about_a_share {
                    let bound = Formula::atom(atom.clone());
                    bounds.push(if positive { bound } else { Formula::not(bound) });
                }
            });
        }
        return Reading { kind: ConstraintKind::Spec, condition: Formula::True, claim: Some(Formula::And(bounds)), temporal: Vec::new(), bounds_a_share: true };
    }
    let temporal = crate::reading::temporal::obligation(sentence, otherwise, reference.clone(), lex).into_iter().collect();
    let guard = guard_formula(sentence, lex);
    let condition = if otherwise { Formula::not(guard) } else { guard };
    let kind = if matches!(sentence.core, Core::Deontic { modal: Modal::May, .. }) { ConstraintKind::Permission } else { ConstraintKind::Spec };
    Reading { kind, condition, claim: claim_formula(sentence, &alone, lex), temporal, bounds_a_share: false }
}

/// Compiles a specification set; `scope` is the number of individuals of each
/// carrier that the statements about individuals are read over.
///
/// The sentences are read without the aliases of the set: the contracts of
/// a sentence follow from the sentence alone. An alias says that two names
/// name one term, and that is said beside the contracts: for each atom that
/// an alias renames, the background holds that the atom and the renamed
/// atom stand together.
pub fn compile(set: &SpecSet, lex: &Lexicon, scope: usize) -> Model {
    let mut model = compile_with(set, &lex.without_aliases(), scope);
    if !lex.has_aliases() {
        return model;
    }
    // The same sentences with the aliases applied: where a contract differs
    // from the contract of its sentence, it differs in the names of atoms.
    let named = compile_with(set, lex, scope);
    let mut renamed: BTreeSet<(Atom, Atom)> = BTreeSet::new();
    let mut seen: BTreeMap<(String, String), usize> = BTreeMap::new();
    for constraint in &model.constraints {
        let Some(at) = constraint.refs.first() else { continue };
        // The contracts of one statement and one kind are paired in their order.
        let key = (format!("{:?}", constraint.kind), at.id.clone());
        let nth = seen.entry(key).or_default();
        let other = named.constraints.iter().filter(|other| other.kind == constraint.kind && other.refs.first().is_some_and(|r| r.id == at.id)).nth(*nth);
        *nth += 1;
        if let Some(other) = other {
            if renamed_atoms(&constraint.assume, &other.assume, &mut renamed) {
                renamed_atoms(&constraint.guarantee, &other.guarantee, &mut renamed);
            }
        }
    }
    for (plain, alias) in renamed {
        let (plain, alias) = (Formula::atom(plain), Formula::atom(alias));
        model.background.push(Formula::And(vec![Formula::implies(plain.clone(), alias.clone()), Formula::implies(alias, plain)]));
    }
    // What the statements say of each other under one name of a term: the
    // values that a statement closes for an attribute, and what one
    // statement carries to another. It stands beside the contracts, over
    // the names that the aliases give, and the equivalences above join it
    // to the contracts.
    for axiom in named.background {
        if !model.background.contains(&axiom) {
            model.background.push(axiom);
        }
    }
    for carried in named.constraints.into_iter().filter(|constraint| constraint.kind == ConstraintKind::Carried) {
        if !model.constraints.contains(&carried) {
            model.constraints.push(carried);
        }
    }
    model
}

/// Compiles a specification set with the names that a lexicon gives.
fn compile_with(set: &SpecSet, lex: &Lexicon, scope: usize) -> Model {
    // A set that declares the types of its individuals is read over them:
    // each statement about a declared type stands for its instances.
    let grounded = crate::reading::ground::apply(set, lex, scope);
    // The set with each statement about declared types replaced by its
    // instances. A statement about the domain of the types stays in it: it
    // is a sentence, and it is read as its sentence states it.
    let set = grounded.as_ref().map_or(set, |g| &g.with_domain);
    let universe = value_universe(set, lex, &|id| grounded.as_ref().is_some_and(|g| g.claims.contains_key(id)), &|id| grounded.as_ref().is_some_and(|g| g.shares.contains(id)));
    let roles = collect_roles(set);
    let mut model = Model { background: background(&universe), ..Default::default() };
    let mut denied_values: Vec<(String, String)> = Vec::new();
    // An enumeration leaves out what is extended: an extension is declared to
    // lie outside the original whole without contradicting it.
    let mut extended: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let scoped = lex.in_document(doc);
        for extension in &doc.extensions {
            let attr = scoped.resolve(&scoped.canon(&extension.attr));
            for value in &extension.values {
                let value = scoped.canon(value);
                extended.entry(attr.clone()).or_default().insert(value.clone());
                model.domain_extensions.entry(attr.clone()).or_default().insert((value, doc.namespace.clone()));
            }
        }
    }
    let alone: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut carried: Vec<(SpecRef, Formula, Vec<Formula>)> = Vec::new();
    let mut closing = universe.clone();
    for (attr, values) in &extended {
        if let Some(known) = closing.get_mut(attr) {
            known.retain(|v| !values.contains(v));
        }
    }

    // What a role makes of a statement that activates it, beside the contract.
    let mut carried_roles: Vec<Constraint> = Vec::new();
    let mut accounted: Option<SpecRef> = None;
    // What each atom of an instance says of a concrete behaviour.
    let mut atoms: Vec<crate::reading::ground::AtomOf> = Vec::new();
    let mut shares: Vec<crate::reading::ground::ShareOf> = Vec::new();
    for pkg in &set.packages {
        for doc in &pkg.documents {
            let lex = &lex.in_document(doc);
            for binding in &doc.bindings {
                model.constraints.push(Constraint {
                    kind: ConstraintKind::Binding,
                    assume: Formula::True,
                    guarantee: Formula::atom(Atom::Role { subject: lex.resolve(&lex.canon(&binding.term)), role: binding.role.clone() }),
                    refs: vec![SpecRef { id: format!("{}:{}", binding.file, binding.line), file: binding.file.clone(), line: binding.line, text: binding.text.clone() }],
                });
            }
            for (spec, sentence) in doc.specs.iter().flat_map(|spec| crate::expand::formalized(spec).into_iter().map(move |sentence| (spec, sentence))) {
                let sentence = &sentence;
                for frame in sentence.frames.scopes.iter().filter(|f| f.keyword.eq_ignore_ascii_case("where")) {
                    frame_formula(&frame.keyword, &frame.clause, lex).atoms(true, &mut |atom, _| {
                        if let Atom::Val { attr, .. } = atom {
                            model.configured.insert(attr.clone());
                        }
                    });
                }
                let display = if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) };
                let reference = SpecRef { id: display, file: spec.file.clone(), line: spec.line, text: sentence.source.clone() };
                if let Some(at) = accounted.replace(reference.clone()) {
                    model.absorb(&at, crate::reading::key::end());
                }
                crate::reading::key::begin();
                // The contract of a sentence is read from the sentence and
                // from the names of its terms.
                let read = read_sentence(sentence, spec.otherwise, &reference, lex);
                // A bound on a share speaks about the activations as a whole:
                // its contract is the bound on the quantity of the share.
                if read.bounds_a_share {
                    let guarantee = read.claim.unwrap_or(Formula::And(Vec::new()));
                    guarantee.atoms(true, &mut |atom, _| {
                        for quantity in atom.symbols() {
                            let entry = crate::reading::ground::ShareOf { quantity: quantity.to_string(), statement: reference.id.clone() };
                            if !shares.contains(&entry) {
                                shares.push(entry);
                            }
                        }
                    });
                    model.constraints.push(Constraint { kind: read.kind, assume: read.condition, guarantee, refs: vec![reference.clone()] });
                    continue;
                }
                model.temporal.extend(read.temporal);
                let guard = read.condition;
                guard.atoms(true, &mut |a, positive| {
                    if let Atom::Val { attr, value } = a {
                        if positive {
                            model.guarded_values.entry(attr.clone()).or_default().insert(value.clone());
                        } else {
                            denied_values.push((attr.clone(), value.clone()));
                        }
                    }
                });
                // `No request is both accepted and rejected.` excludes two actions and lists no values.
                let denied = matches!(&sentence.core, Core::Description { subject: NpGroup::Single(np), .. } if matches!(np.det, Some(Det::No)));
                if let (Core::Description { subject: NpGroup::Single(np), predicate: Predicate::Enumeration { values, .. }, adverb: None, .. }, true, false) = (&sentence.core, guard == Formula::True, denied) {
                    model.closed_domains.entry(np_key(np, lex)).or_default().extend(values.iter().map(|v| value_name(v, lex)));
                }

                // What the statement says alone. An enumeration also excludes the
                // values that other statements name: that part is carried to them.
                let of_the_domain = grounded.as_ref().and_then(|g| g.claims.get(&reference.id));
                let Some(claim) = of_the_domain.cloned().or(read.claim) else { continue };
                if let (None, Some(closed)) = (of_the_domain, claim_formula(sentence, &closing, lex)) {
                    let extra = beyond(&closed, &claim);
                    if !extra.is_empty() {
                        carried.push((reference.clone(), guard.clone(), extra));
                    }
                }
                // An instance whose response chooses an individual requires
                // one of its alternatives, each of an individual that may
                // be chosen: of the kind, and in the relations, that the
                // statement names.
                let mut alternatives: Option<Vec<(Sentence, Formula)>> = None;
                let claim = match grounded.as_ref().and_then(|g| g.alternatives.get(&reference.id)) {
                    Some(choices) => {
                        // The statement about each individual that may be chosen, read by itself.
                        let mut parts: Vec<(Sentence, Formula)> = Vec::new();
                        for (_, group) in choices {
                            let mut one = sentence.clone();
                            if let Core::Deontic { vp, .. } = &mut one.core {
                                *vp = group.clone();
                            }
                            match claim_formula(&one, &alone, lex) {
                                Some(part) => parts.push((one, part)),
                                None => break,
                            }
                        }
                        if parts.is_empty() || parts.len() != choices.len() {
                            // The alternatives are not told apart: nothing is read of the statement.
                            model.unread.push((reference.clone(), crate::reading::key::Unread { part: sentence.core.render(), kind: "a response that chooses an individual,", place: "in a form whose alternatives the reading does not tell apart", phrase: String::new() }));
                            continue;
                        }
                        let chosen: Vec<Formula> = choices.iter().zip(&parts).map(|((may, _), (_, part))| Formula::And(vec![may.clone(), part.clone()])).collect();
                        alternatives = Some(parts);
                        combine(Some(Conj::Or), chosen)
                    }
                    None => claim,
                };
                // A sentence that matches a role's activation binds its subject
                // to the role. The role is declared beside the sentence: what
                // it makes of the sentence is no part of the contract of the
                // sentence, and it stands beside the contract, as what
                // follows from the claim of the sentence.
                let mut bound_roles: Vec<Formula> = Vec::new();
                for info in &roles {
                    for activation in &info.role.activations {
                        for bound in match_core(&activation.core, &sentence.core) {
                            if let Some(subject) = bound.get(SUBJECT_VARIABLE) {
                                bound_roles.push(Formula::atom(Atom::Role { subject: lex.resolve(&lex.canon(subject)), role: info.qualified.clone() }));
                            }
                        }
                    }
                }
                let guarantee = claim;
                let kind = read.kind;
                // An instance holds of its individuals: of those that are of
                // the named types and stand in the named relations.
                let assume = match grounded.as_ref().and_then(|g| g.guards.get(&reference.id)) {
                    Some(of_the_domain) if guard == Formula::True => of_the_domain.clone(),
                    Some(of_the_domain) => Formula::And(vec![guard.clone(), of_the_domain.clone()]),
                    None => guard.clone(),
                };
                if let Some(grounded) = &grounded {
                    let condition = |keyword: &str, clause: &Clause| frame_formula(keyword, &ClauseGroup::single(clause.clone()), lex);
                    match &alternatives {
                        // Each alternative is accounted as the instance of its individual.
                        Some(parts) => {
                            for (at, (one, part)) in parts.iter().enumerate() {
                                grounded.account(&format!("{}|{at}", reference.id), one, part, &condition, &mut atoms);
                            }
                        }
                        None => grounded.account(&reference.id, sentence, &guarantee, &condition, &mut atoms),
                    }
                }
                // An instance of a statement that bounds a share is counted and not required.
                if let Some(statement) = grounded.as_ref().and_then(|g| g.counted.get(&reference.id)) {
                    model.counted.push(Counted { statement: statement.clone(), constraint: Constraint { kind, assume, guarantee, refs: vec![reference.clone()] } });
                    continue;
                }
                if !bound_roles.is_empty() {
                    let claimed = if assume == Formula::True { guarantee.clone() } else { Formula::And(vec![assume.clone(), guarantee.clone()]) };
                    carried_roles.push(Constraint { kind: ConstraintKind::Carried, assume: claimed, guarantee: Formula::And(bound_roles), refs: vec![reference.clone()] });
                }
                model.constraints.push(Constraint { kind, assume, guarantee, refs: vec![reference.clone()] });
                model.constraints.append(&mut carried_roles);

                // A malformed name cannot exist in a role's specification set,
                // whatever the sentence's conditions are.
                for info in &roles {
                    for form in &info.role.forms {
                        let re = compiled(&form.regex);
                        let selector = form.applies_when.as_deref().and_then(compiled);
                        let mut matches = match_core(&form.pattern.core, &sentence.core);
                        matches.extend(match_clauses(&form.pattern.core, sentence));
                        for bound in matches {
                            let (Some(subject), Some(value), Some(re)) = (bound.get(SUBJECT_VARIABLE), bound.get(&form.variable), re.as_ref()) else { continue };
                            if selector.as_ref().is_some_and(|sel| !sel.is_match(value)) || re.is_match(value) != form.negated {
                                continue;
                            }
                            model.constraints.push(Constraint {
                                kind: ConstraintKind::Form,
                                assume: Formula::True,
                                guarantee: Formula::not(Formula::atom(Atom::Role { subject: lex.resolve(&lex.canon(subject)), role: info.qualified.clone() })),
                                refs: vec![SpecRef { id: format!("{}::{}", info.qualified, form.id), file: form.file.clone(), line: form.line, text: form.text.clone() }, reference.clone()],
                            });
                        }
                    }
                }
            }
        }
    }
    if let Some(at) = accounted.take() {
        model.absorb(&at, crate::reading::key::end());
    }
    // `shall be archived` is the passive of an action. Where a statement
    // names `archived` as a value of the subject, the action establishes it
    // and its prohibition excludes it.
    let passive: Vec<(SpecRef, Vec<Formula>)> = model
        .constraints
        .iter()
        .filter(|c| matches!(c.kind, ConstraintKind::Spec | ConstraintKind::Permission))
        .filter_map(|c| {
            let mut links = Vec::new();
            let mut visit = |a: &Atom, _: bool| {
                let (Atom::Act { key } | Atom::Forbid { key }) = a else { return };
                let Some((subject, action)) = key.split_once('|') else { return };
                let Some(value) = action.strip_prefix("be ") else { return };
                if !universe.get(subject).is_some_and(|known| known.contains(value)) {
                    return;
                }
                let held = Formula::atom(Atom::Val { attr: subject.to_string(), value: value.to_string() });
                let link = match a {
                    Atom::Act { .. } => Formula::implies(Formula::atom(a.clone()), held),
                    _ => Formula::implies(Formula::atom(a.clone()), Formula::not(held)),
                };
                if !links.contains(&link) {
                    links.push(link);
                }
            };
            c.assume.atoms(true, &mut visit);
            c.guarantee.atoms(true, &mut visit);
            (!links.is_empty()).then(|| (c.refs.first().cloned(), links))
        })
        .filter_map(|(at, links)| at.map(|at| (at, links)))
        .collect();
    carried.extend(passive.into_iter().map(|(at, links)| (at, Formula::True, links)));
    carry_to_others(&mut model, carried);
    // Order is a strict partial order.
    let mut orders = BTreeSet::new();
    for c in &model.constraints {
        c.guarantee.atoms(true, &mut |a, _| {
            if let Atom::Before { first, second } = a {
                orders.insert((first.clone(), second.clone()));
            }
        });
    }
    let before = |a: &str, b: &str| Formula::atom(Atom::Before { first: a.to_string(), second: b.to_string() });
    for (a, b) in &orders {
        if orders.contains(&(b.clone(), a.clone())) && a < b {
            model.background.push(Formula::not(Formula::And(vec![before(a, b), before(b, a)])));
        }
        if a == b {
            model.background.push(Formula::not(before(a, a)));
        }
        for (_, c) in orders.iter().filter(|(x, _)| x == b) {
            model.background.push(Formula::implies(Formula::And(vec![before(a, b), before(b, c)]), before(a, c)));
            if orders.contains(&(c.clone(), a.clone())) {
                model.background.push(Formula::not(Formula::And(vec![before(a, b), before(b, c), before(c, a)])));
            }
        }
    }
    // Performing an action is the event that a condition on it waits for.
    let (mut acts, mut events) = (BTreeSet::new(), BTreeSet::new());
    for c in &model.constraints {
        let mut visit = |a: &Atom, _: bool| match a {
            Atom::Act { key } => {
                acts.insert(key.clone());
            }
            Atom::Event { key } => {
                events.insert(key.clone());
            }
            _ => {}
        };
        c.assume.atoms(true, &mut visit);
        c.guarantee.atoms(true, &mut visit);
    }
    for key in acts {
        let text = key.replace('|', " ");
        if events.contains(&text) {
            model.background.push(Formula::implies(Formula::atom(Atom::Act { key }), Formula::atom(Atom::Event { key: text })));
        }
    }
    resolve_units(&mut model);
    measure_axioms(&mut model);
    model.base_domains = model.closed_domains.clone();
    for (attr, values) in extended {
        if let Some(domain) = model.closed_domains.get_mut(&attr) {
            domain.extend(values);
        }
    }
    // Denying one value of a closed domain handles every other value:
    // `, unless the valve is Open` covers `Closed`.
    for (attr, value) in denied_values {
        if let Some(domain) = model.closed_domains.get(&attr) {
            model.guarded_values.entry(attr).or_default().extend(domain.iter().filter(|v| **v != value).cloned());
        }
    }
    // A statement that yields to another one applies only outside the other's condition.
    crate::reading::temporal::resolve_origins(&mut model);
    crate::reading::priority::apply(set, lex, &mut model);
    // Definitions, inclusions, exclusions and refinements relate the atoms above.
    crate::reading::meaning::apply(set, lex, &mut model);
    // Statements about individuals are read over a bounded domain.
    let none = BTreeSet::new();
    // The statements about the domain are read over the domain of the instances.
    let scope = grounded.as_ref().map_or(scope, |g| g.individuals.scope);
    let with_domain = grounded.as_ref().map_or(set, |g| &g.with_domain);
    crate::reading::instances::apply(with_domain, lex, &mut model, scope, grounded.is_some(), grounded.as_ref().map_or(&none, |g| &g.relations));
    let domain = if grounded.is_some() { crate::reading::instances::facts(with_domain, lex, scope) } else { Vec::new() };
    if let Some(grounded) = grounded {
        // A relation or a kind that a statement states of its individuals.
        for direct in grounded.direct {
            // What the statement says of the declared individuals follows
            // from what its sentence claims: it stands beside the contract.
            let (kind, assume) = match claim_of(&model, &direct.reference.id) {
                Some(claim) if direct.assume == Formula::True => (ConstraintKind::Carried, claim),
                Some(claim) => (ConstraintKind::Carried, Formula::And(vec![claim, direct.assume])),
                None => (ConstraintKind::Axiom, direct.assume),
            };
            model.constraints.push(Constraint { kind, assume, guarantee: direct.guarantee, refs: vec![direct.reference] });
        }
        model.instance_scope = Some(grounded.individuals.scope);
        let mut individuals = grounded.individuals;
        individuals.atoms.extend(atoms.into_iter().filter(|a| !individuals.atoms.contains(a)).collect::<Vec<_>>());
        // What each atom about the domain says: the kind of an individual,
        // or a relation between two. An individual is named by a noun of
        // its carrier, and a fact names it by the declared noun.
        let canonical: BTreeMap<String, String> = individuals.types.iter().cloned().collect();
        let named = |individual: &str| individual.rsplit_once('#').map(|(noun, index)| format!("{}#{index}", canonical.get(noun).map_or(noun, String::as_str)));
        let mut of_the_domain: BTreeSet<Atom> = BTreeSet::new();
        for formula in model.constraints.iter().flat_map(|c| [&c.assume, &c.guarantee]).chain(&model.background) {
            formula.atoms(true, &mut |atom, _| {
                if matches!(atom, Atom::Rel { name, .. } if !name.ends_with(" between")) {
                    of_the_domain.insert(atom.clone());
                }
            });
        }
        for atom in of_the_domain {
            let Atom::Rel { name, args } = &atom else { continue };
            let fact = match args.as_slice() {
                [subject] => named(subject).map(|subject| crate::reading::ground::Fact::Kind { kind: name.clone(), subject }),
                [owner, member] => named(owner).zip(named(member)).map(|(owner, member)| crate::reading::ground::Fact::Related { relation: name.clone(), owner, member }),
                _ => None,
            };
            if let Some(fact) = fact {
                let entry = crate::reading::ground::AtomOf { atom, fact };
                if !individuals.atoms.contains(&entry) {
                    individuals.atoms.push(entry);
                }
            }
        }
        // An occurrence with a role is an occurrence of the same action
        // or event without it: `notify the author about the message` is a
        // notifying of the author.
        let occurrences: Vec<(&Atom, &crate::reading::ground::Fact)> = individuals.atoms.iter().filter(|a| matches!(a.fact, crate::reading::ground::Fact::Occurs { .. })).map(|a| (&a.atom, &a.fact)).collect();
        for (narrow_atom, narrow) in &occurrences {
            for (wide_atom, wide) in &occurrences {
                let (crate::reading::ground::Fact::Occurs { verb: v1, particle: p1, actor: a1, object: o1, roles: r1 }, crate::reading::ground::Fact::Occurs { verb: v2, particle: p2, actor: a2, object: o2, roles: r2 }) = (narrow, wide) else { continue };
                let same_kind = matches!((narrow_atom, wide_atom), (Atom::Act { .. }, Atom::Act { .. }) | (Atom::Event { .. }, Atom::Event { .. }));
                if same_kind && (v1, p1, a1, o1) == (v2, p2, a2, o2) && r2.len() < r1.len() && r2.iter().all(|role| r1.contains(role)) {
                    let axiom = Formula::implies(Formula::atom((*narrow_atom).clone()), Formula::atom((*wide_atom).clone()));
                    if !model.background.contains(&axiom) {
                        model.background.push(axiom);
                    }
                }
            }
        }
        individuals.domain = domain;
        individuals.shares = shares;
        model.individuals = Some(individuals);
    }
    model
}
