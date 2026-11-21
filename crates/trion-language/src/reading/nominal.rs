//! Structured nominal predicates, before a subject is assigned.

use super::{key, model, Lexicon};
use crate::syntax::ast::*;
use serde::Serialize;
use std::collections::BTreeSet;
use trion_solver::{Atom, Formula};

pub(super) fn parts(group: &NpGroup) -> (&[Np], Conj) {
    match group {
        NpGroup::Single(np) => (std::slice::from_ref(np), Conj::And),
        NpGroup::Coordinated { items, conj, .. } => (items, *conj),
    }
}

pub(super) fn name(np: &Np, lex: &Lexicon) -> String {
    let mut bare = np.clone();
    bare.of = None;
    bare.of_also.clear();
    bare.of_conj = None;
    bare.relative = None;
    model::np_key(&bare, lex)
}

/// A Boolean predicate over one subject. The leaves identify the properties
/// of that subject. The reading of a leaf depends on the representation of
/// its subject, while the connectives are shared.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Nominal<T> {
    Atom(T),
    And(Vec<Self>),
    Or(Vec<Self>),
    Not(Box<Self>),
}

impl<T> Nominal<T> {
    pub fn map<U>(self, atom: &impl Fn(T) -> U) -> Nominal<U> {
        match self {
            Self::Atom(value) => Nominal::Atom(atom(value)),
            Self::And(items) => {
                Nominal::And(items.into_iter().map(|item| item.map(atom)).collect())
            }
            Self::Or(items) => Nominal::Or(items.into_iter().map(|item| item.map(atom)).collect()),
            Self::Not(inner) => Nominal::Not(Box::new(inner.map(atom))),
        }
    }

    pub fn atoms(&self, visit: &mut impl FnMut(&T)) {
        match self {
            Self::Atom(atom) => visit(atom),
            Self::And(items) | Self::Or(items) => items.iter().for_each(|item| item.atoms(visit)),
            Self::Not(inner) => inner.atoms(visit),
        }
    }

    pub fn holds(&self, atom_holds: &impl Fn(&T) -> bool) -> bool {
        match self {
            Self::Atom(atom) => atom_holds(atom),
            Self::And(items) => items.iter().all(|item| item.holds(atom_holds)),
            Self::Or(items) => items.iter().any(|item| item.holds(atom_holds)),
            Self::Not(inner) => !inner.holds(atom_holds),
        }
    }

    pub(super) fn formula(&self, lower: &impl Fn(&T) -> Formula) -> Formula {
        match self {
            Self::Atom(atom) => lower(atom),
            Self::And(items) => {
                Formula::And(items.iter().map(|item| item.formula(lower)).collect())
            }
            Self::Or(items) => Formula::Or(items.iter().map(|item| item.formula(lower)).collect()),
            Self::Not(inner) => Formula::not(inner.formula(lower)),
        }
    }
}

impl<T: std::fmt::Display> std::fmt::Display for Nominal<T> {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Atom(value) => write!(out, "{value}"),
            Self::Not(inner) => write!(out, "¬{inner}"),
            Self::And(items) | Self::Or(items) => {
                let operator = if matches!(self, Self::And(_)) {
                    " ∧ "
                } else {
                    " ∨ "
                };
                let text = items
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(operator);
                write!(out, "({text})")
            }
        }
    }
}

type Unread = (String, &'static str);

fn property<T>(
    group: &NpGroup,
    lex: &Lexicon,
    stack: &mut BTreeSet<String>,
    leaf: &impl Fn(String, Option<&Np>, &Lexicon) -> Result<T, Unread>,
) -> Result<Nominal<T>, Unread> {
    let (items, conj) = parts(group);
    let mut claims = Vec::with_capacity(items.len());
    for np in items {
        if !matches!(np.det, None | Some(Det::A | Det::An | Det::The)) {
            return Err((np.render(), "whose quantifier requires a named subject"));
        }
        if !np.of_also.is_empty() {
            return Err((np.render(), "with coordinated owners"));
        }
        let symbol = name(np, lex);
        let base = if let Some(owner) = &np.of {
            Nominal::Atom(leaf(symbol, Some(owner), lex)?)
        } else if matches!(np.det, Some(Det::The)) {
            return Err((
                np.render(),
                "with a definite complement. Use an alias for another name of the same symbol",
            ));
        } else if let Some(derived) = lex.derived(&symbol) {
            if !stack.insert(symbol.clone()) {
                return Err((np.render(), "whose derived classes are cyclic"));
            }
            key::register_definition(&derived.reference);
            let result = property(&derived.body, &lex.in_definition(derived), stack, leaf)?;
            stack.remove(&symbol);
            result
        } else {
            Nominal::Atom(leaf(symbol, None, lex)?)
        };
        claims.push(match &np.relative {
            Some(relative) => Nominal::And(vec![base, restriction(relative, lex, stack, leaf)?]),
            None => base,
        });
    }
    Ok(if claims.len() == 1 {
        claims.pop().unwrap()
    } else if conj == Conj::And {
        Nominal::And(claims)
    } else {
        Nominal::Or(claims)
    })
}

fn restriction<T>(
    relative: &Relative,
    lex: &Lexicon,
    stack: &mut BTreeSet<String>,
    leaf: &impl Fn(String, Option<&Np>, &Lexicon) -> Result<T, Unread>,
) -> Result<Nominal<T>, Unread> {
    let (group, denied) = match (&relative.marker, &relative.body) {
        (
            RelMarker::That | RelMarker::Who,
            RelativeBody::Copular {
                predicate:
                    Predicate::Words {
                        words,
                        nominal: Some(group),
                    },
                agent: None,
                roles,
                ..
            },
        ) if roles.is_empty() => (
            group,
            words
                .first()
                .is_some_and(|word| word.eq_ignore_ascii_case("not")),
        ),
        _ => {
            return Err((
                relative.render(),
                "whose relative clause needs a meaning over the same subject",
            ))
        }
    };
    let claim = property(group, lex, stack, leaf)?;
    let claim = if denied {
        Nominal::Not(Box::new(claim))
    } else {
        claim
    };
    Ok(match &relative.and {
        Some(next) => Nominal::And(vec![claim, restriction(next, lex, stack, leaf)?]),
        None => claim,
    })
}

pub(super) fn claim(group: &NpGroup, subject: &Np, lex: &Lexicon) -> Formula {
    let holder = model::subject_key(subject, lex);
    let reading = property(group, lex, &mut BTreeSet::new(), &|symbol, owner, lex| {
        let mut args = vec![holder.clone()];
        let kind = if let Some(owner) = owner {
            if !matches!(owner.det, None | Some(Det::The)) || owner.relative.is_some() {
                return Err((
                    owner.render(),
                    "whose owner needs a quantifier or restriction",
                ));
            }
            args.push(model::subject_key(owner, lex));
            "relation"
        } else {
            "class"
        };
        Ok(Formula::atom(Atom::Rel {
            name: format!("{kind} {symbol}"),
            args,
        }))
    });
    match reading {
        Ok(predicate) => predicate.formula(&Formula::clone),
        Err((text, reason)) => {
            key::unread_node(&text, "a nominal predicate", reason);
            Formula::True
        }
    }
}

/// A static classification of the same subject over a bounded carrier.
pub(super) fn classes(group: &NpGroup, lex: &Lexicon) -> Option<Nominal<String>> {
    property(
        group,
        lex,
        &mut BTreeSet::new(),
        &|name, owner, _| match owner {
            Some(np) => Err((np.render(), "whose owner needs a relation over individuals")),
            None => Ok(name),
        },
    )
    .ok()
}

/// Only these formulas may appear in a conservative predicate abbreviation.
/// No clause is evaluated in an extra context or at a different moment.
pub(super) fn definable(group: &NpGroup) -> bool {
    static_nominal(group, false)
}

/// The static nominal fragment can be instantiated by substituting the
/// subject and each named owner. A derived class has only its subject.
pub fn mappable_nominal(group: &NpGroup) -> bool {
    static_nominal(group, true)
}

fn static_nominal(group: &NpGroup, named_owners: bool) -> bool {
    fn relative_is_static(relative: &Relative, named_owners: bool) -> bool {
        matches!((&relative.marker, &relative.body),
            (RelMarker::That | RelMarker::Who, RelativeBody::Copular { predicate: Predicate::Words { nominal: Some(group), .. }, agent: None, roles, .. })
            if roles.is_empty() && static_nominal(group, named_owners))
            && relative
                .and
                .as_deref()
                .is_none_or(|next| relative_is_static(next, named_owners))
    }
    parts(group).0.iter().all(|np| {
        let supported_head = match &np.of {
            None => matches!(np.det, Some(Det::A | Det::An)),
            Some(owner) => {
                named_owners
                    && matches!(np.det, None | Some(Det::A | Det::An | Det::The))
                    && matches!(owner.det, None | Some(Det::The))
                    && owner.of.is_none()
                    && owner.of_also.is_empty()
                    && owner.relative.is_none()
            }
        };
        supported_head
            && np.of_also.is_empty()
            && np
                .relative
                .as_deref()
                .is_none_or(|relative| relative_is_static(relative, named_owners))
    })
}

/// Uses of names introduced by a nominal predicate, including dependencies of
/// an abbreviation. Owners are arguments and the relative shares the subject.
pub(super) fn symbols(group: &NpGroup, lex: &Lexicon, out: &mut Vec<(String, &'static str)>) {
    fn relative_symbols(relative: &Relative, lex: &Lexicon, out: &mut Vec<(String, &'static str)>) {
        if let RelativeBody::Copular {
            predicate:
                Predicate::Words {
                    nominal: Some(group),
                    ..
                },
            ..
        } = &relative.body
        {
            symbols(group, lex, out);
        }
        if let Some(next) = &relative.and {
            relative_symbols(next, lex, out);
        }
    }
    for np in parts(group).0 {
        out.push((
            name(np, lex),
            if np.of.is_some() { "relation" } else { "class" },
        ));
        if let Some(owner) = &np.of {
            out.push((model::np_key(owner, lex), "object"));
        }
        if let Some(relative) = &np.relative {
            relative_symbols(relative, lex, out);
        }
    }
}
