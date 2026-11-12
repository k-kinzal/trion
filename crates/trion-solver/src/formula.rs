//! The logical vocabulary: the formulas that contracts are stated in.
//!
//! A formula is a propositional combination of atoms. An atom is a fact about
//! a term at one moment (an action happens, an attribute has a value, an
//! event occurs) or a linear comparison of integer quantities. Everything
//! after the reading of the sentences works on these formulas only.

use serde::Serialize;
use std::fmt;

/// Numbers are stored in thousandths so that decimals stay exact integers.
pub const NUMERIC_SCALE: i64 = 1000;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub enum Cmp {
    Eq,
    Ge,
    Le,
    Gt,
    Lt,
}

impl Atom {
    /// `first − second cmp n`: a relation between two quantities, or between
    /// two moments when the quantities are times.
    pub fn difference(first: &str, second: &str, unit: &str, cmp: Cmp, n: i64) -> Atom {
        Atom::Lin { terms: vec![(first.to_string(), 1), (second.to_string(), -1)], unit: unit.to_string(), cmp, n }
    }
}

impl Cmp {
    pub fn symbol(self) -> &'static str {
        match self {
            Cmp::Eq => "=",
            Cmp::Ge => "≥",
            Cmp::Le => "≤",
            Cmp::Gt => ">",
            Cmp::Lt => "<",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub enum Atom {
    /// The value belongs to the attribute's domain.
    Dom { attr: String, value: String },
    /// The attribute has the value at a given moment.
    Val { attr: String, value: String },
    /// The action happens.
    Act { key: String },
    /// The action is forbidden.
    Forbid { key: String },
    /// The action is advised against: `should not`.
    Discouraged { key: String },
    /// The event or state holds.
    Event { key: String },
    /// The configuration has the feature. A feature is selected, never triggered.
    Config { key: String },
    /// The term is bound to the role.
    Role { subject: String, role: String },
    /// A numeric comparison on the attribute.
    Num { attr: String, unit: String, cmp: Cmp, n: i64 },
    /// A comparison of a sum of quantities with a number: `timeout − retry
    /// interval < 0`. Each term is a quantity with its coefficient.
    Lin { terms: Vec<(String, i64)>, unit: String, cmp: Cmp, n: i64 },
    /// One action completes before another starts.
    Before { first: String, second: String },
    /// A property of one individual, or a relation between two individuals,
    /// of a bounded domain: `room(room#1)`, `owner(room#1, member#2)`.
    Rel { name: String, args: Vec<String> },
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Dom { attr, value } => write!(f, "Dom({attr}, {value})"),
            Atom::Val { attr, value } => write!(f, "Val({attr}, {value})"),
            Atom::Act { key } => write!(f, "Act({key})"),
            Atom::Forbid { key } => write!(f, "Forbid({key})"),
            Atom::Discouraged { key } => write!(f, "Discouraged({key})"),
            Atom::Event { key } => write!(f, "Event({key})"),
            Atom::Config { key } => write!(f, "Config({key})"),
            Atom::Role { subject, role } => write!(f, "Role({subject}, {role})"),
            Atom::Before { first, second } => write!(f, "Before({first}, {second})"),
            Atom::Rel { name, args } => write!(f, "{name}({})", args.join(", ")),
            Atom::Num { attr, unit, cmp, n } => {
                let scaled = *n as f64 / NUMERIC_SCALE as f64;
                write!(f, "{attr} {} {scaled} {unit}", cmp.symbol())
            }
            Atom::Lin { terms, unit, cmp, n } => {
                // The quantities that are added stand before those that are taken away.
                let ordered = terms.iter().filter(|(_, coef)| *coef > 0).chain(terms.iter().filter(|(_, coef)| *coef <= 0));
                for (i, (attr, coef)) in ordered.enumerate() {
                    let sign = match (i, *coef < 0) {
                        (0, false) => "",
                        (0, true) => "−",
                        (_, false) => " + ",
                        (_, true) => " − ",
                    };
                    match coef.abs() {
                        1 => write!(f, "{sign}{attr}")?,
                        k => write!(f, "{sign}{k}·{attr}")?,
                    }
                }
                let scaled = *n as f64 / NUMERIC_SCALE as f64;
                write!(f, " {} {scaled}{}{unit}", cmp.symbol(), if unit.is_empty() { "" } else { " " })
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Formula {
    True,
    Atom(Atom),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
}

impl Formula {
    /// The formula with each atom replaced.
    pub fn map_atoms(self, f: &dyn Fn(Atom) -> Atom) -> Formula {
        match self {
            Formula::Atom(atom) => Formula::Atom(f(atom)),
            Formula::Not(inner) => Formula::Not(Box::new(inner.map_atoms(f))),
            Formula::And(items) => Formula::And(items.into_iter().map(|i| i.map_atoms(f)).collect()),
            Formula::Or(items) => Formula::Or(items.into_iter().map(|i| i.map_atoms(f)).collect()),
            Formula::Implies(a, b) => Formula::Implies(Box::new(a.map_atoms(f)), Box::new(b.map_atoms(f))),
            other => other,
        }
    }

    pub fn not(f: Formula) -> Self {
        Formula::Not(Box::new(f))
    }

    pub fn implies(a: Formula, b: Formula) -> Self {
        Formula::Implies(Box::new(a), Box::new(b))
    }

    /// The formula of one atom.
    pub fn atom(a: Atom) -> Self {
        Formula::Atom(a)
    }

    /// Visits every atom with its polarity.
    pub fn atoms(&self, positive: bool, visit: &mut dyn FnMut(&Atom, bool)) {
        match self {
            Formula::True => {}
            Formula::Atom(a) => visit(a, positive),
            Formula::Not(x) => x.atoms(!positive, visit),
            Formula::And(xs) | Formula::Or(xs) => xs.iter().for_each(|x| x.atoms(positive, visit)),
            Formula::Implies(a, b) => {
                a.atoms(!positive, visit);
                b.atoms(positive, visit);
            }
        }
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn join(f: &mut fmt::Formatter<'_>, items: &[Formula], sep: &str) -> fmt::Result {
            write!(f, "(")?;
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    write!(f, " {sep} ")?;
                }
                write!(f, "{item}")?;
            }
            write!(f, ")")
        }
        match self {
            Formula::True => write!(f, "⊤"),
            Formula::Atom(a) => write!(f, "{a}"),
            Formula::Not(x) => write!(f, "¬{x}"),
            Formula::And(xs) => join(f, xs, "∧"),
            Formula::Or(xs) => join(f, xs, "∨"),
            Formula::Implies(a, b) => write!(f, "({a} → {b})"),
        }
    }
}
