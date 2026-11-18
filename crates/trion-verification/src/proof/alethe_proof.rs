//! A [`Derivation`] as an Alethe proof, for Carcara.
//!
//! Each step of the derivation is one step of Alethe ("The Alethe Proof
//! Format", the typeset that the `alethe` crate follows, §5.2 for the
//! rules), with its clause stated:
//!
//! - an assumption is `assume`, named `h<k>` for the `k`-th assertion of the
//!   problem (from 1); the assumptions come first;
//! - a definition is `and_pos` (with the index of the part), `and_neg`,
//!   `or_pos`, `or_neg` (with the index), `implies_pos`, `implies_neg1`,
//!   `implies_neg2`, `true` or `false`;
//! - a double negation is `not_not`, `(cl (not (not (not t))) t)`, resolved
//!   with the premise on `(not (not t))`;
//! - factoring is `contraction`;
//! - resolution is `resolution` with its pivot and polarity as arguments;
//! - a Farkas lemma is `la_generic`, whose arguments are the coefficient of
//!   each literal: the multiplier of its negation, which for an equation
//!   `s = n` is that of `s ≥ n` less that of `s ≤ n` (the rule reads each
//!   negation as `s ⋈ d` with `⋈` among `>`, `≥`, `=` and tightens a strict
//!   comparison of integers, as the solver does);
//! - a trichotomy is `la_disequality` followed by `or`.
//!
//! The steps are named `t<n>`. The proof ends with the empty clause.

use super::derivation::{Definition, Derivation, How, Weight};
use super::smt::{apply, boolean, not, number};
use alethe::{Assume, Command, Proof, Step};
use smtlib::term::NonEmpty;
use smtlib::{Symbol, Term};

fn symbol(name: &str) -> Symbol {
    Symbol::new(name).unwrap_or_else(|_| unreachable!("{name} is a symbol"))
}

fn error(e: alethe::Error) -> String {
    format!("the Alethe writer: {e}")
}

/// Steps that are written one after the other, each named `t<n>`.
struct Writer {
    commands: Vec<Command>,
    next: usize,
}

impl Writer {
    fn step(&mut self, clause: Vec<Term>, rule: &str, premises: &[Symbol], args: Vec<Term>) -> Result<Symbol, String> {
        self.next += 1;
        let id = symbol(&format!("t{}", self.next));
        let mut step = Step::new(id.clone(), clause, symbol(rule)).map_err(error)?;
        if let Some(premises) = NonEmpty::new(premises.to_vec()) {
            step = step.with_premises(premises).map_err(error)?;
        }
        if let Some(args) = NonEmpty::new(args) {
            step = step.with_args(args).map_err(error)?;
        }
        self.commands.push(Command::Step(step));
        Ok(id)
    }
}

impl Derivation {
    /// The Alethe proof of the derivation, for the problem whose assertions
    /// [`super::problem`] writes.
    pub fn alethe(&self) -> Result<Proof, String> {
        let mut writer = Writer { commands: Vec::new(), next: 0 };
        let mut ids: Vec<Symbol> = Vec::with_capacity(self.steps.len());
        // The assumptions first, each once: Carcara warns of one after a step.
        let mut assumed: Vec<Option<Symbol>> = vec![None; self.assertions.len()];
        for step in &self.steps {
            if let How::Assume(k) = step.how {
                if assumed[k].is_none() {
                    let id = symbol(&format!("h{}", k + 1));
                    writer.commands.push(Command::Assume(Assume::new(id.clone(), self.assertions[k].clone()).map_err(error)?));
                    assumed[k] = Some(id);
                }
            }
        }
        for step in &self.steps {
            let clause = step.clause.clone();
            let id = match &step.how {
                How::Assume(k) => assumed[*k].clone().unwrap_or_else(|| unreachable!("each assumption is written above")),
                How::Definition(definition, _) => {
                    let (rule, args) = match definition {
                        Definition::AndPos(i) => ("and_pos", vec![number(*i as i128)]),
                        Definition::AndNeg => ("and_neg", vec![]),
                        Definition::OrPos => ("or_pos", vec![]),
                        Definition::OrNeg(i) => ("or_neg", vec![number(*i as i128)]),
                        Definition::ImpliesPos => ("implies_pos", vec![]),
                        Definition::ImpliesNeg1 => ("implies_neg1", vec![]),
                        Definition::ImpliesNeg2 => ("implies_neg2", vec![]),
                        Definition::True => ("true", vec![]),
                        Definition::False => ("false", vec![]),
                    };
                    writer.step(clause, rule, &[], args)?
                }
                How::Unwrap { premise, inner } => {
                    let doubled = not(not(inner.clone()));
                    let law = writer.step(vec![not(doubled.clone()), inner.clone()], "not_not", &[], vec![])?;
                    writer.step(clause, "resolution", &[ids[*premise].clone(), law], vec![doubled, boolean(true)])?
                }
                How::Factor(premise) => writer.step(clause, "contraction", &[ids[*premise].clone()], vec![])?,
                How::Resolve { left, right, pivot, polarity } => writer.step(clause, "resolution", &[ids[*left].clone(), ids[*right].clone()], vec![pivot.clone(), boolean(*polarity)])?,
                How::Farkas(rows) => {
                    let coefficients = rows
                        .iter()
                        .map(|row| match row.weight {
                            Weight::One(m) => Ok(number(m)),
                            Weight::Equality { upper, lower } => lower.checked_sub(upper).map(number).ok_or_else(|| "a coefficient overflows".to_string()),
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    writer.step(clause, "la_generic", &[], coefficients)?
                }
                How::Trichotomy { .. } => {
                    // `(or (= s v) (not (<= s v)) (not (<= v s)))`: the clause as one term.
                    let disjunction = apply("or", clause.clone());
                    let law = writer.step(vec![disjunction], "la_disequality", &[], vec![])?;
                    writer.step(clause, "or", &[law], vec![])?
                }
            };
            ids.push(id);
        }
        Ok(Proof::new(writer.commands))
    }
}
