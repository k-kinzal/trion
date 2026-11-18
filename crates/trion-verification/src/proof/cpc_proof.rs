//! A [`Derivation`] as the body of a CPC proof, for Ethos.
//!
//! CPC is the calculus of cvc5 1.4.2, defined in Eunoia by the signature
//! `proofs/eo/cpc` of its sources; the rules named here are those of
//! `Cpc.eo` alone. A clause is the term `(or l…)`, a clause of one literal
//! the literal, and the empty clause `false`. The steps do not state their
//! conclusions, which Ethos computes, except the sum of a Farkas lemma and
//! the last step, which concludes `false`:
//!
//! - an assumption is `assume`, named `@h<k>` for the `k`-th assertion of
//!   the problem (from 1); the assumptions come first;
//! - a definition is `cnf_and_pos`, `cnf_and_neg`, `cnf_or_pos`,
//!   `cnf_or_neg`, `cnf_implies_pos`, `cnf_implies_neg1` or
//!   `cnf_implies_neg2` of the term; `true` is `true_elim` of `(refl true)`
//!   and `(not false)` is `false_elim` of `(refl false)`;
//! - a double negation `(not (not t))` is resolved with `(split t)`, which
//!   is `(or t (not t))`, on `(not t)`;
//! - factoring is `factoring`, resolution `resolution`;
//! - a Farkas lemma assumes the negation of each literal in a scope
//!   (`assume-push`), states it as a comparison that is not strict
//!   (the rewrites `arith-elim-int-lt`, `arith-elim-int-gt`,
//!   `arith-geq-tighten`, `arith-leq-norm`, `arith-elim-lt`, `arith-elim-gt`
//!   tighten and remove the negations), scales each by its weight
//!   (`arith_mult_pos`, `arith_mult_neg`), sums them (`arith_sum_ub`) to
//!   `L ≤ R`, shows by polynomial normalization (`arith_poly_norm`,
//!   `arith_poly_norm_rel`) that it is `d ≤ 0` for the positive number `d`
//!   that `L − R` is, which `evaluate` makes `false`, and closes the scopes
//!   (`scope`, `process_scope`, `not_and`);
//! - a trichotomy assumes `(not (= s v))`, `(<= s v)` and `(<= v s)` in a
//!   scope and refutes them with `arith-elim-leq`, `arith_trichotomy` and
//!   `contra`.
//!
//! The steps are named `@p<n>` and the local assumptions `@a<n>`; a
//! symbol that trion gives an atom or a quantity never starts with `@`.

use super::derivation::{application, Definition, Derivation, How, Op, Poly, Row, Weight};
use super::smt::{apply, number};
use eunoia::{Command, Literal, LiteralCategory, Script, Step, Symbol, Term};
use smtlib::lexicon::SpecConstant;

fn symbol(name: &str) -> Symbol {
    Symbol::new(name).unwrap_or_else(|_| unreachable!("{name} is a symbol"))
}

fn named(name: &str) -> Term {
    Term::Symbol(symbol(name))
}

fn app(head: &str, args: Vec<Term>) -> Term {
    Term::app(head, args).unwrap_or_else(|_| unreachable!("{head} is applied to a term"))
}

fn numeral(n: i128) -> Term {
    Term::Literal(Literal::numeral(n))
}

fn boolean(value: bool) -> Term {
    named(if value { "true" } else { "false" })
}

/// A term of the problem in Eunoia: the same symbols, numerals and
/// applications.
fn eo(term: &smtlib::Term) -> Result<Term, String> {
    match term {
        smtlib::Term::Constant(SpecConstant::Numeral(n)) => Literal::new(LiteralCategory::Numeral, n.as_str()).map(Term::Literal).map_err(|e| e.to_string()),
        smtlib::Term::Identifier(head) if head.sort().is_none() => match head.identifier().as_simple() {
            Some(s) => Symbol::new(s.as_str()).map(Term::Symbol).map_err(|e| format!("{s} is no Eunoia symbol: {e}")),
            None => Err(format!("{term} is no term of CPC that trion writes")),
        },
        _ => match application(term) {
            Some((head, args)) => Ok(app(head, args.iter().map(eo).collect::<Result<_, _>>()?)),
            None => Err(format!("{term} is no term of CPC that trion writes")),
        },
    }
}

/// The commands, each step named `@p<n>` and each local assumption `@a<n>`.
struct Writer {
    commands: Vec<Command>,
    next: usize,
}

impl Writer {
    fn fresh(&mut self, prefix: &str) -> Symbol {
        self.next += 1;
        symbol(&format!("{prefix}{}", self.next))
    }

    fn command(&mut self, pop: bool, conclusion: Option<Term>, rule: &str, premises: &[&Symbol], args: Vec<Term>) -> Symbol {
        let name = self.fresh("@p");
        let mut step = Step::new(name.clone(), symbol(rule));
        step.conclusion = conclusion;
        if !premises.is_empty() {
            step.premises = Some(premises.iter().map(|p| Term::Symbol((*p).clone())).collect());
        }
        if !args.is_empty() {
            step.args = Some(args);
        }
        self.commands.push(if pop { Command::StepPop(step) } else { Command::Step(step) });
        name
    }

    fn step(&mut self, rule: &str, premises: &[&Symbol], args: Vec<Term>) -> Symbol {
        self.command(false, None, rule, premises, args)
    }

    fn assume_push(&mut self, formula: Term) -> Symbol {
        let name = self.fresh("@a");
        self.commands.push(Command::AssumePush { name: name.clone(), formula });
        name
    }

    /// Closes the scopes of `pushed`, innermost first, around the proof
    /// `body` of `false`: the clause of the negations of the assumptions.
    fn close(&mut self, pushed: usize, body: Symbol) -> Symbol {
        let mut proof = body;
        for _ in 0..pushed {
            proof = self.command(true, None, "scope", &[&proof], vec![]);
        }
        let negation = self.step("process_scope", &[&proof], vec![boolean(false)]);
        if pushed > 1 {
            self.step("not_and", &[&negation], vec![])
        } else {
            negation
        }
    }

    /// The clause with its literal `(not (not t))` written `t`.
    fn unwrap(&mut self, clause: &Symbol, inner: Term) -> Symbol {
        let law = self.step("split", &[], vec![inner.clone()]);
        self.step("resolution", &[clause, &law], vec![boolean(false), app("not", vec![inner])])
    }

    /// `relation` from the proof of `φ` and of the equation `(= φ (not G))`
    /// that a rewrite proves: `G`.
    fn through_negation(&mut self, phi: &Symbol, equation: Symbol, relation: Term) -> Symbol {
        let clause = self.step("equiv_elim2", &[&equation], vec![]);
        let doubled = self.step("resolution", &[&clause, phi], vec![boolean(true), relation]);
        self.step("not_not_elim", &[&doubled], vec![])
    }
}

/// A comparison that is not strict, `(op left right)` with `op` `<=`, `>=`
/// or `=`, with its proof.
struct Bound {
    op: Op,
    left: smtlib::Term,
    right: smtlib::Term,
    proof: Symbol,
}

fn plus_one(term: &smtlib::Term) -> smtlib::Term {
    apply("+", vec![term.clone(), number(1)])
}

/// The negation of a row's literal, assumed as `phi`, as a bound.
fn bound(writer: &mut Writer, row: &Row, phi: Symbol) -> Result<Bound, String> {
    let (l, r) = (&row.relation.left, &row.relation.right);
    let (el, er) = (eo(l)?, eo(r)?);
    let rewrite = |writer: &mut Writer, rule: &str| writer.step(rule, &[], vec![el.clone(), er.clone()]);
    let comparison = |op: &str| app(op, vec![el.clone(), er.clone()]);
    Ok(match (row.relation.op, row.positive) {
        (op @ (Op::Le | Op::Ge | Op::Eq), false) => Bound { op, left: l.clone(), right: r.clone(), proof: phi },
        // `l < r` is `r ≥ l + 1`, and `l > r` is `l ≥ r + 1`.
        (Op::Lt, false) => {
            let equation = rewrite(writer, "arith-elim-int-lt");
            Bound { op: Op::Ge, left: r.clone(), right: plus_one(l), proof: writer.step("eq_resolve", &[&phi, &equation], vec![]) }
        }
        (Op::Gt, false) => {
            let equation = rewrite(writer, "arith-elim-int-gt");
            Bound { op: Op::Ge, left: l.clone(), right: plus_one(r), proof: writer.step("eq_resolve", &[&phi, &equation], vec![]) }
        }
        // `(not (>= l r))` is `r ≥ l + 1`.
        (Op::Ge, true) => {
            let equation = rewrite(writer, "arith-geq-tighten");
            Bound { op: Op::Ge, left: r.clone(), right: plus_one(l), proof: writer.step("eq_resolve", &[&phi, &equation], vec![]) }
        }
        // `(<= l r)` is `(not (>= l (+ r 1)))`, `(< l r)` is `(not (>= l
        // r))` and `(> l r)` is `(not (>= r l))`: their negations are the
        // comparisons inside.
        (Op::Le, true) => {
            let equation = rewrite(writer, "arith-leq-norm");
            Bound { op: Op::Ge, left: l.clone(), right: plus_one(r), proof: writer.through_negation(&phi, equation, comparison("<=")) }
        }
        (Op::Lt, true) => {
            let equation = rewrite(writer, "arith-elim-lt");
            Bound { op: Op::Ge, left: l.clone(), right: r.clone(), proof: writer.through_negation(&phi, equation, comparison("<")) }
        }
        (Op::Gt, true) => {
            let equation = rewrite(writer, "arith-elim-gt");
            Bound { op: Op::Ge, left: r.clone(), right: l.clone(), proof: writer.through_negation(&phi, equation, comparison(">")) }
        }
        (Op::Eq, true) => return Err(format!("the negation of {} is no inequality", row.literal)),
    })
}

fn op_name(op: Op) -> &'static str {
    match op {
        Op::Le => "<=",
        Op::Lt => "<",
        Op::Ge => ">=",
        Op::Gt => ">",
        Op::Eq => "=",
    }
}

/// The proof of `false` from the assumed negations of the rows of a Farkas lemma.
fn farkas(writer: &mut Writer, rows: &[Row], assumed: &[Symbol]) -> Result<Symbol, String> {
    let mut scaled = Vec::new();
    let (mut left, mut right) = (Vec::new(), Vec::new());
    let mut difference = Poly::default();
    for (row, phi) in rows.iter().zip(assumed) {
        let bound = bound(writer, row, phi.clone())?;
        // Each bound becomes `c·left ≤ c·right` (or `=`): a bound `≤` and an
        // equation `left = right` with `c` its multiplier, a bound `≥` with
        // `c` the negated multiplier.
        let c = match (row.weight, bound.op) {
            (Weight::One(m), Op::Le) => m,
            (Weight::One(m), Op::Ge) => m.checked_neg().ok_or("a multiplier overflows")?,
            (Weight::Equality { upper, lower }, Op::Eq) => upper.checked_sub(lower).ok_or("a multiplier overflows")?,
            _ => return Err(format!("the weight of {} does not fit its bound", row.literal)),
        };
        if c == 0 {
            continue;
        }
        let relation = app(op_name(bound.op), vec![eo(&bound.left)?, eo(&bound.right)?]);
        let (rule, sign) = if c > 0 { ("arith_mult_pos", ">") } else { ("arith_mult_neg", "<") };
        let law = writer.step(rule, &[], vec![numeral(c), relation]);
        let sign = writer.step("evaluate", &[], vec![app(sign, vec![numeral(c), numeral(0)])]);
        let sign = writer.step("true_elim", &[&sign], vec![]);
        let both = writer.step("and_intro", &[&sign, &bound.proof], vec![]);
        scaled.push(writer.step("modus_ponens", &[&both, &law], vec![]));
        left.push(app("*", vec![numeral(c), eo(&bound.left)?]));
        right.push(app("*", vec![numeral(c), eo(&bound.right)?]));
        difference = difference.add(c, &Poly::of(&bound.left)?)?.add(c.checked_neg().ok_or("a multiplier overflows")?, &Poly::of(&bound.right)?)?;
    }
    // The sum is `L ≤ R` with `L − R` a positive number `d`.
    let d = difference.constant;
    if !difference.coefficients.is_empty() || d <= 0 || scaled.is_empty() {
        return Err("the bounds of a Farkas lemma do not sum to a false comparison of constants".to_string());
    }
    let (l, r) = (app("+", left), app("+", right));
    let sum_relation = app("<=", vec![l.clone(), r.clone()]);
    let premises: Vec<&Symbol> = scaled.iter().collect();
    let sum = writer.command(false, Some(sum_relation.clone()), "arith_sum_ub", &premises, vec![]);
    let one = || numeral(1);
    let difference = app("=", vec![app("*", vec![one(), app("-", vec![l, r])]), app("*", vec![one(), app("-", vec![numeral(d), numeral(0)])])]);
    let normalized = writer.step("arith_poly_norm", &[], vec![difference]);
    let constant = app("<=", vec![numeral(d), numeral(0)]);
    let same = writer.step("arith_poly_norm_rel", &[&normalized], vec![app("=", vec![sum_relation, constant.clone()])]);
    let value = writer.step("evaluate", &[], vec![constant]);
    let falsity = writer.step("trans", &[&same, &value], vec![]);
    Ok(writer.command(false, Some(boolean(false)), "eq_resolve", &[&sum, &falsity], vec![]))
}

impl Derivation {
    /// The body of the CPC proof of the derivation, for the problem whose
    /// assertions [`super::problem`] writes: the commands that follow the
    /// `include` of the signature and the `reference` to the problem.
    pub fn cpc(&self) -> Result<Script, String> {
        let mut writer = Writer { commands: Vec::new(), next: 0 };
        let mut ids: Vec<Symbol> = Vec::with_capacity(self.steps.len());
        // The assumptions first, each once.
        let mut assumed: Vec<Option<Symbol>> = vec![None; self.assertions.len()];
        for step in &self.steps {
            if let How::Assume(k) = step.how {
                if assumed[k].is_none() {
                    let name = symbol(&format!("@h{}", k + 1));
                    writer.commands.push(Command::Assume { name: name.clone(), formula: eo(&self.assertions[k])? });
                    assumed[k] = Some(name);
                }
            }
        }
        for step in &self.steps {
            let id = match &step.how {
                How::Assume(k) => assumed[*k].clone().unwrap_or_else(|| unreachable!("each assumption is written above")),
                How::Definition(definition, term) => {
                    let t = eo(term)?;
                    match definition {
                        Definition::AndPos(i) => writer.step("cnf_and_pos", &[], vec![t, numeral(*i as i128)]),
                        Definition::AndNeg => writer.step("cnf_and_neg", &[], vec![t]),
                        Definition::OrPos => writer.step("cnf_or_pos", &[], vec![t]),
                        Definition::OrNeg(i) => writer.step("cnf_or_neg", &[], vec![t, numeral(*i as i128)]),
                        Definition::ImpliesPos => writer.step("cnf_implies_pos", &[], vec![t]),
                        Definition::ImpliesNeg1 => writer.step("cnf_implies_neg1", &[], vec![t]),
                        Definition::ImpliesNeg2 => writer.step("cnf_implies_neg2", &[], vec![t]),
                        Definition::True => {
                            let same = writer.step("refl", &[], vec![boolean(true)]);
                            writer.step("true_elim", &[&same], vec![])
                        }
                        Definition::False => {
                            let same = writer.step("refl", &[], vec![boolean(false)]);
                            writer.step("false_elim", &[&same], vec![])
                        }
                    }
                }
                How::Unwrap { premise, inner } => writer.unwrap(&ids[*premise].clone(), eo(inner)?),
                How::Factor(premise) => writer.step("factoring", &[&ids[*premise].clone()], vec![]),
                How::Resolve { left, right, pivot, polarity } => writer.step("resolution", &[&ids[*left].clone(), &ids[*right].clone()], vec![boolean(*polarity), eo(pivot)?]),
                How::Farkas(rows) => {
                    let mut assumed = Vec::new();
                    for row in rows {
                        // The negation of the literal.
                        let atom = eo(&row.relation_term())?;
                        assumed.push(writer.assume_push(if row.positive { app("not", vec![atom]) } else { atom }));
                    }
                    let contradiction = farkas(&mut writer, rows, &assumed)?;
                    let mut clause = writer.close(assumed.len(), contradiction);
                    // The negation of an assumed `(not R)` is `(not (not R))`.
                    for row in rows.iter().filter(|r| r.positive) {
                        clause = writer.unwrap(&clause, eo(&row.relation_term())?);
                    }
                    clause
                }
                How::Trichotomy { sum, value } => {
                    let (s, v) = (eo(sum)?, eo(value)?);
                    let equal = app("=", vec![s.clone(), v.clone()]);
                    let differs = writer.assume_push(app("not", vec![equal.clone()]));
                    let at_most = writer.assume_push(app("<=", vec![s.clone(), v.clone()]));
                    let at_least = writer.assume_push(app("<=", vec![v.clone(), s.clone()]));
                    let flipped = writer.step("arith-elim-leq", &[], vec![v, s]);
                    let at_least = writer.step("eq_resolve", &[&at_least, &flipped], vec![]);
                    let equal_proof = writer.step("arith_trichotomy", &[&at_most, &at_least], vec![]);
                    let contradiction = writer.command(false, Some(boolean(false)), "contra", &[&equal_proof, &differs], vec![]);
                    let clause = writer.close(3, contradiction);
                    writer.unwrap(&clause, equal)
                }
            };
            ids.push(id);
        }
        // The last step concludes the empty clause, `false`.
        match writer.commands.last_mut() {
            Some(Command::Step(last)) if self.steps.last().is_some_and(|s| s.clause.is_empty()) => last.conclusion = Some(boolean(false)),
            _ => return Err("the derivation does not end with the empty clause".to_string()),
        }
        Ok(Script::new(writer.commands))
    }
}

impl Row {
    /// The comparison of the row's literal.
    fn relation_term(&self) -> smtlib::Term {
        apply(op_name(self.relation.op), vec![self.relation.left.clone(), self.relation.right.clone()])
    }
}
