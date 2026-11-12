//! Writes the formulas that are decided as SMT-LIB 2, so that an external
//! solver such as z3 answers the question that is reported.

use super::Proof;
use trion_solver::Status;
use trion_solver::{Atom, Cmp, Formula};
use std::collections::BTreeSet;
use std::sync::Arc;

fn symbol(raw: &str) -> String {
    let safe: String = raw.chars().map(|c| if c == '|' || c == '\\' { '_' } else { c }).collect();
    format!("|{safe}|")
}

fn num_var(attr: &str, unit: &str) -> String {
    symbol(&format!("num:{attr}:{unit}"))
}

fn operator(cmp: Cmp) -> &'static str {
    match cmp {
        Cmp::Eq => "=",
        Cmp::Ge => ">=",
        Cmp::Le => "<=",
        Cmp::Gt => ">",
        Cmp::Lt => "<",
    }
}

/// SMT-LIB writes a negative number as an application of `-`.
fn number(n: i64) -> String {
    if n < 0 {
        format!("(- {})", n.unsigned_abs())
    } else {
        n.to_string()
    }
}

fn term(f: &Formula) -> String {
    match f {
        Formula::True => "true".to_string(),
        Formula::Atom(Atom::Num { attr, unit, cmp, n }) => format!("({} {} {})", operator(*cmp), num_var(attr, unit), number(*n)),
        Formula::Atom(Atom::Lin { terms, unit, cmp, n }) => {
            let sum: Vec<String> = terms.iter().map(|(attr, coef)| format!("(* {} {})", number(*coef), num_var(attr, unit))).collect();
            format!("({} (+ 0 {}) {})", operator(*cmp), sum.join(" "), number(*n))
        }
        Formula::Atom(a) => symbol(&a.to_string()),
        Formula::Not(x) => format!("(not {})", term(x)),
        Formula::And(xs) => format!("(and true {})", xs.iter().map(term).collect::<Vec<_>>().join(" ")),
        Formula::Or(xs) => format!("(or false {})", xs.iter().map(term).collect::<Vec<_>>().join(" ")),
        Formula::Implies(a, b) => format!("(=> {} {})", term(a), term(b)),
    }
}

fn collect(f: &Formula, bools: &mut BTreeSet<String>, ints: &mut BTreeSet<String>) {
    match f {
        Formula::True => {}
        Formula::Atom(Atom::Num { attr, unit, .. }) => {
            ints.insert(num_var(attr, unit));
        }
        Formula::Atom(Atom::Lin { terms, unit, .. }) => ints.extend(terms.iter().map(|(attr, _)| num_var(attr, unit))),
        Formula::Atom(a) => {
            bools.insert(symbol(&a.to_string()));
        }
        Formula::Not(x) => collect(x, bools, ints),
        Formula::And(xs) | Formula::Or(xs) => xs.iter().for_each(|x| collect(x, bools, ints)),
        Formula::Implies(a, b) => {
            collect(a, bools, ints);
            collect(b, bools, ints);
        }
    }
}

/// Writes the formulas that are decided: the background and each contract
/// over the trace. A recommendation is no part of the status, so it is
/// written as a comment and not asserted.
pub(crate) fn decided_to_smt2(background: &[Formula], contracts: &[(String, Formula, bool)]) -> String {
    let (mut bools, mut ints) = (BTreeSet::new(), BTreeSet::new());
    for f in background.iter().chain(contracts.iter().map(|(_, f, _)| f)) {
        collect(f, &mut bools, &mut ints);
    }
    let mut out = String::from("(set-option :produce-unsat-cores true)\n(set-logic QF_LIA)\n");
    for b in &bools {
        out.push_str(&format!("(declare-const {b} Bool)\n"));
    }
    for i in &ints {
        out.push_str(&format!("(declare-const {i} Int)\n"));
    }
    for f in background {
        out.push_str(&format!("(assert {})\n", term(f)));
    }
    for (i, (id, f, recommendation)) in contracts.iter().enumerate() {
        if *recommendation {
            out.push_str(&format!("; {id}: a recommendation, not asserted\n; {}\n", term(f)));
        } else {
            out.push_str(&format!("; {id}\n(assert (! {} :named g{i}))\n", term(f)));
        }
    }
    out.push_str("(check-sat)\n");
    out
}

/// One question of a proof, as a second solver can be asked it.
pub struct Query {
    /// What the question decides, for a message.
    pub name: String,
    /// The numbers of its formulas in the group that holds it.
    pub formulas: Vec<usize>,
    /// The certified answer of this run.
    pub status: Status,
}

/// The questions of a proof that are asked over one pool of formulas.
pub struct QueryGroup {
    pool: Arc<Vec<Formula>>,
    pub queries: Vec<Query>,
}

impl QueryGroup {
    /// A formula of the group as an SMT-LIB term, as [`QueryGroup::script`] writes it.
    pub fn term(&self, formula: usize) -> String {
        term(&self.pool[formula])
    }

    /// The questions of the group as one script: each formula that a
    /// question names is defined once, and each question asserts its
    /// formulas between `(push 1)` and `(pop 1)` and asks `(check-sat)`. A
    /// solver prints one answer for each question, in their order.
    pub fn script(&self) -> String {
        let used: BTreeSet<usize> = self.queries.iter().flat_map(|q| &q.formulas).copied().collect();
        let (mut bools, mut ints) = (BTreeSet::new(), BTreeSet::new());
        for &id in &used {
            collect(&self.pool[id], &mut bools, &mut ints);
        }
        let mut out = String::from("(set-logic QF_LIA)\n");
        for b in &bools {
            out.push_str(&format!("(declare-const {b} Bool)\n"));
        }
        for i in &ints {
            out.push_str(&format!("(declare-const {i} Int)\n"));
        }
        for &id in &used {
            out.push_str(&format!("(define-fun f{id} () Bool {})\n", term(&self.pool[id])));
        }
        for query in &self.queries {
            out.push_str("(push 1)\n");
            for id in &query.formulas {
                out.push_str(&format!("(assert f{id})\n"));
            }
            out.push_str("(check-sat)\n(pop 1)\n");
        }
        out
    }
}

impl Proof {
    /// Every question that this proof rests on, grouped by the pool of
    /// formulas that it is asked over: the questions of the inventory, the
    /// status of each consistency example, and each question of the reader.
    /// A group without a question is left out.
    pub fn query_groups(&self) -> Vec<QueryGroup> {
        let mut groups = Vec::new();
        let mut add = |pool: Arc<Vec<Formula>>, queries: Vec<Query>| {
            if !queries.is_empty() {
                groups.push(QueryGroup { pool, queries });
            }
        };
        let inventory = self.questions().into_iter().enumerate().map(|(n, q)| Query { name: if n == 0 { "status".to_string() } else { format!("question {n}") }, formulas: q.query.clone(), status: q.status() }).collect();
        add(self.pool.clone(), inventory);
        for example in &self.examples {
            add(example.pool.clone(), example.questions().into_iter().enumerate().map(|(n, q)| Query { name: if n == 0 { format!("example {}", example.name) } else { format!("example {}, question {n}", example.name) }, formulas: q.query.clone(), status: q.status() }).collect());
        }
        // A question of the reader holds its own formulas.
        for (number, relation) in self.relations.iter().enumerate() {
            for (index, query) in relation.queries.iter().enumerate() {
                let pool = query.all();
                let formulas = (0..pool.len()).collect();
                add(Arc::new(pool), vec![Query { name: format!("relation {number}.{index}"), formulas, status: query.answer.status }]);
            }
        }
        groups
    }
}
