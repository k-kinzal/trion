//! Writes the questions that are decided as SMT-LIB 2.7 and as MoXI, so that
//! an external solver or model checker answers the question that is
//! reported.
//!
//! Every script is built from the abstract syntax of the `smtlib` and
//! `moxi` crates and printed by their printers. The crates model the
//! grammar only: whether a script is well sorted in its logic is decided by
//! the tools that read it (cvc5 with `--strict-parsing`, z3, the MoXI sort
//! checker), which trion's tests run on every form. The logic is QF_LIA: the
//! atoms are Boolean constants and the quantities integer constants.
//!
//! The symbols come from a table, [`Names`]: each atom that is not a
//! comparison is named by its own text, and each quantity (an attribute with
//! its unit) by `num:attribute:unit`, as a quoted symbol where the text
//! needs one. A character that a quoted symbol cannot hold (`|`, `\`)
//! becomes `_`; a name that another entry or a symbol of the logic already
//! has gets the first free suffix ` #2`, ` #3`, …. The table therefore gives
//! distinct entries distinct symbols by construction, whatever their text,
//! and the legend that the files carry as comments says what each name that
//! differs from its text stands for.
//!
//! The entries are named in the order of their first occurrence in the
//! questions, which the document fixes, and the table starts from the same
//! symbols of the logic every time. A name, its suffix included, therefore
//! depends only on the document: two runs on the same document write the
//! same names.

use moxi::{CheckAttribute, CheckSystem, Condition, ConditionKind, DefineSystem, Query};
use smtlib::command::{Command, Script};
use smtlib::lexicon::{Numeral, SpecConstant};
use smtlib::term::{Identifier, NonEmpty, QualIdentifier, SortedVar};
use smtlib::{Sort, Symbol, Term};
use std::collections::{HashMap, HashSet};
use trion_solver::{Atom, Cmp, Formula, Quantity, Witness};

/// The logic of every script.
pub const LOGIC: &str = "QF_LIA";

/// The symbols of QF_LIA's theories (Core and Ints, SMT-LIB 2.7), which no
/// constant of a question may take.
const LOGIC_SYMBOLS: &[&str] = &["true", "false", "not", "=>", "and", "or", "xor", "=", "distinct", "ite", "-", "+", "*", "div", "mod", "abs", "<=", "<", ">=", ">", "divisible"];

/// The symbol of each atom and of each quantity of a set of questions.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Names {
    atoms: Vec<(Atom, Symbol)>,
    quantities: Vec<(Quantity, Symbol)>,
    atom_index: HashMap<Atom, usize>,
    quantity_index: HashMap<Quantity, usize>,
    /// Every name given, and its next-state name `name'` (MoXI), so that
    /// no name is the next-state name of another.
    taken: HashSet<String>,
}

/// A sum of quantities with their coefficients, a comparison and a bound.
type Comparison = (Vec<(Quantity, i64)>, Cmp, i64);

/// The terms and the comparison of a numeric atom.
fn numeric(atom: &Atom) -> Option<Comparison> {
    match atom {
        Atom::Num { attr, unit, cmp, n } => Some((vec![((attr.clone(), unit.clone()), 1)], *cmp, *n)),
        Atom::Lin { terms, unit, cmp, n } => Some((terms.iter().map(|(attr, coef)| ((attr.clone(), unit.clone()), *coef)).collect(), *cmp, *n)),
        _ => None,
    }
}

/// The text of a quantity, as its name is made from it.
fn quantity_text(quantity: &Quantity) -> String {
    format!("num:{}:{}", quantity.0, quantity.1)
}

/// `text` with the characters that a quoted symbol cannot hold (`|`, `\`
/// and those that are neither printable nor white space, SMT-LIB 2.7 §3.1)
/// and a leading `@` or `.` (reserved for solvers) replaced by `_`, and
/// line breaks and tabs by a space, so that a comment line can hold it.
fn symbol_text(text: &str) -> String {
    let mut out: String = text
        .chars()
        .map(|c| match c {
            '|' | '\\' => '_',
            '\n' | '\r' | '\t' => ' ',
            c if c.is_control() => '_',
            c => c,
        })
        .collect();
    if out.starts_with('@') || out.starts_with('.') {
        out.replace_range(0..1, "_");
    }
    out
}

impl Names {
    /// The table of the atoms and quantities of `questions`, in the order
    /// of their first occurrence.
    pub fn of(questions: &[&[Formula]]) -> Names {
        let mut names = Names { taken: LOGIC_SYMBOLS.iter().map(|s| s.to_string()).collect(), ..Names::default() };
        for formula in questions.iter().flat_map(|q| q.iter()) {
            formula.atoms(true, &mut |atom, _| names.add(atom));
        }
        names
    }

    /// A name for `text` that no entry has: the text itself when it is free,
    /// otherwise the first free `text #k`.
    fn fresh(&mut self, text: &str) -> Symbol {
        let base = symbol_text(text);
        let mut candidate = base.clone();
        let mut k = 1;
        while self.taken.contains(&candidate) || self.taken.contains(&format!("{candidate}'")) {
            k += 1;
            candidate = format!("{base} #{k}");
        }
        self.taken.insert(format!("{candidate}'"));
        self.taken.insert(candidate.clone());
        Symbol::new(&candidate).unwrap_or_else(|_| unreachable!("symbol_text leaves only characters of a quoted symbol"))
    }

    fn add(&mut self, atom: &Atom) {
        match numeric(atom) {
            Some((terms, _, _)) => {
                for (quantity, _) in terms {
                    if !self.quantity_index.contains_key(&quantity) {
                        let name = self.fresh(&quantity_text(&quantity));
                        self.quantity_index.insert(quantity.clone(), self.quantities.len());
                        self.quantities.push((quantity, name));
                    }
                }
            }
            None => {
                if !self.atom_index.contains_key(atom) {
                    let name = self.fresh(&atom.to_string());
                    self.atom_index.insert(atom.clone(), self.atoms.len());
                    self.atoms.push((atom.clone(), name));
                }
            }
        }
    }

    /// The Boolean constant of an atom that is not a comparison.
    pub fn atom(&self, atom: &Atom) -> Option<Symbol> {
        self.atom_index.get(atom).map(|k| self.atoms[*k].1.clone())
    }

    /// The integer constant of a quantity.
    pub fn quantity(&self, quantity: &Quantity) -> Option<Symbol> {
        self.quantity_index.get(quantity).map(|k| self.quantities[*k].1.clone())
    }

    /// Each symbol with its sort, Booleans first.
    pub fn symbols(&self) -> Vec<(Symbol, Sort)> {
        let atoms = self.atoms.iter().map(|(_, s)| (s.clone(), Sort::bool()));
        atoms.chain(self.quantities.iter().map(|(_, s)| (s.clone(), Sort::int()))).collect()
    }

    /// The symbols that `formulas` use, with their sorts, in table order.
    fn used(&self, formulas: &[Formula]) -> Vec<(Symbol, Sort)> {
        let only = Names::of(&[formulas]);
        let mut atoms: Vec<usize> = only.atoms.iter().filter_map(|(a, _)| self.atom_index.get(a).copied()).collect();
        let mut quantities: Vec<usize> = only.quantities.iter().filter_map(|(q, _)| self.quantity_index.get(q).copied()).collect();
        atoms.sort_unstable();
        quantities.sort_unstable();
        let atoms = atoms.into_iter().map(|k| (self.atoms[k].1.clone(), Sort::bool()));
        atoms.chain(quantities.into_iter().map(|k| (self.quantities[k].1.clone(), Sort::int()))).collect()
    }

    /// The legend: each symbol whose name is not the text of what it stands
    /// for, with that text, one per line.
    pub fn legend(&self) -> Vec<String> {
        let one_line = |text: &str| text.replace(['\n', '\r'], " ");
        let atoms = self.atoms.iter().map(|(a, s)| (s, a.to_string()));
        let quantities = self.quantities.iter().map(|(q, s)| (s, quantity_text(q)));
        atoms.chain(quantities).filter(|(s, text)| s.as_str() != text).map(|(s, text)| format!("{} stands for {}", s.to_text(&smtlib::Dialect::strict()), one_line(&text))).collect()
    }

    /// The term of an atom.
    pub(super) fn atom_term(&self, atom: &Atom) -> Result<Term, String> {
        let Some((terms, cmp, n)) = numeric(atom) else {
            return self.atom(atom).map(constant).ok_or_else(|| format!("the atom {atom} has no symbol"));
        };
        let mut parts = Vec::new();
        for (quantity, coefficient) in terms {
            let x = constant(self.quantity(&quantity).ok_or_else(|| format!("the quantity {} has no symbol", quantity.0))?);
            parts.push(if coefficient == 1 { x } else { apply("*", vec![integer(coefficient), x]) });
        }
        let sum = match parts.len() {
            0 => integer(0),
            1 => parts.remove(0),
            _ => apply("+", parts),
        };
        let operator = match cmp {
            Cmp::Eq => "=",
            Cmp::Ge => ">=",
            Cmp::Le => "<=",
            Cmp::Gt => ">",
            Cmp::Lt => "<",
        };
        Ok(apply(operator, vec![sum, integer(n)]))
    }

    /// The term of a formula: `and` and `or` of fewer than two parts are
    /// `true`, `false` or the part itself.
    pub fn term(&self, formula: &Formula) -> Result<Term, String> {
        Ok(match formula {
            Formula::True => boolean(true),
            Formula::Atom(atom) => self.atom_term(atom)?,
            Formula::Not(inner) => not(self.term(inner)?),
            Formula::And(items) => junction("and", true, items.iter().map(|i| self.term(i)).collect::<Result<_, _>>()?),
            Formula::Or(items) => junction("or", false, items.iter().map(|i| self.term(i)).collect::<Result<_, _>>()?),
            Formula::Implies(a, b) => apply("=>", vec![self.term(a)?, self.term(b)?]),
        })
    }

    /// The assertions of the problem of a question: its formulas, or, with
    /// a witness, the check of the witness. The check asserts the value that
    /// the witness gives to each symbol of the formulas (`p` or `(not p)`,
    /// `(= x v)`), and then `(not (and formulas…))`: it is unsatisfiable
    /// exactly when the values make every formula true, and since the values
    /// are equations on distinct constants and hold in some model, a
    /// refutation of the check shows the question satisfiable.
    pub fn assertions(&self, formulas: &[Formula], witness: Option<&Witness>) -> Vec<Formula> {
        let Some(witness) = witness else { return formulas.to_vec() };
        let used: HashSet<Symbol> = self.used(formulas).into_iter().map(|(s, _)| s).collect();
        let mut out = Vec::new();
        for (atom, value) in witness.atoms() {
            if self.atom(&atom).is_some_and(|p| used.contains(&p)) {
                let stated = Formula::Atom(atom);
                out.push(if value { stated } else { Formula::not(stated) });
            }
        }
        for ((attr, unit), value) in witness.quantities() {
            if self.quantity(&(attr.clone(), unit.clone())).is_some_and(|x| used.contains(&x)) {
                out.push(Formula::Atom(Atom::Num { attr, unit, cmp: Cmp::Eq, n: value }));
            }
        }
        out.push(Formula::not(Formula::And(formulas.to_vec())));
        out
    }
}

/// The term of a symbol alone.
pub(super) fn constant(symbol: Symbol) -> Term {
    Term::Identifier(QualIdentifier::plain(Identifier::simple(symbol)))
}

/// The application of the theory symbol `name` to `args`, which its callers
/// never leave empty.
pub(super) fn apply(name: &str, args: Vec<Term>) -> Term {
    let function = QualIdentifier::plain(Identifier::simple(Symbol::new(name).unwrap_or_else(|_| unreachable!("{name} is a symbol of the logic"))));
    Term::Application(function, NonEmpty::new(args).unwrap_or_else(|| unreachable!("{name} is applied to at least one term")))
}

pub(super) fn not(term: Term) -> Term {
    apply("not", vec![term])
}

/// `true` or `false`.
pub(super) fn boolean(value: bool) -> Term {
    constant(Symbol::new(if value { "true" } else { "false" }).unwrap_or_else(|_| unreachable!()))
}

/// The integer `i`: the numeral, or `(- n)` for a negative value (Ints).
fn integer(i: i64) -> Term {
    number(i128::from(i))
}

/// [`integer`] for a value of any width: the multipliers of a refutation.
pub(super) fn number(i: i128) -> Term {
    let numeral = Term::Constant(SpecConstant::Numeral(Numeral::new(&i.unsigned_abs().to_string()).unwrap_or_else(|_| unreachable!("the digits of a number are a numeral"))));
    if i >= 0 {
        numeral
    } else {
        apply("-", vec![numeral])
    }
}

/// `and` or `or` of `parts`: the unit (`true` for `and`, `false` for `or`)
/// when there is none, the part itself when there is one.
fn junction(name: &str, unit: bool, mut parts: Vec<Term>) -> Term {
    match parts.len() {
        0 => boolean(unit),
        1 => parts.remove(0),
        _ => apply(name, parts),
    }
}

/// What one check of a script asks, and the answer it is expected to have.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Check {
    /// Question `k` (from 1): are its formulas satisfiable together?
    Question(usize),
    /// The witness of question `k`: is there a model of the witness's
    /// values in which a formula of the question is false? `unsat` shows
    /// that the values make every formula true.
    Witness(usize),
}

/// A script with its checks: the commands of each check, after the common
/// declarations, and the answer each is expected to have.
#[derive(Debug, Clone)]
pub struct Questions {
    /// The symbols and what they stand for.
    pub names: Names,
    /// The whole script.
    pub script: Script,
    /// The checks, in the order of their `check-sat`, with the expected
    /// answer (`true` for `sat`).
    pub checks: Vec<(Check, bool)>,
    /// For each check, the index in `script.commands` of its first command.
    starts: Vec<usize>,
}

/// The commands of a script, starting with `(set-logic QF_LIA)`.
struct Writer {
    commands: Vec<Command>,
}

impl Writer {
    fn new() -> Writer {
        Writer { commands: vec![Command::SetLogic(Symbol::new(LOGIC).unwrap_or_else(|_| unreachable!()))] }
    }

    fn declare(&mut self, symbols: &[(Symbol, Sort)]) {
        self.commands.extend(symbols.iter().map(|(symbol, sort)| Command::DeclareConst(symbol.clone(), sort.clone())));
    }

    /// `(push 1)`, the assertions, `(check-sat)` and `(pop 1)`.
    fn check(&mut self, assertions: Vec<Term>) {
        self.commands.push(Command::Push(1u64.into()));
        self.commands.extend(assertions.into_iter().map(Command::Assert));
        self.commands.push(Command::CheckSat);
        self.commands.push(Command::Pop(1u64.into()));
    }

    fn finish(self) -> Script {
        Script::new(self.commands)
    }
}

/// One script with every question between `(push 1)` and `(pop 1)`, each
/// with its `(check-sat)`, and after them, for each question that a witness
/// answers, the check of the witness: its values asserted with `(not (and
/// formulas…))`, which is `unsat` exactly when the values make every
/// formula true. That they do shows the question satisfiable, since the
/// values are equations on distinct constants and hold in some model. The
/// commands are those of SMT-LIB 2.7: `declare-const` (§4.2.3), `push` and
/// `pop` (§4.2.2), `assert` (§4.2.4) and `check-sat` (§4.2.5), whose answer
/// `unsat` means that no model of the logic satisfies the assertions.
/// `expected[k]` is `Some(true)` for a satisfiable question, `Some(false)`
/// for an unsatisfiable one, `None` for one without an answer.
pub fn questions(questions: &[&[Formula]], expected: &[Option<bool>], witnesses: &[Option<&Witness>]) -> Result<Questions, String> {
    let names = Names::of(questions);
    let mut writer = Writer::new();
    writer.declare(&names.symbols());
    let mut checks = Vec::new();
    let mut starts = Vec::new();
    for (k, formulas) in questions.iter().enumerate() {
        starts.push(writer.commands.len());
        writer.check(formulas.iter().map(|f| names.term(f)).collect::<Result<_, _>>()?);
        checks.push((Check::Question(k + 1), expected.get(k).copied().flatten().unwrap_or(false)));
    }
    for (k, formulas) in questions.iter().enumerate() {
        let Some(witness) = witnesses.get(k).copied().flatten() else { continue };
        starts.push(writer.commands.len());
        writer.check(names.assertions(formulas, Some(witness)).iter().map(|f| names.term(f)).collect::<Result<_, _>>()?);
        checks.push((Check::Witness(k + 1), false));
    }
    Ok(Questions { names, script: writer.finish(), checks, starts })
}

/// The questions alone, as the external prover is asked them: each between
/// `(push 1)` and `(pop 1)`, with the conjunction of its formulas asserted
/// once and its `(check-sat)`. The answer is that of [`questions`], whose
/// script asserts the formulas one by one: a set of assertions is
/// satisfiable exactly when their conjunction is (SMT-LIB 2.7, §4.2.4).
pub fn asked(questions: &[&[Formula]]) -> Result<Script, String> {
    let names = Names::of(questions);
    let mut writer = Writer::new();
    writer.declare(&names.symbols());
    for formulas in questions {
        writer.check(vec![names.term(&Formula::And(formulas.to_vec()))?]);
    }
    Ok(writer.finish())
}

impl Questions {
    /// The text of the script: a header with the expected answers (its
    /// first line), the title and the legend, and a comment before each
    /// check.
    pub fn text(&self, title: &str) -> String {
        let word = |sat: bool| if sat { "sat" } else { "unsat" };
        // The answers come first, where a reader of the file finds them.
        let mut out = format!("; the expected answers, in order: {}\n; {title}\n", self.checks.iter().map(|(_, sat)| word(*sat)).collect::<Vec<_>>().join(" "));
        if self.checks.iter().any(|(check, _)| matches!(check, Check::Witness(_))) {
            out.push_str("; a witness check asserts the values of a satisfying assignment and the negation of the question's formulas: unsat shows that the values make every formula true\n");
        }
        for line in self.names.legend() {
            out.push_str(&format!("; {line}\n"));
        }
        let first: HashMap<usize, usize> = self.starts.iter().enumerate().map(|(at, start)| (*start, at)).collect();
        for (i, command) in self.script.commands().iter().enumerate() {
            if let Some(&at) = first.get(&i) {
                let (check, sat) = self.checks[at];
                match check {
                    Check::Question(k) => out.push_str(&format!("; question {k}: expected {}\n", word(sat))),
                    Check::Witness(k) => out.push_str(&format!("; the witness of question {k}: expected {}\n", word(sat))),
                }
            }
            out.push_str(&format!("{command}\n"));
        }
        out
    }
}

/// One question as a standalone problem: the declarations of its symbols,
/// its assertions ([`Names::assertions`]: its formulas, or with a witness
/// the check of the witness) and one `(check-sat)`. Either kind is
/// unsatisfiable, and a proof format that states refutations proves it.
pub fn problem(names: &Names, formulas: &[Formula], witness: Option<&Witness>) -> Result<Script, String> {
    let mut writer = Writer::new();
    writer.declare(&names.used(formulas));
    for assertion in names.assertions(formulas, witness) {
        writer.commands.push(Command::Assert(names.term(&assertion)?));
    }
    writer.commands.push(Command::CheckSat);
    Ok(writer.finish())
}

/// Questions over their own formulas as one SMT-LIB script: the legend of
/// its symbols as comments, then the commands of [`questions`], without
/// expected answers or witnesses. For the callers that read the questions
/// only; every formula of trion has a term, and an error is a defect of
/// trion.
pub fn script_of(asked: &[&[Formula]]) -> String {
    match questions(asked, &[], &[]) {
        Ok(q) => q.names.legend().iter().map(|line| format!("; {line}\n")).chain(q.script.commands().iter().map(|c| format!("{c}\n"))).collect(),
        Err(problem) => panic!("{problem}"),
    }
}

/// The next-state name of a variable: `x'` (MoXI, "Atomic Systems").
fn primed(variable: &Symbol) -> Symbol {
    Symbol::new(&format!("{}'", variable.as_str())).unwrap_or_else(|_| unreachable!("a name with a quote added is a symbol"))
}

/// The questions as MoXI ("MoXI — A Model Checking Intermediate Language
/// (Draft)", the document that the `moxi` crate models): each question is
/// a system and a query of its own. The trace of a question is already
/// unrolled, so the system has no time of its own. Its local variables are
/// the symbols of the question; `:init` is `true`, so that every valuation
/// is an initial state, and `:trans` is `x' = x` for every variable `x`, so
/// that each step keeps the state and the reachable states are exactly the
/// initial ones ("Atomic System Semantics": a trace starts in a state that
/// satisfies the initial condition and each step satisfies the transition
/// relation). The query asks whether a reachable state satisfies the
/// conjunction of the question's formulas ("Check-system Semantics", a
/// `:reachable` condition), which is therefore exactly whether the question
/// is satisfiable: a model checker that answers the queries answers the
/// questions. The script is built with the constructors of the `moxi`
/// crate, which model the grammar only; its text must read back to the
/// script. [`moxi_text`] writes it with the answer that each query is
/// expected to have.
pub fn moxi_script(asked: &[&[Formula]]) -> Result<(Names, moxi::Script), String> {
    let names = Names::of(asked);
    let moxi_error = |e: moxi::Error| format!("the MoXI writer: {e}");
    let mut commands = vec![moxi::Command::SetLogic(Symbol::new(LOGIC).unwrap_or_else(|_| unreachable!()))];
    let symbol = |s: &str| Symbol::new(s).unwrap_or_else(|_| unreachable!("{s} is a symbol"));
    for (k, formulas) in asked.iter().enumerate() {
        let locals: Vec<SortedVar> = names.used(formulas).into_iter().map(|(variable, sort)| SortedVar::new(variable, sort)).collect();
        let kept: Vec<Term> = locals.iter().map(|v| apply("=", vec![constant(primed(v.variable())), constant(v.variable().clone())])).collect();
        let name = symbol(&format!("question{}", k + 1));
        let system = DefineSystem::new(name.clone()).with_local(locals.clone()).and_then(|s| s.with_init(boolean(true))).and_then(|s| s.with_trans(junction("and", true, kept))).map_err(moxi_error)?;
        let holds = Condition::new(ConditionKind::Reachable, symbol("holds"), names.term(&Formula::And(formulas.to_vec()))?).map_err(moxi_error)?;
        let check = CheckSystem::new(name).with_local(locals).map_err(moxi_error)?.with_attribute(CheckAttribute::Condition(holds)).with_attribute(CheckAttribute::Query(Query::new(symbol("asked"), vec![symbol("holds")])));
        commands.push(moxi::Command::DefineSystem(Box::new(system)));
        commands.push(moxi::Command::CheckSystem(Box::new(check)));
    }
    let script = moxi::Script::new(commands);
    // The text reads back to the same script.
    match script.to_string().parse::<moxi::Script>() {
        Ok(read) if read == script => Ok((names, script)),
        Ok(_) => Err("the MoXI text does not read back to the script that was written".to_string()),
        Err(e) => Err(format!("the MoXI text does not read back: {e}")),
    }
}

/// The text of [`moxi_script`]: the legend, and before each system the answer its
/// query is expected to have.
pub fn moxi_text(names: &Names, script: &moxi::Script, expected: &[bool], title: &str) -> String {
    let mut out = format!("; {title}\n");
    for line in names.legend() {
        out.push_str(&format!("; {line}\n"));
    }
    let mut question = 0;
    for command in script.commands() {
        if let moxi::Command::DefineSystem(_) = command {
            question += 1;
            let reachable = expected.get(question - 1).copied().unwrap_or(false);
            out.push_str(&format!("; question {question}: expected {}\n", if reachable { "reachable (satisfiable)" } else { "unreachable (unsatisfiable)" }));
        }
        out.push_str(&format!("{command}\n"));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use std::collections::BTreeMap;

    fn text() -> impl Strategy<Value = String> {
        prop::sample::select(vec!["API", "API|x", "API_x", "x", "Act", "Act(API|x)", "a b", "|", "\\", "", "message@0", "time@1", "and", "true", "x'", "@x", "a #2"]).prop_map(str::to_string)
    }

    fn atom() -> impl Strategy<Value = Atom> {
        let cmp = prop::sample::select(vec![Cmp::Eq, Cmp::Ge, Cmp::Le, Cmp::Gt, Cmp::Lt]);
        prop_oneof![
            (text(), text()).prop_map(|(attr, value)| Atom::Dom { attr, value }),
            (text(), text()).prop_map(|(attr, value)| Atom::Val { attr, value }),
            text().prop_map(|key| Atom::Act { key }),
            text().prop_map(|key| Atom::Forbid { key }),
            text().prop_map(|key| Atom::Discouraged { key }),
            text().prop_map(|key| Atom::Event { key }),
            text().prop_map(|key| Atom::Config { key }),
            (text(), text()).prop_map(|(subject, role)| Atom::Role { subject, role }),
            (text(), text()).prop_map(|(first, second)| Atom::Before { first, second }),
            (text(), prop::collection::vec(text(), 0..3)).prop_map(|(name, args)| Atom::Rel { name, args }),
            (text(), text(), cmp.clone(), -5i64..5).prop_map(|(attr, unit, cmp, n)| Atom::Num { attr, unit, cmp, n }),
            (prop::collection::vec((text(), -3i64..3), 0..3), text(), cmp, -5i64..5).prop_map(|(terms, unit, cmp, n)| Atom::Lin { terms, unit, cmp, n }),
        ]
    }

    proptest! {
        // Distinct atoms never share a symbol, nor do distinct quantities,
        // and the script of any formulas over them is accepted.
        #[test]
        fn names_are_injective(atoms in prop::collection::vec(atom(), 1..12)) {
            let formulas: Vec<Formula> = atoms.iter().cloned().map(Formula::Atom).collect();
            let names = Names::of(&[formulas.as_slice()]);
            let mut seen: BTreeMap<Symbol, Atom> = BTreeMap::new();
            for atom in atoms.iter().filter(|a| numeric(a).is_none()) {
                let p = names.atom(atom).unwrap();
                if let Some(other) = seen.insert(p.clone(), atom.clone()) {
                    prop_assert_eq!(&other, atom, "{} names two atoms", p);
                }
            }
            let mut quantities: BTreeMap<Symbol, Quantity> = BTreeMap::new();
            for (quantity, _) in atoms.iter().filter_map(numeric).flat_map(|(terms, _, _)| terms) {
                let x = names.quantity(&quantity).unwrap();
                prop_assert!(seen.keys().all(|p| *p != x));
                if let Some(other) = quantities.insert(x.clone(), quantity.clone()) {
                    prop_assert_eq!(other, quantity, "{} names two quantities", x);
                }
            }
            // No name is that of a symbol of the logic, nor the next-state
            // name of another.
            let all: Vec<String> = names.symbols().into_iter().map(|(s, _)| s.as_str().to_string()).collect();
            for name in &all {
                prop_assert!(!LOGIC_SYMBOLS.contains(&name.as_str()), "{} is a symbol of the logic", name);
                prop_assert!(!all.contains(&format!("{name}'")), "{}' is a name", name);
            }
            let written = questions(&[formulas.as_slice(), &[Formula::Or(formulas.clone()), Formula::And(Vec::new())]], &[], &[]);
            prop_assert!(written.is_ok(), "{:?}", written.as_ref().err());
            // The text reads back to the script.
            let script = written.unwrap().script;
            prop_assert_eq!(&Script::parse(&script.to_string()).unwrap(), &script);
            let written = moxi_script(&[formulas.as_slice(), &[Formula::Or(formulas.clone())], &[]]);
            prop_assert!(written.is_ok(), "{:?}", written.err());
        }
    }

    #[test]
    fn padding_is_gone() {
        let a = Formula::Atom(Atom::Act { key: "API|store".to_string() });
        let script = script_of(&[&[Formula::And(vec![]), Formula::And(vec![a.clone()]), Formula::Or(vec![]), Formula::Or(vec![a.clone(), Formula::True])]]);
        assert!(!script.contains("(and true") && !script.contains("(or false") && !script.contains("(+ 0"), "{script}");
        assert!(script.contains("(assert true)") && script.contains("(assert |Act(API_store)|)") && script.contains("(assert false)") && script.contains("(assert (or |Act(API_store)| true))"), "{script}");
    }
}
