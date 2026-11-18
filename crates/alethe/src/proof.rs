//! The concrete syntax of proofs (§2.1, Figure 2): commands and proofs.
//!
//! ```text
//! ⟨proof⟩              ≔ ⟨proof_command⟩*
//! ⟨proof_command⟩      ≔ (assume ⟨symbol⟩ ⟨proof_term⟩ ⟨attribute⟩*)
//!                       | (step ⟨symbol⟩ ⟨clause⟩ :rule ⟨symbol⟩ ⟨premises_annotation⟩?
//!                               ⟨args_annotation⟩? ⟨attribute⟩*)
//!                       | (anchor :step ⟨symbol⟩ ⟨context_annotation⟩? ⟨attribute⟩*)
//!                       | (define-fun ⟨function_def⟩)
//! ⟨clause⟩             ≔ (cl ⟨proof_term⟩*)
//! ⟨premises_annotation⟩ ≔ :premises (⟨symbol⟩+)
//! ⟨args_annotation⟩     ≔ :args (⟨step_arg⟩+)
//! ⟨context_annotation⟩  ≔ :args (⟨context_assignment⟩+)
//! ⟨context_assignment⟩  ≔ ⟨sorted_var⟩ | (:= ⟨sorted_var⟩ ⟨proof_term⟩)
//! ```
//!
//! The syntax tree keeps the grammar's invariants: the fields are private,
//! the constructors check every ⟨symbol⟩, ⟨proof_term⟩ and sort they are
//! given ([`crate::term::validate`]) and refuse an extra attribute that
//! uses a predefined keyword, and the annotations that the grammar writes
//! with `+` hold a [`NonEmpty`] list or are absent. They also refuse a
//! command whose text would nest deeper than the reader's limit
//! ([`crate::dialect`]). Every value of these types
//! therefore prints to text that [`Proof::parse`] reads back to an equal
//! value.
//!
//! Decisions where the text leaves a choice:
//!
//! - **Step arguments are proof terms.** Figure 2 writes
//!   `⟨step_arg⟩ ≔ ⟨symbol⟩ | ( ⟨symbol⟩ ⟨proof_term⟩ )`, but every example
//!   of the document gives terms (`:args (1.0 -1.0)`, Example 11.1;
//!   `:args ((f a) b)`, Example 21.1; `:args (1.0 1/4)`, Example 11.2), §2
//!   says "the arguments are either terms or tuples", and the tuple shape
//!   `(x t)` cannot be told apart from the application `(x t)`. The tuple
//!   form `(:= x t)` was removed from `forall_inst` (changelog, "Breaking
//!   changes"), so this crate reads arguments as terms only, as Carcara
//!   does (`src/parser/mod.rs`, `parse_step_command`, `:args` read with
//!   `parse_term`).
//! - **The order of the predefined annotations is strict** (§2.1: "the
//!   order in which those must be printed is strict"): `:rule`, then
//!   `:premises`, then `:args`. A predefined keyword that appears again
//!   among the extra attributes is an error, not an extra attribute, so
//!   that no premise or argument is silently ignored.
//! - **`:premises ()` and `:args ()` are errors**: the grammar has ⟨symbol⟩+
//!   and ⟨step_arg⟩+, and §2.1 says the annotation is skipped when empty.
//! - **`:discharge`.** Not in the specification, but written by cvc5 and
//!   veriT on `subproof` steps and read by Carcara (`src/parser/mod.rs`,
//!   `parse_step_command`): `:discharge ( ⟨symbol⟩+ )` directly after
//!   `:rule`/`:premises`/`:args` is kept in [`Step::discharge`].
//! - **Rule names.** `:rule ⟨symbol⟩`; the rule `let` (Rule 91) is spelled
//!   with an SMT-LIB reserved word, so a reserved word is accepted as a rule
//!   name too (as Carcara does, `src/parser/mod.rs`, `parse_step_command`),
//!   and printed bare.
//! - **Extra attributes** after the predefined ones are kept in order and
//!   printed back (§2.1: "A consumer of Alethe proofs must be able to parse
//!   proofs that contain such annotations"); `assume` takes them as well
//!   (changelog: "Allow arbitrary extra annotations in assume commands").
//!
//! What the grammar does not state is not checked here: whether indices
//! are unique, whether premises refer to earlier commands, whether anchors
//! are closed, whether terms are well sorted, and whether a step follows
//! from its premises by its rule. Those are the business of a proof
//! checker such as Carcara.

use crate::error::{Error, ErrorKind, Result};
use crate::term::{self as proof_term, dialect, Symbols};
use smtlib::command::FunctionDef;
use smtlib::lexicon::{Keyword, Reserved, Symbol};
use smtlib::sexpr::{read_all, Atom, SExpr, Spanned};
use smtlib::term::{Attribute, NonEmpty, SortedVar, Term};
use smtlib::Position;
use std::fmt;

fn non_empty<T>(items: Vec<T>, node: &Spanned, annotation: &str) -> Result<NonEmpty<T>> {
    NonEmpty::new(items).ok_or_else(|| Error::syntax(node.position(), format!("{annotation} lists at least one item; when there is none the annotation is omitted (Figure 2, §2.1)")))
}

fn predefined_attribute(attributes: &[Attribute], predefined: &[&str]) -> Result<()> {
    match attributes.iter().find(|a| predefined.iter().any(|p| a.keyword().is(p))) {
        Some(a) => Err(Error::new(ErrorKind::Construction, format!("{} is a predefined annotation and cannot be an extra attribute", a.keyword()))),
        None => proof_term::validate_attributes_at(attributes, 1, Symbols::Check),
    }
}

/// Checks the terms of a clause or of `:args`, two parentheses deep.
fn validate_terms(terms: &[Term]) -> Result<()> {
    terms.iter().try_for_each(|t| proof_term::validate_term_at(t, 2, Symbols::Check))
}

fn validate_symbols(symbols: &[Symbol]) -> Result<()> {
    symbols.iter().try_for_each(proof_term::validate_symbol)
}

/// An element of the context an anchor pushes (§2, "Contexts"): a fixed
/// variable, or a mapping of a variable to a term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ContextAssignment {
    /// `(x S)`: fixes the variable `x`.
    Fixed(SortedVar),
    /// `(:= (x S) t)`: maps `x` to `t`.
    Mapping(SortedVar, Term),
}

impl ContextAssignment {
    /// The variable fixed or mapped.
    pub fn variable(&self) -> &SortedVar {
        match self {
            ContextAssignment::Fixed(v) | ContextAssignment::Mapping(v, _) => v,
        }
    }

    fn validate(&self) -> Result<()> {
        match self {
            ContextAssignment::Fixed(v) => proof_term::validate_var_at(v, 2, Symbols::Check),
            ContextAssignment::Mapping(v, t) => {
                proof_term::validate_var_at(v, 3, Symbols::Check)?;
                proof_term::validate_term_at(t, 3, Symbols::Check)
            }
        }
    }

    fn to_sexpr(&self) -> SExpr {
        match self {
            ContextAssignment::Fixed(v) => v.to_sexpr(),
            ContextAssignment::Mapping(v, t) => SExpr::List(vec![SExpr::keyword(keyword("=")), v.to_sexpr(), t.to_sexpr()]),
        }
    }

    fn from_spanned(node: &Spanned) -> Result<ContextAssignment> {
        let items = node.expect_list("a context assignment: ⟨sorted_var⟩ or (:= ⟨sorted_var⟩ ⟨proof_term⟩)")?;
        if items.first().and_then(Spanned::as_keyword).is_some_and(|k| k.is("=")) {
            if items.len() != 3 {
                return Err(node.expected("(:= ⟨sorted_var⟩ ⟨proof_term⟩)").into());
            }
            if items[1].as_symbol().is_some() {
                return Err(Error::syntax(items[1].position(), "a mapping names its variable with its sort, (:= (x S) t); the form (:= x t) was removed (changelog, \"Add the sort to all variables in contexts\")"));
            }
            let var = SortedVar::from_spanned(&items[1])?;
            proof_term::validate_var_at(&var, 3, Symbols::Checked).map_err(|e| e.or_at(items[1].position()))?;
            return Ok(ContextAssignment::Mapping(var, proof_term::from_spanned_at(&items[2], 3)?));
        }
        let var = SortedVar::from_spanned(node)?;
        proof_term::validate_var_at(&var, 2, Symbols::Checked).map_err(|e| e.or_at(node.position()))?;
        Ok(ContextAssignment::Fixed(var))
    }
}

/// An `assume` command: `(assume id term attributes…)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assume {
    id: Symbol,
    term: Term,
    attributes: Vec<Attribute>,
}

impl Assume {
    /// The assumption `term` with index `id`.
    pub fn new(id: Symbol, term: Term) -> Result<Assume> {
        proof_term::validate_symbol(&id)?;
        proof_term::validate_term_at(&term, 1, Symbols::Check)?;
        Ok(Assume { id, term, attributes: Vec::new() })
    }

    /// This assumption with `attribute` appended to its extra attributes.
    pub fn with_attribute(mut self, attribute: Attribute) -> Result<Assume> {
        predefined_attribute(std::slice::from_ref(&attribute), &[])?;
        self.attributes.push(attribute);
        Ok(self)
    }

    /// The index.
    pub fn id(&self) -> &Symbol {
        &self.id
    }

    /// The assumed formula.
    pub fn term(&self) -> &Term {
        &self.term
    }

    /// The extra attributes, in order.
    pub fn attributes(&self) -> &[Attribute] {
        &self.attributes
    }
}

/// A `step` command.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Step {
    id: Symbol,
    clause: Vec<Term>,
    rule: Symbol,
    premises: Option<NonEmpty<Symbol>>,
    args: Option<NonEmpty<Term>>,
    discharge: Option<NonEmpty<Symbol>>,
    attributes: Vec<Attribute>,
}

const STEP_KEYWORDS: [&str; 4] = ["rule", "premises", "args", "discharge"];

impl Step {
    /// The step `id` concluding the clause `(cl clause…)` by `rule`, with
    /// no premises, arguments or attributes. An empty `clause` is the empty
    /// clause.
    pub fn new(id: Symbol, clause: Vec<Term>, rule: Symbol) -> Result<Step> {
        proof_term::validate_symbol(&id)?;
        proof_term::validate_symbol(&rule)?;
        validate_terms(&clause)?;
        Ok(Step { id, clause, rule, premises: None, args: None, discharge: None, attributes: Vec::new() })
    }

    /// This step with `:premises (premises…)`.
    pub fn with_premises(mut self, premises: NonEmpty<Symbol>) -> Result<Step> {
        validate_symbols(&premises)?;
        self.premises = Some(premises);
        Ok(self)
    }

    /// This step with `:args (args…)`.
    pub fn with_args(mut self, args: NonEmpty<Term>) -> Result<Step> {
        validate_terms(&args)?;
        self.args = Some(args);
        Ok(self)
    }

    /// This step with `:discharge (assumptions…)`.
    pub fn with_discharge(mut self, assumptions: NonEmpty<Symbol>) -> Result<Step> {
        validate_symbols(&assumptions)?;
        self.discharge = Some(assumptions);
        Ok(self)
    }

    /// This step with `attribute` appended to its extra attributes; a
    /// predefined keyword (`:rule`, `:premises`, `:args`, `:discharge`) is
    /// a construction error.
    pub fn with_attribute(mut self, attribute: Attribute) -> Result<Step> {
        predefined_attribute(std::slice::from_ref(&attribute), &STEP_KEYWORDS)?;
        self.attributes.push(attribute);
        Ok(self)
    }

    /// The index.
    pub fn id(&self) -> &Symbol {
        &self.id
    }

    /// The literals of the conclusion `(cl …)`; empty for the empty clause.
    pub fn clause(&self) -> &[Term] {
        &self.clause
    }

    /// The rule name.
    pub fn rule(&self) -> &Symbol {
        &self.rule
    }

    /// The premises; empty when `:premises` is absent.
    pub fn premises(&self) -> &[Symbol] {
        self.premises.as_deref().unwrap_or(&[])
    }

    /// The arguments; empty when `:args` is absent.
    pub fn args(&self) -> &[Term] {
        self.args.as_deref().unwrap_or(&[])
    }

    /// The discharged assumptions of `:discharge`; empty when absent.
    pub fn discharge(&self) -> &[Symbol] {
        self.discharge.as_deref().unwrap_or(&[])
    }

    /// The extra attributes, in order.
    pub fn attributes(&self) -> &[Attribute] {
        &self.attributes
    }
}

/// An `anchor` command: `(anchor :step id :args (…) attributes…)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Anchor {
    step: Symbol,
    context: Option<NonEmpty<ContextAssignment>>,
    attributes: Vec<Attribute>,
}

impl Anchor {
    /// The anchor of the subproof that the step `step` concludes, with no
    /// context.
    pub fn new(step: Symbol) -> Result<Anchor> {
        proof_term::validate_symbol(&step)?;
        Ok(Anchor { step, context: None, attributes: Vec::new() })
    }

    /// This anchor with the context `:args (context…)`.
    pub fn with_context(mut self, context: NonEmpty<ContextAssignment>) -> Result<Anchor> {
        context.iter().try_for_each(ContextAssignment::validate)?;
        self.context = Some(context);
        Ok(self)
    }

    /// This anchor with `attribute` appended to its extra attributes; `:step`
    /// and `:args` are construction errors.
    pub fn with_attribute(mut self, attribute: Attribute) -> Result<Anchor> {
        predefined_attribute(std::slice::from_ref(&attribute), &["step", "args"])?;
        self.attributes.push(attribute);
        Ok(self)
    }

    /// The index of the step that concludes the subproof.
    pub fn step(&self) -> &Symbol {
        &self.step
    }

    /// The context the subproof pushes; empty when `:args` is absent.
    pub fn context(&self) -> &[ContextAssignment] {
        self.context.as_deref().unwrap_or(&[])
    }

    /// The extra attributes, in order.
    pub fn attributes(&self) -> &[Attribute] {
        &self.attributes
    }
}

/// A `define-fun` command of a proof.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefineFun {
    definition: FunctionDef,
}

impl DefineFun {
    /// The command `(define-fun …)` of `definition`.
    pub fn new(definition: FunctionDef) -> Result<DefineFun> {
        DefineFun::checked(definition, Symbols::Check)
    }

    fn checked(definition: FunctionDef, symbols: Symbols) -> Result<DefineFun> {
        if symbols == Symbols::Check {
            proof_term::validate_symbol(definition.name())?;
        }
        definition.parameters().iter().try_for_each(|v| proof_term::validate_var_at(v, 2, symbols))?;
        proof_term::validate_sort_at(definition.sort(), 1, symbols)?;
        proof_term::validate_term_at(definition.body(), 1, symbols)?;
        Ok(DefineFun { definition })
    }

    /// The definition.
    pub fn definition(&self) -> &FunctionDef {
        &self.definition
    }
}

/// A command of a proof.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Command {
    /// `(assume …)`.
    Assume(Assume),
    /// `(step …)`.
    Step(Step),
    /// `(anchor …)`.
    Anchor(Anchor),
    /// `(define-fun …)`.
    DefineFun(DefineFun),
}

fn keyword(name: &str) -> Keyword {
    Keyword::new(name).expect("a predefined keyword is a keyword")
}

fn symbol_atom(name: &str) -> SExpr {
    SExpr::symbol(Symbol::new(name).expect("a command name is a symbol"))
}

fn symbols(items: &[Symbol]) -> SExpr {
    SExpr::List(items.iter().cloned().map(SExpr::symbol).collect())
}

/// The S-expression of a rule name: bare when it is an SMT-LIB reserved
/// word (the rule `let`).
fn rule_sexpr(rule: &Symbol) -> SExpr {
    match Reserved::from_name(rule.as_str()) {
        Some(r) => SExpr::reserved(r),
        None => SExpr::symbol(rule.clone()),
    }
}

impl Command {
    /// The index of an `assume` or `step`.
    pub fn id(&self) -> Option<&Symbol> {
        match self {
            Command::Assume(a) => Some(&a.id),
            Command::Step(s) => Some(&s.id),
            _ => None,
        }
    }

    /// The S-expression of this command.
    pub fn to_sexpr(&self) -> SExpr {
        match self {
            Command::Assume(Assume { id, term, attributes }) => {
                let mut items = vec![symbol_atom("assume"), SExpr::symbol(id.clone()), term.to_sexpr()];
                attributes.iter().for_each(|a| a.push_sexprs(&mut items));
                SExpr::List(items)
            }
            Command::Step(step) => {
                let mut clause = vec![symbol_atom("cl")];
                clause.extend(step.clause.iter().map(Term::to_sexpr));
                let mut items = vec![symbol_atom("step"), SExpr::symbol(step.id.clone()), SExpr::List(clause), SExpr::keyword(keyword("rule")), rule_sexpr(&step.rule)];
                if let Some(premises) = &step.premises {
                    items.push(SExpr::keyword(keyword("premises")));
                    items.push(symbols(premises));
                }
                if let Some(args) = &step.args {
                    items.push(SExpr::keyword(keyword("args")));
                    items.push(SExpr::List(args.iter().map(Term::to_sexpr).collect()));
                }
                if let Some(discharge) = &step.discharge {
                    items.push(SExpr::keyword(keyword("discharge")));
                    items.push(symbols(discharge));
                }
                step.attributes.iter().for_each(|a| a.push_sexprs(&mut items));
                SExpr::List(items)
            }
            Command::Anchor(Anchor { step, context, attributes }) => {
                let mut items = vec![symbol_atom("anchor"), SExpr::keyword(keyword("step")), SExpr::symbol(step.clone())];
                if let Some(context) = context {
                    items.push(SExpr::keyword(keyword("args")));
                    items.push(SExpr::List(context.iter().map(ContextAssignment::to_sexpr).collect()));
                }
                attributes.iter().for_each(|a| a.push_sexprs(&mut items));
                SExpr::List(items)
            }
            Command::DefineFun(DefineFun { definition }) => {
                let mut items = vec![SExpr::reserved(Reserved::DefineFun)];
                definition.push_sexprs(&mut items);
                SExpr::List(items)
            }
        }
    }

    /// Reads one command from `text`.
    pub fn parse(text: &str) -> Result<Command> {
        Command::from_spanned(&smtlib::sexpr::read(text, dialect())?)
    }

    /// Reads a command from an S-expression read in [`crate::dialect`].
    pub fn from_spanned(node: &Spanned) -> Result<Command> {
        // Every ⟨symbol⟩ of the command, once, at its own position; the
        // terms, sorts and variables read below are then walked without
        // checking their symbols again.
        proof_term::symbols_in(node)?;
        const WHAT: &str = "a proof command (assume, step, anchor or define-fun)";
        let Some((head, rest)) = node.expect_list(WHAT)?.split_first() else {
            return Err(node.expected(WHAT).into());
        };
        let command = if head.is_reserved(Reserved::DefineFun) {
            let definition = FunctionDef::from_spanned_items(node, rest, dialect())?;
            Command::DefineFun(DefineFun::checked(definition, Symbols::Checked).map_err(|e| e.or_at(node.position()))?)
        } else {
            match head.as_symbol().map(Symbol::as_str) {
                Some("assume") => {
                    if rest.len() < 2 {
                        return Err(Error::syntax(node.position(), "assume takes an index and a term"));
                    }
                    let id = rest[0].expect_symbol("the index of the assume (a symbol)")?.clone();
                    let term = proof_term::from_spanned_at(&rest[1], 1)?;
                    Command::Assume(Assume { id, term, attributes: extra_attributes(&rest[2..], &[])? })
                }
                Some("step") => Command::Step(step_from_spanned(node, rest)?),
                Some("anchor") => Command::Anchor(anchor_from_spanned(node, rest)?),
                _ => return Err(head.expected("assume, step, anchor or define-fun").into()),
            }
        };
        Ok(command)
    }
}

fn anchor_from_spanned(node: &Spanned, rest: &[Spanned]) -> Result<Anchor> {
    let mut i = 0;
    expect_keyword(node, rest, &mut i, "step")?;
    let step = rest.get(i).ok_or_else(|| Error::syntax(node.position(), "anchor :step needs the index of the concluding step"))?.expect_symbol("the index of the concluding step")?.clone();
    i += 1;
    let mut context = None;
    if rest.get(i).and_then(Spanned::as_keyword).is_some_and(|k| k.is("args")) {
        let list_node = rest.get(i + 1).ok_or_else(|| Error::syntax(rest[i].position(), ":args needs a list"))?;
        let items = list_node.expect_list("a list of context assignments")?.iter().map(ContextAssignment::from_spanned).collect::<Result<Vec<_>>>()?;
        context = Some(non_empty(items, list_node, "the :args of an anchor")?);
        i += 2;
    }
    Ok(Anchor { step, context, attributes: extra_attributes(&rest[i..], &["step", "args"])? })
}

fn expect_keyword(node: &Spanned, rest: &[Spanned], i: &mut usize, name: &str) -> Result<()> {
    match rest.get(*i) {
        Some(k) if k.as_keyword().is_some_and(|k| k.is(name)) => {
            *i += 1;
            Ok(())
        }
        Some(other) => Err(other.expected(&format!(":{name}")).into()),
        None => Err(Error::syntax(node.position(), format!("expected :{name}, found the end of the command"))),
    }
}

fn extra_attributes(nodes: &[Spanned], predefined: &[&str]) -> Result<Vec<Attribute>> {
    for node in nodes {
        if let Some(k) = node.as_keyword() {
            if predefined.iter().any(|p| k.is(p)) {
                return Err(Error::syntax(node.position(), format!("{k} is a predefined annotation and is out of order or repeated: the order is strict (§2.1)")));
            }
        }
    }
    Attribute::sequence_from_spanned(nodes).map_err(Error::from)
}

fn symbol_list(node: &Spanned, what: &str, annotation: &str) -> Result<NonEmpty<Symbol>> {
    let items = node.expect_list(what)?.iter().map(|i| Ok(i.expect_symbol("an index (a symbol)")?.clone())).collect::<Result<Vec<_>>>()?;
    non_empty(items, node, annotation)
}

fn step_from_spanned(node: &Spanned, rest: &[Spanned]) -> Result<Step> {
    let id = rest.first().ok_or_else(|| Error::syntax(node.position(), "step takes an index, a clause and :rule"))?.expect_symbol("the index of the step (a symbol)")?.clone();
    let clause_node = rest.get(1).ok_or_else(|| Error::syntax(node.position(), "step needs a clause (cl …)"))?;
    let clause_items = clause_node.expect_list("a clause (cl ⟨proof_term⟩*)")?;
    match clause_items.first() {
        Some(head) if head.as_symbol().is_some_and(|s| s.as_str() == "cl") => {}
        _ => return Err(Error::syntax(clause_node.position(), format!("the conclusion of a step is a clause (cl …), found {}; every step uses cl, even for a unit clause (§2.1)", clause_node.describe()))),
    }
    let clause = clause_items[1..].iter().map(|t| proof_term::from_spanned_at(t, 2)).collect::<Result<Vec<_>>>()?;
    let mut i = 2;
    expect_keyword(node, rest, &mut i, "rule")?;
    let rule_node = rest.get(i).ok_or_else(|| Error::syntax(node.position(), ":rule needs a rule name"))?;
    let rule = match rule_node.as_atom() {
        Some(Atom::Symbol(s)) => s.clone(),
        Some(Atom::Reserved(r)) => Symbol::new(r.as_str())?,
        _ => return Err(rule_node.expected("a rule name (a symbol)").into()),
    };
    i += 1;
    let mut premises = None;
    if rest.get(i).and_then(Spanned::as_keyword).is_some_and(|k| k.is("premises")) {
        let node = rest.get(i + 1).ok_or_else(|| Error::syntax(rest[i].position(), ":premises needs a list"))?;
        premises = Some(symbol_list(node, "a list of premises", ":premises")?);
        i += 2;
    }
    let mut args = None;
    if rest.get(i).and_then(Spanned::as_keyword).is_some_and(|k| k.is("args")) {
        let args_node = rest.get(i + 1).ok_or_else(|| Error::syntax(rest[i].position(), ":args needs a list"))?;
        let items = args_node.expect_list("a list of arguments")?.iter().map(|t| proof_term::from_spanned_at(t, 2)).collect::<Result<Vec<_>>>()?;
        args = Some(non_empty(items, args_node, ":args")?);
        i += 2;
    }
    let mut discharge = None;
    if rest.get(i).and_then(Spanned::as_keyword).is_some_and(|k| k.is("discharge")) {
        let node = rest.get(i + 1).ok_or_else(|| Error::syntax(rest[i].position(), ":discharge needs a list"))?;
        discharge = Some(symbol_list(node, "a list of discharged assumptions", ":discharge")?);
        i += 2;
    }
    let attributes = extra_attributes(&rest[i..], &STEP_KEYWORDS)?;
    Ok(Step { id, clause, rule, premises, args, discharge, attributes })
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_sexpr().to_text(dialect()))
    }
}

/// A proof: a list of commands (§2.1).
///
/// ```
/// let text = "(assume h1 (not p))\n(step t1 (cl) :rule hole :premises (h1))\n";
/// let proof = alethe::Proof::parse(text).unwrap();
/// assert_eq!(proof.commands().len(), 2);
/// assert_eq!(proof.to_text(), text);
/// ```
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Proof {
    commands: Vec<Command>,
}

impl Proof {
    /// The proof made of `commands`, in order.
    pub fn new(commands: Vec<Command>) -> Proof {
        Proof { commands }
    }

    /// The commands, in order.
    pub fn commands(&self) -> &[Command] {
        &self.commands
    }

    /// The commands, in order.
    pub fn into_commands(self) -> Vec<Command> {
        self.commands
    }

    /// Appends `command`.
    pub fn push(&mut self, command: Command) {
        self.commands.push(command);
    }

    /// Reads a proof: a sequence of commands, nothing around them.
    pub fn parse(text: &str) -> Result<Proof> {
        Ok(Proof { commands: Proof::parse_located(text)?.into_iter().map(|(_, c)| c).collect() })
    }

    /// Reads a proof with the position of each command.
    pub fn parse_located(text: &str) -> Result<Vec<(Position, Command)>> {
        read_all(text, dialect())?.iter().map(|node| Ok((node.position(), Command::from_spanned(node)?))).collect()
    }

    /// The text of this proof: one command per line.
    pub fn to_text(&self) -> String {
        let d = dialect();
        let mut out = String::new();
        for command in &self.commands {
            // Writing to a `String` does not fail.
            let _ = command.to_sexpr().write(&mut out, d);
            out.push('\n');
        }
        out
    }
}

impl FromIterator<Command> for Proof {
    fn from_iter<I: IntoIterator<Item = Command>>(iter: I) -> Proof {
        Proof { commands: iter.into_iter().collect() }
    }
}

impl fmt::Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_text())
    }
}
