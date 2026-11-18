//! The abstract syntax of MoXI scripts, its reader and its printer
//! (description.md, "Supported SMT-LIB Commands", "MoXI-specific Commands",
//! "System Definition Command", "System Checking Command").
//!
//! A MoXI script is a sequence of commands. Five are SMT-LIB commands that
//! MoXI adopts (`set-logic`, `declare-sort`, `define-sort`, `declare-const`,
//! `define-fun`); they are read and printed by the `smtlib` crate and kept
//! here as variants of [`Command`], so that no other SMT-LIB command can be
//! represented. Three are MoXI's own: `declare-enum-sort`, `define-system`
//! and `check-system`. Every other command is rejected when read: an
//! SMT-LIB command that MoXI does not adopt as [`ErrorKind::Unsupported`],
//! any other head as [`ErrorKind::Syntax`].
//!
//! The attributes of `define-system` and `check-system` are kept in a
//! normal form. The document makes their order immaterial apart from the
//! constraints it states (the variable declarations first, then the
//! subsystems, then the formulas), so the reader enforces those constraints
//! and the printer writes the attributes in a canonical order; reading
//! printed syntax gives back an equal value. Attributes that "can occur at
//! most once" are `Option`s, so that an absent attribute and an attribute
//! written with an empty value stay distinct; the repeatable ones are
//! sequences in the order written.
//!
//! The reader checks the grammar only. Whether a name is declared, a
//! formula has sort Bool, a primed variable is admitted where it occurs, a
//! subsystem matches the system it instantiates or a query names defined
//! formulas is static semantics, which this crate does not check; the
//! reference tool's sort checker does.
//!
//! Terms, sorts, symbols and sorted variables are those of the `smtlib`
//! crate, read and printed in the MoXI [`dialect`], where `'` may occur in a
//! simple symbol (`x'`, the next-state copy of `x`). They are SMT-LIB 2.6
//! terms: the productions SMT-LIB 2.7 added to the term grammar (`lambda`,
//! the `_` pattern) are rejected as unsupported. (`@` and `->` are symbols
//! in the grammar of both versions; what 2.7 makes of them is theory, not
//! grammar, and not checked.) Every constructor that takes a term or a sort
//! checks it the same way, and also rejects what the reader could not have
//! produced (a constant or binder of another dialect, text nested deeper
//! than the reader accepts), so that every value prints as text that reads
//! back to it.

use crate::error::{Error, ErrorKind, Result};
use crate::validate;
use smtlib::command::FunctionDef;
use smtlib::lexicon::{Dialect, Keyword, Numeral, Reserved, Symbol};
use smtlib::sexpr::{read, read_all, Spanned};
use smtlib::term::SortedVar;
use smtlib::{NonEmpty, Position, Sort, Term};
use std::fmt;
use std::str::FromStr;

/// The deepest nesting of parentheses the readers accept, the command's own
/// included: `smtlib`'s default, [`Dialect::DEFAULT_MAX_DEPTH`]. Deeper text
/// is an [`ErrorKind::Depth`] error at the parenthesis that exceeds it, and
/// a constructor rejects a value whose text would nest deeper in its place.
/// Reading, printing and dropping are iterative and need no limit; the
/// limit keeps the derived traits (`Clone`, `PartialEq`, `Debug`, …), which
/// recurse, within a 2 MiB stack, as the test
/// `deep_terms_within_the_limit_round_trip` checks on such a stack.
pub(crate) const DEPTH_LIMIT: usize = Dialect::DEFAULT_MAX_DEPTH;

/// The dialect MoXI is written in: SMT-LIB with `'` admitted in simple
/// symbols, for next-state variables (description.md, "Atomic Systems":
/// "next-state variables … are denoted by convention by appending ′ to the
/// names of the current-state variables"). Its nesting limit is `smtlib`'s
/// default, [`Dialect::DEFAULT_MAX_DEPTH`]; a deeper text is an
/// [`ErrorKind::Depth`] error.
///
/// ```
/// let d = moxi::dialect();
/// assert!(d.is_simple_symbol("x'"));
/// assert_eq!(d.max_depth(), smtlib::Dialect::DEFAULT_MAX_DEPTH);
/// ```
pub fn dialect() -> Dialect {
    // Not input: the character is a constant. `with_symbol_char` refuses
    // only a character that already has a role in the SMT-LIB lexicon
    // (letters, digits, delimiters, `:`, `#`, `\` and the punctuation simple
    // symbols admit); `'` has none. Should smtlib's rule change, every
    // reader and printer of this crate fails loudly (and the test
    // `dialect_admits_the_prime` with them) instead of silently reading
    // another grammar.
    #[allow(clippy::expect_used)]
    let primed = Dialect::strict().with_symbol_char('\'').expect("' has no role in the SMT-LIB lexicon, so smtlib admits it as a symbol character");
    primed.with_max_depth(DEPTH_LIMIT)
}

/// Reads one term in the MoXI [`dialect`], for building commands.
///
/// ```
/// let trans = moxi::parse_term("(= o' i)")?;
/// assert_eq!(trans.to_text(&moxi::dialect()), "(= o' i)");
/// assert_eq!(moxi::parse_term("(lambda ((x Int)) x)").unwrap_err().kind(), moxi::ErrorKind::Unsupported);
/// # Ok::<(), moxi::Error>(())
/// ```
pub fn parse_term(text: &str) -> Result<Term> {
    let d = dialect();
    term(&read(text, &d)?, 0, &d)
}

/// A MoXI command.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Command {
    /// `(set-logic L)`
    SetLogic(Symbol),
    /// `(declare-sort s n)`
    DeclareSort(Symbol, Numeral),
    /// `(define-sort s (u1 … un) τ)`
    DefineSort(DefineSort),
    /// `(declare-const c σ)`
    DeclareConst(DeclareConst),
    /// `(define-fun f ((x1 σ1) … (xn σn)) σ t)`
    DefineFun(DefineFun),
    /// `(declare-enum-sort s (c1 … cn))`
    DeclareEnumSort(Symbol, Vec<Symbol>),
    /// `(define-system S …)` (boxed: it is much larger than the others)
    DefineSystem(Box<DefineSystem>),
    /// `(check-system S …)` (boxed, likewise)
    CheckSystem(Box<CheckSystem>),
}

/// `(define-sort s (u1 … un) τ)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefineSort {
    name: Symbol,
    parameters: Vec<Symbol>,
    sort: Sort,
}

impl DefineSort {
    /// The definition of `name` with `parameters` as `sort`; `sort` is
    /// checked as described in the [module documentation](self).
    pub fn new(name: Symbol, parameters: Vec<Symbol>, sort: Sort) -> Result<DefineSort> {
        validate::sort(&sort, 1)?;
        Ok(DefineSort { name, parameters, sort })
    }

    /// The defined sort symbol.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// The sort parameters.
    pub fn parameters(&self) -> &[Symbol] {
        &self.parameters
    }

    /// The defining sort.
    pub fn sort(&self) -> &Sort {
        &self.sort
    }
}

/// `(declare-const c σ)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DeclareConst {
    name: Symbol,
    sort: Sort,
}

impl DeclareConst {
    /// The declaration of `name` of `sort`; `sort` is checked as described
    /// in the [module documentation](self).
    pub fn new(name: Symbol, sort: Sort) -> Result<DeclareConst> {
        validate::sort(&sort, 1)?;
        Ok(DeclareConst { name, sort })
    }

    /// The declared constant.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// Its sort.
    pub fn sort(&self) -> &Sort {
        &self.sort
    }
}

/// `(define-fun f ((x1 σ1) … (xn σn)) σ t)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefineFun {
    definition: FunctionDef,
}

impl DefineFun {
    /// The command for `definition`; its sorts and body are checked as
    /// described in the [module documentation](self).
    pub fn new(definition: FunctionDef) -> Result<DefineFun> {
        validate::function_def(&definition, 1)?;
        Ok(DefineFun { definition })
    }

    /// The definition: name, parameters, result sort and body.
    pub fn definition(&self) -> &FunctionDef {
        &self.definition
    }
}

/// `(N (S x1 … y1 …))`, the value of a `:subsys` attribute: a local name for
/// an instance of the system `S` whose inputs are connected to `x…` and
/// whose outputs to `y…`. The document writes the two sequences one after
/// the other; how many of the arguments are inputs is known only from the
/// definition of `S`, so they are kept as one sequence.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Subsystem {
    name: Symbol,
    system: Symbol,
    arguments: Vec<Symbol>,
}

impl Subsystem {
    /// The instance `name` of `system`, connected to `arguments`.
    pub fn new(name: Symbol, system: Symbol, arguments: Vec<Symbol>) -> Subsystem {
        Subsystem { name, system, arguments }
    }

    /// The local synonym `N`.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// The instantiated system `S`.
    pub fn system(&self) -> &Symbol {
        &self.system
    }

    /// The variables `x…` then `y…`.
    pub fn arguments(&self) -> &[Symbol] {
        &self.arguments
    }
}

/// `(define-system S :input … :output … :local … :subsys … :init I :trans T :inv P)`.
///
/// The `with_*` methods check the sorts and terms they are given as
/// described in the [module documentation](self).
///
/// ```
/// use moxi::{parse_term, DefineSystem};
/// use smtlib::{Sort, Symbol, term::SortedVar};
///
/// let var = |name: &str| SortedVar::new(Symbol::new(name).unwrap(), Sort::int());
/// let delay = DefineSystem::new(Symbol::new("Delay").unwrap())
///     .with_input(vec![var("i")])?
///     .with_output(vec![var("o")])?
///     .with_init(parse_term("(= o 0)")?)?
///     .with_trans(parse_term("(= o' i)")?)?;
/// assert!(delay.is_atomic());
/// assert_eq!(moxi::Command::DefineSystem(Box::new(delay)).to_string(), "(define-system Delay\n :input ((i Int))\n :output ((o Int))\n :init (= o 0)\n :trans (= o' i))");
/// # Ok::<(), moxi::Error>(())
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefineSystem {
    name: Symbol,
    input: Option<Vec<SortedVar>>,
    output: Option<Vec<SortedVar>>,
    local: Option<Vec<SortedVar>>,
    subsystems: Vec<Subsystem>,
    init: Option<Term>,
    trans: Option<Term>,
    inv: Option<Term>,
}

impl DefineSystem {
    /// The system `name` with no attribute written.
    pub fn new(name: Symbol) -> DefineSystem {
        DefineSystem { name, input: None, output: None, local: None, subsystems: Vec::new(), init: None, trans: None, inv: None }
    }

    /// This system with `:input vars` (replacing an earlier `:input`).
    pub fn with_input(mut self, vars: Vec<SortedVar>) -> Result<DefineSystem> {
        validate::sorted_vars(&vars, 1)?;
        self.input = Some(vars);
        Ok(self)
    }

    /// This system with `:output vars` (replacing an earlier `:output`).
    pub fn with_output(mut self, vars: Vec<SortedVar>) -> Result<DefineSystem> {
        validate::sorted_vars(&vars, 1)?;
        self.output = Some(vars);
        Ok(self)
    }

    /// This system with `:local vars` (replacing an earlier `:local`).
    pub fn with_local(mut self, vars: Vec<SortedVar>) -> Result<DefineSystem> {
        validate::sorted_vars(&vars, 1)?;
        self.local = Some(vars);
        Ok(self)
    }

    /// This system with `subsystem` appended to its `:subsys` attributes.
    pub fn with_subsystem(mut self, subsystem: Subsystem) -> DefineSystem {
        self.subsystems.push(subsystem);
        self
    }

    /// This system with `:init formula` (replacing an earlier `:init`).
    pub fn with_init(mut self, formula: Term) -> Result<DefineSystem> {
        validate::term(&formula, 1)?;
        self.init = Some(formula);
        Ok(self)
    }

    /// This system with `:trans formula` (replacing an earlier `:trans`).
    pub fn with_trans(mut self, formula: Term) -> Result<DefineSystem> {
        validate::term(&formula, 1)?;
        self.trans = Some(formula);
        Ok(self)
    }

    /// This system with `:inv formula` (replacing an earlier `:inv`).
    pub fn with_inv(mut self, formula: Term) -> Result<DefineSystem> {
        validate::term(&formula, 1)?;
        self.inv = Some(formula);
        Ok(self)
    }

    /// The system's identifier.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// `:input`, if written.
    pub fn input(&self) -> Option<&[SortedVar]> {
        self.input.as_deref()
    }

    /// `:output`, if written.
    pub fn output(&self) -> Option<&[SortedVar]> {
        self.output.as_deref()
    }

    /// `:local`, if written.
    pub fn local(&self) -> Option<&[SortedVar]> {
        self.local.as_deref()
    }

    /// The `:subsys` attributes, in order.
    pub fn subsystems(&self) -> &[Subsystem] {
        &self.subsystems
    }

    /// `:init`, if written.
    pub fn init(&self) -> Option<&Term> {
        self.init.as_ref()
    }

    /// `:trans`, if written.
    pub fn trans(&self) -> Option<&Term> {
        self.trans.as_ref()
    }

    /// `:inv`, if written.
    pub fn inv(&self) -> Option<&Term> {
        self.inv.as_ref()
    }

    /// Whether the system is atomic: it has no `:subsys` attribute
    /// ("Atomic Systems", "Composite Systems").
    pub fn is_atomic(&self) -> bool {
        self.subsystems.is_empty()
    }
}

/// The kinds of named formulas of `check-system`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ConditionKind {
    /// `:assumption`, an environmental assumption.
    Assumption,
    /// `:fairness`, a fairness condition.
    Fairness,
    /// `:reachable`, a state reachability condition.
    Reachable,
    /// `:current`, a state initiality condition.
    Current,
}

impl ConditionKind {
    /// The attribute keyword, without the colon.
    pub fn keyword(self) -> &'static str {
        match self {
            ConditionKind::Assumption => "assumption",
            ConditionKind::Fairness => "fairness",
            ConditionKind::Reachable => "reachable",
            ConditionKind::Current => "current",
        }
    }
}

/// The attribute keyword with its colon: `:assumption`, ….
impl fmt::Display for ConditionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ":{}", self.keyword())
    }
}

/// `:assumption (a A)`, `:fairness (f F)`, `:reachable (r R)` or `:current (c C)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Condition {
    kind: ConditionKind,
    label: Symbol,
    formula: Term,
}

impl Condition {
    /// The formula `formula` of kind `kind`, named `label`; `formula` is
    /// checked as described in the [module documentation](self).
    pub fn new(kind: ConditionKind, label: Symbol, formula: Term) -> Result<Condition> {
        validate::term(&formula, 2)?;
        Ok(Condition { kind, label, formula })
    }

    /// Which attribute.
    pub fn kind(&self) -> ConditionKind {
        self.kind
    }

    /// The identifier queries use.
    pub fn label(&self) -> &Symbol {
        &self.label
    }

    /// The formula.
    pub fn formula(&self) -> &Term {
        &self.formula
    }
}

/// `(q (g1 … gn))`: a query made of the formulas named `g…`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Query {
    name: Symbol,
    formulas: Vec<Symbol>,
}

impl Query {
    /// The query `name` over the formulas labelled `formulas`.
    pub fn new(name: Symbol, formulas: Vec<Symbol>) -> Query {
        Query { name, formulas }
    }

    /// The query's identifier.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// The labels of its formulas.
    pub fn formulas(&self) -> &[Symbol] {
        &self.formulas
    }
}

/// A repeatable attribute of `check-system`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CheckAttribute {
    /// A named formula.
    Condition(Condition),
    /// `:query (q (g…))`
    Query(Query),
    /// `:queries ((q1 (g…)) … (qt (g…)))`
    Queries(NonEmpty<Query>),
}

/// `(check-system S :input … :output … :local … attributes…)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CheckSystem {
    name: Symbol,
    input: Option<Vec<SortedVar>>,
    output: Option<Vec<SortedVar>>,
    local: Option<Vec<SortedVar>>,
    attributes: Vec<CheckAttribute>,
}

impl CheckSystem {
    /// The check of the system `name` with no attribute written.
    pub fn new(name: Symbol) -> CheckSystem {
        CheckSystem { name, input: None, output: None, local: None, attributes: Vec::new() }
    }

    /// This check with `:input vars` (replacing an earlier `:input`); the
    /// sorts are checked as described in the [module documentation](self).
    pub fn with_input(mut self, vars: Vec<SortedVar>) -> Result<CheckSystem> {
        validate::sorted_vars(&vars, 1)?;
        self.input = Some(vars);
        Ok(self)
    }

    /// This check with `:output vars` (replacing an earlier `:output`).
    pub fn with_output(mut self, vars: Vec<SortedVar>) -> Result<CheckSystem> {
        validate::sorted_vars(&vars, 1)?;
        self.output = Some(vars);
        Ok(self)
    }

    /// This check with `:local vars` (replacing an earlier `:local`).
    pub fn with_local(mut self, vars: Vec<SortedVar>) -> Result<CheckSystem> {
        validate::sorted_vars(&vars, 1)?;
        self.local = Some(vars);
        Ok(self)
    }

    /// This check with `attribute` appended to its repeatable attributes.
    pub fn with_attribute(mut self, attribute: CheckAttribute) -> CheckSystem {
        self.attributes.push(attribute);
        self
    }

    /// The checked system.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// `:input`, the renaming of the system's inputs, if written.
    pub fn input(&self) -> Option<&[SortedVar]> {
        self.input.as_deref()
    }

    /// `:output`, the renaming of the system's outputs, if written.
    pub fn output(&self) -> Option<&[SortedVar]> {
        self.output.as_deref()
    }

    /// `:local`, the renaming of the system's local variables, if written.
    pub fn local(&self) -> Option<&[SortedVar]> {
        self.local.as_deref()
    }

    /// The repeatable attributes, in order.
    pub fn attributes(&self) -> &[CheckAttribute] {
        &self.attributes
    }

    /// The named formulas, in order.
    pub fn conditions(&self) -> impl Iterator<Item = &Condition> {
        self.attributes.iter().filter_map(|a| match a {
            CheckAttribute::Condition(c) => Some(c),
            _ => None,
        })
    }

    /// Every query, from `:query` and `:queries`, in order.
    pub fn queries(&self) -> impl Iterator<Item = &Query> {
        self.attributes.iter().flat_map(|a| match a {
            CheckAttribute::Query(q) => std::slice::from_ref(q),
            CheckAttribute::Queries(qs) => &qs[..],
            CheckAttribute::Condition(_) => &[],
        })
    }
}

/// A MoXI script: a sequence of commands.
///
/// ```
/// let script: moxi::Script = "(set-logic QF_LIA)\n(define-system S :output ((o Int)) :init (= o 0))".parse()?;
/// assert_eq!(script.commands().len(), 2);
/// assert_eq!(script.to_string().parse::<moxi::Script>()?, script);
/// # Ok::<(), moxi::Error>(())
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct Script {
    commands: Vec<Command>,
}

impl Script {
    /// The script made of `commands`.
    pub fn new(commands: Vec<Command>) -> Script {
        Script { commands }
    }

    /// The commands, in order.
    pub fn commands(&self) -> &[Command] {
        &self.commands
    }

    /// The commands, by value.
    pub fn into_commands(self) -> Vec<Command> {
        self.commands
    }

    /// Appends `command`.
    pub fn push(&mut self, command: Command) {
        self.commands.push(command);
    }

    /// Reads a script from `text`, with the position of each command; to
    /// read a script alone, use [`str::parse`].
    pub fn parse_located(text: &str) -> Result<Vec<(Position, Command)>> {
        let d = dialect();
        read_all(text, &d)?.iter().map(|node| Ok((node.position(), Command::read(node, &d)?))).collect()
    }
}

impl FromIterator<Command> for Script {
    fn from_iter<I: IntoIterator<Item = Command>>(iter: I) -> Script {
        Script { commands: iter.into_iter().collect() }
    }
}

/// Reads a script: every command of `text`, in the MoXI [`dialect`].
impl FromStr for Script {
    type Err = Error;

    fn from_str(text: &str) -> Result<Script> {
        Ok(Script { commands: Script::parse_located(text)?.into_iter().map(|(_, c)| c).collect() })
    }
}

/// One command per line; each `define-system` and `check-system` attribute
/// on a line of its own.
impl fmt::Display for Script {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for command in &self.commands {
            writeln!(f, "{command}")?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------- reading

/// A syntax error of MoXI's own productions at `node`.
pub(crate) fn syntax(node: &Spanned, message: impl Into<String>) -> Error {
    Error::at(ErrorKind::Syntax, node.position(), message)
}

/// The symbol of `node`, or a syntax error that names `what`.
pub(crate) fn symbol(node: &Spanned, what: &str) -> Result<Symbol> {
    Ok(node.expect_symbol(what)?.clone())
}

/// `(s …)`, the symbols of the list `node`.
fn symbols(node: &Spanned, what: &str) -> Result<Vec<Symbol>> {
    node.expect_list(&format!("a list of {what}"))?.iter().map(|s| symbol(s, what)).collect()
}

/// One attribute read by [`attributes`]: the keyword's node, the keyword,
/// and the value's node.
pub(crate) type Attribute<'a> = (&'a Spanned, Keyword, &'a Spanned);

/// The `:keyword value` pairs of `nodes`, in order. Every attribute of
/// MoXI's commands and responses has a value, so a keyword followed by a
/// keyword or by nothing is an error at the keyword; `what` names the
/// enclosing form.
pub(crate) fn attributes<'a>(nodes: &'a [Spanned], what: &str) -> Result<Vec<Attribute<'a>>> {
    let mut out = Vec::with_capacity(nodes.len() / 2);
    let mut rest = nodes;
    while let Some((at, tail)) = rest.split_first() {
        let keyword = at.expect_keyword(&format!("an attribute of {what} (a keyword)"))?.clone();
        let Some((value, tail)) = tail.split_first().filter(|(v, _)| v.as_keyword().is_none()) else {
            return Err(syntax(at, format!("the attribute {keyword} of {what} needs a value")));
        };
        out.push((at, keyword, value));
        rest = tail;
    }
    Ok(out)
}

/// A term read from `node`, whose text is inside `outer` parentheses.
pub(crate) fn term(node: &Spanned, outer: usize, d: &Dialect) -> Result<Term> {
    let term = Term::from_spanned_in(node, d).map_err(|e| Error::from(e).or_at(node.position()))?;
    validate::term(&term, outer).map_err(|e| e.or_at(node.position()))?;
    Ok(term)
}

/// `((x S) …)` read from `node`, whose text is inside `outer` parentheses.
fn sorted_vars(node: &Spanned, outer: usize) -> Result<Vec<SortedVar>> {
    let vars = node.expect_list("a list of sorted variables ( (⟨symbol⟩ ⟨sort⟩)* )")?.iter().map(|v| SortedVar::from_spanned(v).map_err(|e| Error::from(e).or_at(v.position()))).collect::<Result<Vec<_>>>()?;
    validate::sorted_vars(&vars, outer).map_err(|e| e.or_at(node.position()))?;
    Ok(vars)
}

/// Whether `word` is one of the basic reserved words of SMT-LIB §3.1 rather
/// than a command name (which §3.1 also reserves).
fn is_basic_reserved(word: Reserved) -> bool {
    use Reserved::*;
    matches!(word, Binary | Decimal | Hexadecimal | Numeral | String | Underscore | Bang | As | Lambda | Let | Exists | Forall | Match | Par)
}

impl Command {
    fn read(node: &Spanned, d: &Dialect) -> Result<Command> {
        let items = node.expect_list("a command ( ⟨name⟩ … )")?;
        let Some((head, rest)) = items.split_first() else {
            return Err(node.expected("a command").into());
        };
        if let Some(reserved) = head.as_reserved() {
            if is_basic_reserved(reserved) {
                return Err(head.expected("a command name").into());
            }
            return match reserved {
                Reserved::SetLogic | Reserved::DeclareSort | Reserved::DefineSort | Reserved::DeclareConst | Reserved::DefineFun => smtlib::Command::from_spanned_in(node, d).map_err(Error::from).and_then(|c| Command::from_smtlib(c, head.position())).map_err(|e| e.or_at(node.position())),
                other => Err(Error::at(
                    ErrorKind::Unsupported,
                    head.position(),
                    format!("{other} is an SMT-LIB command that MoXI does not adopt; MoXI adopts set-logic, declare-sort, define-sort, declare-const and define-fun (description.md, \"Supported SMT-LIB Commands\")"),
                )),
            };
        }
        let name = symbol(head, "a command name")?;
        match name.as_str() {
            "declare-enum-sort" => {
                let [sort, values] = rest else {
                    return Err(syntax(node, format!("declare-enum-sort takes a sort symbol and a list of values, found {} argument(s)", rest.len())));
                };
                Ok(Command::DeclareEnumSort(symbol(sort, "the enumeration sort symbol")?, symbols(values, "enumeration values (symbols)")?))
            }
            "define-system" => Ok(Command::DefineSystem(Box::new(define_system(node, rest, d)?))),
            "check-system" => Ok(Command::CheckSystem(Box::new(check_system(node, rest, d)?))),
            other => Err(syntax(head, format!("unknown command {other}: MoXI has set-logic, declare-sort, define-sort, declare-const, define-fun, declare-enum-sort, define-system and check-system"))),
        }
    }

    fn from_smtlib(command: smtlib::Command, at: Position) -> Result<Command> {
        Ok(match command {
            smtlib::Command::SetLogic(l) => Command::SetLogic(l),
            smtlib::Command::DeclareSort(s, n) => Command::DeclareSort(s, n),
            smtlib::Command::DefineSort(s, ps, t) => Command::DefineSort(DefineSort::new(s, ps, t)?),
            smtlib::Command::DeclareConst(c, s) => Command::DeclareConst(DeclareConst::new(c, s)?),
            smtlib::Command::DefineFun(def) => Command::DefineFun(DefineFun::new(def)?),
            other => return Err(Error::at(ErrorKind::Unsupported, at, format!("{} is not an SMT-LIB command MoXI adopts", other.name()))),
        })
    }

    /// The command's name.
    pub fn name(&self) -> &'static str {
        match self {
            Command::SetLogic(_) => "set-logic",
            Command::DeclareSort(..) => "declare-sort",
            Command::DefineSort(_) => "define-sort",
            Command::DeclareConst(_) => "declare-const",
            Command::DefineFun(_) => "define-fun",
            Command::DeclareEnumSort(..) => "declare-enum-sort",
            Command::DefineSystem(_) => "define-system",
            Command::CheckSystem(_) => "check-system",
        }
    }
}

/// Reads exactly one command.
///
/// ```
/// use moxi::{Command, ErrorKind};
/// let command: Command = "(declare-enum-sort Light (on off))".parse()?;
/// assert_eq!(command.name(), "declare-enum-sort");
/// assert_eq!("(assert true)".parse::<Command>().unwrap_err().kind(), ErrorKind::Unsupported);
/// # Ok::<(), moxi::Error>(())
/// ```
impl FromStr for Command {
    type Err = Error;

    fn from_str(text: &str) -> Result<Command> {
        let d = dialect();
        Command::read(&read(text, &d)?, &d)
    }
}

// ---------------------------------------------------------------- printing

/// `(a b …)` from the texts of the items.
pub(crate) fn parenthesized(items: impl IntoIterator<Item = String>) -> String {
    format!("({})", items.into_iter().collect::<Vec<_>>().join(" "))
}

fn sorted_vars_text(vars: &[SortedVar], d: &Dialect) -> String {
    parenthesized(vars.iter().map(|v| v.to_sexpr().to_text(d)))
}

fn query_text(q: &Query, d: &Dialect) -> String {
    format!("({} {})", q.name.to_text(d), parenthesized(q.formulas.iter().map(|g| g.to_text(d))))
}

/// The `:input`, `:output` and `:local` attributes that are written.
fn variable_attributes(input: &Option<Vec<SortedVar>>, output: &Option<Vec<SortedVar>>, local: &Option<Vec<SortedVar>>, d: &Dialect) -> Vec<String> {
    [("input", input), ("output", output), ("local", local)].into_iter().filter_map(|(name, vars)| vars.as_ref().map(|vars| format!(":{name} {}", sorted_vars_text(vars, d)))).collect()
}

/// `(head name` then each attribute on a line of its own, then `)`.
fn write_attributes(f: &mut fmt::Formatter<'_>, head: &str, name: &Symbol, attributes: &[String], d: &Dialect) -> fmt::Result {
    write!(f, "({head} {}", name.to_text(d))?;
    for attribute in attributes {
        write!(f, "\n {attribute}")?;
    }
    f.write_str(")")
}

impl DefineSystem {
    /// The attributes in the canonical order: `:input :output :local`, the
    /// `:subsys` attributes, `:init :trans :inv`.
    fn attribute_texts(&self, d: &Dialect) -> Vec<String> {
        let mut out = variable_attributes(&self.input, &self.output, &self.local, d);
        for s in &self.subsystems {
            let instance = parenthesized(std::iter::once(s.system.to_text(d)).chain(s.arguments.iter().map(|a| a.to_text(d))));
            out.push(format!(":subsys ({} {instance})", s.name.to_text(d)));
        }
        for (name, formula) in [("init", &self.init), ("trans", &self.trans), ("inv", &self.inv)] {
            if let Some(formula) = formula {
                out.push(format!(":{name} {}", formula.to_text(d)));
            }
        }
        out
    }
}

impl CheckSystem {
    /// `:input :output :local`, then the repeatable attributes in order.
    fn attribute_texts(&self, d: &Dialect) -> Vec<String> {
        let mut out = variable_attributes(&self.input, &self.output, &self.local, d);
        for attribute in &self.attributes {
            out.push(match attribute {
                CheckAttribute::Condition(c) => format!("{} ({} {})", c.kind, c.label.to_text(d), c.formula.to_text(d)),
                CheckAttribute::Query(q) => format!(":query {}", query_text(q, d)),
                CheckAttribute::Queries(qs) => format!(":queries {}", parenthesized(qs.iter().map(|q| query_text(q, d)))),
            });
        }
        out
    }
}

/// The text of the command in the MoXI dialect. `define-system` and
/// `check-system` put each attribute on a line of its own; terms are
/// printed on one line. Reading the text gives back an equal command.
impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let d = dialect();
        let adopted = match self {
            Command::SetLogic(l) => smtlib::Command::SetLogic(l.clone()),
            Command::DeclareSort(s, n) => smtlib::Command::DeclareSort(s.clone(), n.clone()),
            Command::DefineSort(c) => smtlib::Command::DefineSort(c.name.clone(), c.parameters.clone(), c.sort.clone()),
            Command::DeclareConst(c) => smtlib::Command::DeclareConst(c.name.clone(), c.sort.clone()),
            Command::DefineFun(c) => smtlib::Command::DefineFun(c.definition.clone()),
            Command::DeclareEnumSort(s, values) => return write!(f, "(declare-enum-sort {} {})", s.to_text(&d), parenthesized(values.iter().map(|v| v.to_text(&d)))),
            Command::DefineSystem(s) => return write_attributes(f, "define-system", &s.name, &s.attribute_texts(&d), &d),
            Command::CheckSystem(c) => return write_attributes(f, "check-system", &c.name, &c.attribute_texts(&d), &d),
        };
        f.write_str(&adopted.to_text(&d))
    }
}

// ------------------------------------------------- define-system, check-system

/// Which group of attributes has been read, for the order constraints.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Phase {
    Variables,
    Subsystems,
    Formulas,
}

fn set_once<T>(slot: &mut Option<T>, value: T, keyword: &Keyword, at: &Spanned, command: &str) -> Result<()> {
    if slot.is_some() {
        let section = if command == "define-system" { "Atomic Systems" } else { "System Checking Command" };
        return Err(syntax(at, format!("the attribute {keyword} occurs twice in {command}; it can occur at most once (description.md, \"{section}\")")));
    }
    *slot = Some(value);
    Ok(())
}

fn define_system(node: &Spanned, rest: &[Spanned], d: &Dialect) -> Result<DefineSystem> {
    let Some((name, attributes_nodes)) = rest.split_first() else {
        return Err(syntax(node, "define-system needs the system's identifier"));
    };
    let mut system = DefineSystem::new(symbol(name, "the system's identifier (a symbol)")?);
    let mut phase = Phase::Variables;
    for (at, keyword, value) in attributes(attributes_nodes, "define-system")? {
        let out_of_order = |required: Phase| {
            let rule = if required == Phase::Variables {
                ":input, :output and :local must occur before :subsys, :init, :trans and :inv"
            } else {
                "every :subsys attribute occurs after :input, :output and :local but before :init, :trans and :inv"
            };
            syntax(at, format!("{keyword} is out of order: {rule} (description.md, \"Atomic Systems\", \"Composite Systems\")"))
        };
        match keyword.name() {
            "input" | "output" | "local" => {
                if phase > Phase::Variables {
                    return Err(out_of_order(Phase::Variables));
                }
                let vars = sorted_vars(value, 1)?;
                let slot = match keyword.name() {
                    "input" => &mut system.input,
                    "output" => &mut system.output,
                    _ => &mut system.local,
                };
                set_once(slot, vars, &keyword, at, "define-system")?;
            }
            "subsys" => {
                if phase > Phase::Subsystems {
                    return Err(out_of_order(Phase::Subsystems));
                }
                phase = Phase::Subsystems;
                system.subsystems.push(subsystem(value)?);
            }
            "init" | "trans" | "inv" => {
                phase = Phase::Formulas;
                let formula = term(value, 1, d)?;
                let slot = match keyword.name() {
                    "init" => &mut system.init,
                    "trans" => &mut system.trans,
                    _ => &mut system.inv,
                };
                set_once(slot, formula, &keyword, at, "define-system")?;
            }
            _ => return Err(syntax(at, format!("{keyword} is not an attribute of define-system: the attributes are :input, :output, :local, :subsys, :init, :trans and :inv"))),
        }
    }
    Ok(system)
}

fn subsystem(value: &Spanned) -> Result<Subsystem> {
    let shape = "a subsystem ( ⟨symbol⟩ ( ⟨symbol⟩ ⟨symbol⟩* ) )";
    let [name, instance] = value.expect_list(shape)? else {
        return Err(value.expected(shape).into());
    };
    let instance_shape = "an instance ( ⟨system⟩ ⟨variable⟩* )";
    let Some((system, arguments)) = instance.expect_list(instance_shape)?.split_first() else {
        return Err(instance.expected(instance_shape).into());
    };
    Ok(Subsystem {
        name: symbol(name, "the subsystem's local name (a symbol)")?,
        system: symbol(system, "the name of a system (a symbol)")?,
        arguments: arguments.iter().map(|a| symbol(a, "a variable of the enclosing system (a symbol)")).collect::<Result<Vec<_>>>()?,
    })
}

fn query(value: &Spanned) -> Result<Query> {
    let shape = "a query ( ⟨symbol⟩ ( ⟨symbol⟩* ) )";
    let [name, formulas] = value.expect_list(shape)? else {
        return Err(value.expected(shape).into());
    };
    Ok(Query { name: symbol(name, "the query's identifier (a symbol)")?, formulas: symbols(formulas, "formula identifiers")? })
}

fn check_system(node: &Spanned, rest: &[Spanned], d: &Dialect) -> Result<CheckSystem> {
    let Some((name, attribute_nodes)) = rest.split_first() else {
        return Err(syntax(node, "check-system needs the identifier of a system"));
    };
    let mut check = CheckSystem::new(symbol(name, "the identifier of a system (a symbol)")?);
    for (at, keyword, value) in attributes(attribute_nodes, "check-system")? {
        let kind = match keyword.name() {
            "input" | "output" | "local" => {
                if !check.attributes.is_empty() {
                    return Err(syntax(at, format!("{keyword} is out of order: :input, :output and :local have to come before the other attributes (description.md, \"System Checking Command\")")));
                }
                let vars = sorted_vars(value, 1)?;
                let slot = match keyword.name() {
                    "input" => &mut check.input,
                    "output" => &mut check.output,
                    _ => &mut check.local,
                };
                set_once(slot, vars, &keyword, at, "check-system")?;
                continue;
            }
            "assumption" => ConditionKind::Assumption,
            "fairness" => ConditionKind::Fairness,
            "reachable" => ConditionKind::Reachable,
            "current" => ConditionKind::Current,
            "query" => {
                check.attributes.push(CheckAttribute::Query(query(value)?));
                continue;
            }
            "queries" => {
                let queries = value.expect_list("a list of queries ( ( ⟨symbol⟩ ( ⟨symbol⟩* ) )+ )")?.iter().map(query).collect::<Result<Vec<_>>>()?;
                let queries = NonEmpty::new(queries).ok_or_else(|| syntax(value, ":queries needs at least one query"))?;
                check.attributes.push(CheckAttribute::Queries(queries));
                continue;
            }
            _ => {
                return Err(syntax(
                    at,
                    format!("{keyword} is not an attribute of check-system: the attributes are :input, :output, :local, :assumption, :fairness, :reachable, :current, :query and :queries"),
                ))
            }
        };
        let shape = format!("a named formula ( ⟨symbol⟩ ⟨term⟩ ) for {kind}");
        let [label, formula] = value.expect_list(&shape)? else {
            return Err(value.expected(&shape).into());
        };
        check.attributes.push(CheckAttribute::Condition(Condition { kind, label: symbol(label, "a formula identifier (a symbol)")?, formula: term(formula, 2, d)? }));
    }
    Ok(check)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dialect_admits_the_prime() {
        assert!(dialect().is_symbol_char('\''));
        assert!(dialect().is_simple_symbol("x'"));
    }
}
