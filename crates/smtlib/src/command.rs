//! Commands and scripts (§3.11, Figure 3.7), with the option and info-flag
//! categories of Figures 3.8 and 3.9.
//!
//! A [`Command`] follows Figure 3.7 one variant per production, including
//! the commands SMT-LIB 2.7 added (`declare-sort-parameter`,
//! `define-const`) and its `check-sat-assuming` with arbitrary terms
//! (§1.1.2). The predefined options of Figure 3.8 and the predefined info
//! flags of Figure 3.9 are alternatives of the same productions as an arbitrary
//! `⟨attribute⟩` or `⟨keyword⟩` (the grammar itself reads `:print-success 5`
//! as an attribute), so the syntax keeps them as attributes and keywords;
//! [`SolverOption::classify`] and [`InfoFlag::classify`] give the typed view.
//!
//! ```
//! use smtlib::{Command, Script};
//!
//! let script: Script = "(set-logic QF_LIA) (declare-const x Int) (assert (> x 0)) (check-sat)".parse().unwrap();
//! assert_eq!(script.commands().len(), 4);
//! assert!(matches!(script.commands()[3], Command::CheckSat));
//! assert_eq!(script.to_string(), "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n");
//! ```

use crate::error::{Error, Position, Result};
use crate::lexicon::{Dialect, Keyword, Numeral, Reserved, SpecConstant, StringLiteral, Symbol};
use crate::read;
use crate::sexpr::{read as read_sexpr, read_all, SExpr, Spanned};
use crate::term::{Attribute, AttributeValue, NonEmpty, Sort, SortedVar, Term};
use std::fmt;

/// `( ⟨symbol⟩ ⟨numeral⟩ )`: a datatype name and its arity.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SortDec {
    symbol: Symbol,
    arity: Numeral,
}

impl SortDec {
    /// `(symbol arity)`.
    pub fn new(symbol: Symbol, arity: Numeral) -> SortDec {
        SortDec { symbol, arity }
    }

    /// The datatype.
    pub fn symbol(&self) -> &Symbol {
        &self.symbol
    }

    /// Its arity.
    pub fn arity(&self) -> &Numeral {
        &self.arity
    }
}

/// `( ⟨symbol⟩ ⟨sort⟩ )`: a selector and its sort.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SelectorDec {
    symbol: Symbol,
    sort: Sort,
}

impl SelectorDec {
    /// `(symbol sort)`.
    pub fn new(symbol: Symbol, sort: Sort) -> SelectorDec {
        SelectorDec { symbol, sort }
    }

    /// The selector.
    pub fn symbol(&self) -> &Symbol {
        &self.symbol
    }

    /// The sort it selects.
    pub fn sort(&self) -> &Sort {
        &self.sort
    }
}

/// `( ⟨symbol⟩ ⟨selector_dec⟩* )`: a constructor and its selectors.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstructorDec {
    symbol: Symbol,
    selectors: Vec<SelectorDec>,
}

impl ConstructorDec {
    /// `(symbol selectors…)`.
    pub fn new(symbol: Symbol, selectors: Vec<SelectorDec>) -> ConstructorDec {
        ConstructorDec { symbol, selectors }
    }

    /// The constructor.
    pub fn symbol(&self) -> &Symbol {
        &self.symbol
    }

    /// Its selectors.
    pub fn selectors(&self) -> &[SelectorDec] {
        &self.selectors
    }
}

/// `( ⟨constructor_dec⟩+ ) | ( par ( ⟨symbol⟩+ ) ( ⟨constructor_dec⟩+ ) )`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DatatypeDec {
    parameters: Vec<Symbol>,
    constructors: NonEmpty<ConstructorDec>,
}

impl DatatypeDec {
    /// The declaration with sort `parameters` (the `par` form when there
    /// are some) and `constructors`.
    pub fn new(parameters: Vec<Symbol>, constructors: NonEmpty<ConstructorDec>) -> DatatypeDec {
        DatatypeDec { parameters, constructors }
    }

    /// The sort parameters; empty for the form without `par`.
    pub fn parameters(&self) -> &[Symbol] {
        &self.parameters
    }

    /// The constructors.
    pub fn constructors(&self) -> &NonEmpty<ConstructorDec> {
        &self.constructors
    }
}

/// `( ⟨symbol⟩ ( ⟨sorted_var⟩* ) ⟨sort⟩ )`: a function declared by
/// `define-funs-rec`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionDec {
    name: Symbol,
    parameters: Vec<SortedVar>,
    sort: Sort,
}

impl FunctionDec {
    /// `(name (parameters…) sort)`.
    pub fn new(name: Symbol, parameters: Vec<SortedVar>, sort: Sort) -> FunctionDec {
        FunctionDec { name, parameters, sort }
    }

    /// The function.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// Its parameters.
    pub fn parameters(&self) -> &[SortedVar] {
        &self.parameters
    }

    /// Its result sort.
    pub fn sort(&self) -> &Sort {
        &self.sort
    }

    /// The S-expression `(name (parameters…) sort)`.
    pub fn to_sexpr(&self) -> SExpr {
        SExpr::List(vec![SExpr::symbol(self.name.clone()), sorted_vars(&self.parameters), self.sort.to_sexpr()])
    }

    /// Reads `(name (parameters…) sort)`.
    pub fn from_spanned(node: &Spanned) -> Result<FunctionDec> {
        match node.as_list() {
            Some([name, params, sort]) => Ok(FunctionDec { name: name.expect_symbol("a function name")?.clone(), parameters: sorted_var_list(params)?, sort: Sort::from_spanned(sort)? }),
            _ => Err(node.expected("a function declaration ( ⟨symbol⟩ ( ⟨sorted_var⟩* ) ⟨sort⟩ )")),
        }
    }
}

/// `⟨symbol⟩ ( ⟨sorted_var⟩* ) ⟨sort⟩ ⟨term⟩`: a function definition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionDef {
    name: Symbol,
    parameters: Vec<SortedVar>,
    sort: Sort,
    body: Term,
}

impl FunctionDef {
    /// `name (parameters…) sort body`.
    pub fn new(name: Symbol, parameters: Vec<SortedVar>, sort: Sort, body: Term) -> FunctionDef {
        FunctionDef { name, parameters, sort, body }
    }

    /// The function.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// Its parameters.
    pub fn parameters(&self) -> &[SortedVar] {
        &self.parameters
    }

    /// Its result sort.
    pub fn sort(&self) -> &Sort {
        &self.sort
    }

    /// Its body.
    pub fn body(&self) -> &Term {
        &self.body
    }

    /// Appends the four S-expressions of the definition to `out`.
    pub fn push_sexprs(&self, out: &mut Vec<SExpr>) {
        out.push(SExpr::symbol(self.name.clone()));
        out.push(sorted_vars(&self.parameters));
        out.push(self.sort.to_sexpr());
        out.push(self.body.to_sexpr());
    }

    /// Reads the four items of a definition, `items`, of the command or
    /// response `node`, in `dialect`.
    pub fn from_spanned_items(node: &Spanned, items: &[Spanned], dialect: &Dialect) -> Result<FunctionDef> {
        match items {
            [name, params, sort, body] => Ok(FunctionDef { name: name.expect_symbol("a function name")?.clone(), parameters: sorted_var_list(params)?, sort: Sort::from_spanned(sort)?, body: Term::from_spanned_in(body, dialect)? }),
            _ => Err(node.expected("a function definition ⟨symbol⟩ ( ⟨sorted_var⟩* ) ⟨sort⟩ ⟨term⟩")),
        }
    }
}

/// A command of Figure 3.7. Each variant holds the parts of its production
/// in the order of the text; the two lists of `declare-datatypes` and of
/// `define-funs-rec`, which have the same length, are held as pairs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Command {
    /// `(assert t)`
    Assert(Term),
    /// `(check-sat)`
    CheckSat,
    /// `(check-sat-assuming (t…))`: SMT-LIB 2.7 admits any terms, where 2.6
    /// admitted only literals `p` and `(not p)`.
    CheckSatAssuming(Vec<Term>),
    /// `(declare-const f σ)`
    DeclareConst(Symbol, Sort),
    /// `(declare-datatype δ d)`
    DeclareDatatype(Symbol, DatatypeDec),
    /// `(declare-datatypes ((δ k)…) (d…))`: the two lists have the same
    /// length, so the pairs are stored together.
    DeclareDatatypes(NonEmpty<(SortDec, DatatypeDec)>),
    /// `(declare-fun f (σ…) σ)`
    DeclareFun(Symbol, Vec<Sort>, Sort),
    /// `(declare-sort s n)`
    DeclareSort(Symbol, Numeral),
    /// `(declare-sort-parameter u)` (SMT-LIB 2.7)
    DeclareSortParameter(Symbol),
    /// `(define-const f σ t)` (SMT-LIB 2.7)
    DefineConst(Symbol, Sort, Term),
    /// `(define-fun f ((x σ)…) σ t)`
    DefineFun(FunctionDef),
    /// `(define-fun-rec f ((x σ)…) σ t)`
    DefineFunRec(FunctionDef),
    /// `(define-funs-rec (dec…) (t…))`: the two lists have the same length,
    /// so the pairs are stored together.
    DefineFunsRec(NonEmpty<(FunctionDec, Term)>),
    /// `(define-sort s (u…) τ)`
    DefineSort(Symbol, Vec<Symbol>, Sort),
    /// `(echo s)`
    Echo(StringLiteral),
    /// `(exit)`
    Exit,
    /// `(get-assertions)`
    GetAssertions,
    /// `(get-assignment)`
    GetAssignment,
    /// `(get-info flag)`
    GetInfo(Keyword),
    /// `(get-model)`
    GetModel,
    /// `(get-option keyword)`
    GetOption(Keyword),
    /// `(get-proof)`
    GetProof,
    /// `(get-unsat-assumptions)`
    GetUnsatAssumptions,
    /// `(get-unsat-core)`
    GetUnsatCore,
    /// `(get-value (t…))`
    GetValue(NonEmpty<Term>),
    /// `(pop n)`
    Pop(Numeral),
    /// `(push n)`
    Push(Numeral),
    /// `(reset)`
    Reset,
    /// `(reset-assertions)`
    ResetAssertions,
    /// `(set-info attribute)`
    SetInfo(Attribute),
    /// `(set-logic l)`
    SetLogic(Symbol),
    /// `(set-option option)`
    SetOption(Attribute),
}

fn sorted_vars(vars: &[SortedVar]) -> SExpr {
    SExpr::List(vars.iter().map(SortedVar::to_sexpr).collect())
}

fn sorted_var_list(node: &Spanned) -> Result<Vec<SortedVar>> {
    node.expect_list("a list of sorted variables")?.iter().map(SortedVar::from_spanned).collect()
}

fn datatype_dec_sexpr(dec: &DatatypeDec) -> SExpr {
    let constructors = SExpr::List(
        dec.constructors
            .iter()
            .map(|c| {
                let mut items = vec![SExpr::symbol(c.symbol.clone())];
                items.extend(c.selectors.iter().map(|s| SExpr::List(vec![SExpr::symbol(s.symbol.clone()), s.sort.to_sexpr()])));
                SExpr::List(items)
            })
            .collect(),
    );
    if dec.parameters.is_empty() {
        constructors
    } else {
        SExpr::List(vec![SExpr::reserved(Reserved::Par), SExpr::List(dec.parameters.iter().cloned().map(SExpr::symbol).collect()), constructors])
    }
}

impl Command {
    /// The command name, a reserved word.
    pub fn name(&self) -> Reserved {
        match self {
            Command::Assert(_) => Reserved::Assert,
            Command::CheckSat => Reserved::CheckSat,
            Command::CheckSatAssuming(_) => Reserved::CheckSatAssuming,
            Command::DeclareConst(..) => Reserved::DeclareConst,
            Command::DeclareDatatype(..) => Reserved::DeclareDatatype,
            Command::DeclareDatatypes(_) => Reserved::DeclareDatatypes,
            Command::DeclareFun(..) => Reserved::DeclareFun,
            Command::DeclareSort(..) => Reserved::DeclareSort,
            Command::DeclareSortParameter(_) => Reserved::DeclareSortParameter,
            Command::DefineConst(..) => Reserved::DefineConst,
            Command::DefineFun(_) => Reserved::DefineFun,
            Command::DefineFunRec(_) => Reserved::DefineFunRec,
            Command::DefineFunsRec(_) => Reserved::DefineFunsRec,
            Command::DefineSort(..) => Reserved::DefineSort,
            Command::Echo(_) => Reserved::Echo,
            Command::Exit => Reserved::Exit,
            Command::GetAssertions => Reserved::GetAssertions,
            Command::GetAssignment => Reserved::GetAssignment,
            Command::GetInfo(_) => Reserved::GetInfo,
            Command::GetModel => Reserved::GetModel,
            Command::GetOption(_) => Reserved::GetOption,
            Command::GetProof => Reserved::GetProof,
            Command::GetUnsatAssumptions => Reserved::GetUnsatAssumptions,
            Command::GetUnsatCore => Reserved::GetUnsatCore,
            Command::GetValue(_) => Reserved::GetValue,
            Command::Pop(_) => Reserved::Pop,
            Command::Push(_) => Reserved::Push,
            Command::Reset => Reserved::Reset,
            Command::ResetAssertions => Reserved::ResetAssertions,
            Command::SetInfo(_) => Reserved::SetInfo,
            Command::SetLogic(_) => Reserved::SetLogic,
            Command::SetOption(_) => Reserved::SetOption,
        }
    }

    /// The S-expression of this command.
    pub fn to_sexpr(&self) -> SExpr {
        let mut items = vec![SExpr::reserved(self.name())];
        match self {
            Command::Assert(t) => items.push(t.to_sexpr()),
            Command::CheckSatAssuming(terms) => items.push(SExpr::List(terms.iter().map(Term::to_sexpr).collect())),
            Command::DeclareSortParameter(u) => items.push(SExpr::symbol(u.clone())),
            Command::DefineConst(f, sort, t) => {
                items.push(SExpr::symbol(f.clone()));
                items.push(sort.to_sexpr());
                items.push(t.to_sexpr());
            }
            Command::DeclareConst(f, sort) => {
                items.push(SExpr::symbol(f.clone()));
                items.push(sort.to_sexpr());
            }
            Command::DeclareDatatype(name, dec) => {
                items.push(SExpr::symbol(name.clone()));
                items.push(datatype_dec_sexpr(dec));
            }
            Command::DeclareDatatypes(pairs) => {
                items.push(SExpr::List(pairs.iter().map(|(s, _)| SExpr::List(vec![SExpr::symbol(s.symbol.clone()), SExpr::constant(SpecConstant::Numeral(s.arity.clone()))])).collect()));
                items.push(SExpr::List(pairs.iter().map(|(_, d)| datatype_dec_sexpr(d)).collect()));
            }
            Command::DeclareFun(f, args, result) => {
                items.push(SExpr::symbol(f.clone()));
                items.push(SExpr::List(args.iter().map(Sort::to_sexpr).collect()));
                items.push(result.to_sexpr());
            }
            Command::DeclareSort(s, n) => {
                items.push(SExpr::symbol(s.clone()));
                items.push(SExpr::constant(SpecConstant::Numeral(n.clone())));
            }
            Command::DefineFun(def) | Command::DefineFunRec(def) => def.push_sexprs(&mut items),
            Command::DefineFunsRec(pairs) => {
                items.push(SExpr::List(pairs.iter().map(|(d, _)| d.to_sexpr()).collect()));
                items.push(SExpr::List(pairs.iter().map(|(_, t)| t.to_sexpr()).collect()));
            }
            Command::DefineSort(s, params, sort) => {
                items.push(SExpr::symbol(s.clone()));
                items.push(SExpr::List(params.iter().cloned().map(SExpr::symbol).collect()));
                items.push(sort.to_sexpr());
            }
            Command::Echo(s) => items.push(SExpr::constant(SpecConstant::String(s.clone()))),
            Command::GetInfo(k) | Command::GetOption(k) => items.push(SExpr::keyword(k.clone())),
            Command::GetValue(terms) => items.push(SExpr::List(terms.iter().map(Term::to_sexpr).collect())),
            Command::Pop(n) | Command::Push(n) => items.push(SExpr::constant(SpecConstant::Numeral(n.clone()))),
            Command::SetInfo(a) | Command::SetOption(a) => a.push_sexprs(&mut items),
            Command::SetLogic(l) => items.push(SExpr::symbol(l.clone())),
            Command::CheckSat
            | Command::Exit
            | Command::GetAssertions
            | Command::GetAssignment
            | Command::GetModel
            | Command::GetProof
            | Command::GetUnsatAssumptions
            | Command::GetUnsatCore
            | Command::Reset
            | Command::ResetAssertions => {}
        }
        SExpr::List(items)
    }

    /// Writes this command in `dialect`, on one line.
    pub fn write<W: fmt::Write + ?Sized>(&self, out: &mut W, dialect: &Dialect) -> fmt::Result {
        self.to_sexpr().write(out, dialect)
    }

    /// The text of this command in `dialect`, on one line.
    pub fn to_text(&self, dialect: &Dialect) -> String {
        self.to_sexpr().to_text(dialect)
    }

    /// Reads a command from `text` in strict SMT-LIB 2.7.
    pub fn parse(text: &str) -> Result<Command> {
        Command::parse_in(text, &Dialect::strict())
    }

    /// Reads a command from `text` in `dialect`.
    pub fn parse_in(text: &str, dialect: &Dialect) -> Result<Command> {
        Command::from_spanned_in(&read_sexpr(text, dialect)?, dialect)
    }

    /// Reads a command in strict SMT-LIB 2.7.
    pub fn from_spanned(node: &Spanned) -> Result<Command> {
        Command::from_spanned_in(node, &Dialect::strict())
    }

    /// Reads a command in `dialect` (its binders, [`Term::from_spanned_in`]).
    pub fn from_spanned_in(node: &Spanned, dialect: &Dialect) -> Result<Command> {
        let term = |n: &Spanned| Term::from_spanned_in(n, dialect);
        let items = node.expect_list("a command ( ⟨command name⟩ … )")?;
        let Some((head, args)) = items.split_first() else {
            return Err(node.expected("a command"));
        };
        let Some(name) = head.as_reserved() else {
            return Err(head.expected("a command name"));
        };
        let n = |count: usize| read::arity(node, args, count, name.as_str());
        let command = match name {
            Reserved::Assert => {
                n(1)?;
                Command::Assert(term(&args[0])?)
            }
            Reserved::CheckSat => {
                n(0)?;
                Command::CheckSat
            }
            Reserved::CheckSatAssuming => {
                n(1)?;
                Command::CheckSatAssuming(args[0].expect_list("a list of assumptions ( ⟨term⟩* )")?.iter().map(term).collect::<Result<Vec<_>>>()?)
            }
            Reserved::DeclareConst => {
                n(2)?;
                Command::DeclareConst(args[0].expect_symbol("a symbol")?.clone(), Sort::from_spanned(&args[1])?)
            }
            Reserved::DeclareDatatype => {
                n(2)?;
                Command::DeclareDatatype(args[0].expect_symbol("a datatype name")?.clone(), datatype_dec(&args[1])?)
            }
            Reserved::DeclareDatatypes => {
                n(2)?;
                let sorts = args[0].expect_list("a list of sort declarations")?
                    .iter()
                    .map(|s| match s.as_list() {
                        Some([symbol, arity]) => Ok(SortDec { symbol: symbol.expect_symbol("a datatype name")?.clone(), arity: arity.expect_numeral("an arity")?.clone() }),
                        _ => Err(s.expected("a sort declaration ( ⟨symbol⟩ ⟨numeral⟩ )")),
                    })
                    .collect::<Result<Vec<_>>>()?;
                let decs = args[1].expect_list("a list of datatype declarations")?.iter().map(datatype_dec).collect::<Result<Vec<_>>>()?;
                if sorts.len() != decs.len() || sorts.is_empty() {
                    return Err(node.error(format!("declare-datatypes needs n+1 sort declarations and n+1 datatype declarations, found {} and {}", sorts.len(), decs.len())));
                }
                Command::DeclareDatatypes(NonEmpty::try_from(sorts.into_iter().zip(decs).collect::<Vec<_>>()).map_err(|e| e.or_at(node.position()))?)
            }
            Reserved::DeclareFun => {
                n(3)?;
                let sorts = args[1].expect_list("a list of sorts")?.iter().map(Sort::from_spanned).collect::<Result<Vec<_>>>()?;
                Command::DeclareFun(args[0].expect_symbol("a symbol")?.clone(), sorts, Sort::from_spanned(&args[2])?)
            }
            Reserved::DeclareSort => {
                n(2)?;
                Command::DeclareSort(args[0].expect_symbol("a symbol")?.clone(), args[1].expect_numeral("an arity")?.clone())
            }
            Reserved::DeclareSortParameter => {
                n(1)?;
                Command::DeclareSortParameter(args[0].expect_symbol("a sort parameter (a symbol)")?.clone())
            }
            Reserved::DefineConst => {
                n(3)?;
                Command::DefineConst(args[0].expect_symbol("a symbol")?.clone(), Sort::from_spanned(&args[1])?, term(&args[2])?)
            }
            Reserved::DefineFun | Reserved::DefineFunRec => {
                n(4)?;
                let def = FunctionDef::from_spanned_items(node, args, dialect)?;
                if name == Reserved::DefineFun {
                    Command::DefineFun(def)
                } else {
                    Command::DefineFunRec(def)
                }
            }
            Reserved::DefineFunsRec => {
                n(2)?;
                let decs = args[0].expect_list("a list of function declarations")?.iter().map(FunctionDec::from_spanned).collect::<Result<Vec<_>>>()?;
                let bodies = args[1].expect_list("a list of function bodies")?.iter().map(term).collect::<Result<Vec<_>>>()?;
                if decs.len() != bodies.len() || decs.is_empty() {
                    return Err(node.error(format!("define-funs-rec needs n+1 declarations and n+1 bodies, found {} and {}", decs.len(), bodies.len())));
                }
                Command::DefineFunsRec(NonEmpty::try_from(decs.into_iter().zip(bodies).collect::<Vec<_>>()).map_err(|e| e.or_at(node.position()))?)
            }
            Reserved::DefineSort => {
                n(3)?;
                let params = args[1].expect_list("a list of sort parameters")?.iter().map(|p| p.expect_symbol("a sort parameter").cloned()).collect::<Result<Vec<_>>>()?;
                Command::DefineSort(args[0].expect_symbol("a symbol")?.clone(), params, Sort::from_spanned(&args[2])?)
            }
            Reserved::Echo => {
                n(1)?;
                Command::Echo(args[0].expect_string("a string literal")?.clone())
            }
            Reserved::Exit => {
                n(0)?;
                Command::Exit
            }
            Reserved::GetAssertions => {
                n(0)?;
                Command::GetAssertions
            }
            Reserved::GetAssignment => {
                n(0)?;
                Command::GetAssignment
            }
            Reserved::GetInfo => {
                n(1)?;
                Command::GetInfo(args[0].expect_keyword("an info flag (a keyword)")?.clone())
            }
            Reserved::GetModel => {
                n(0)?;
                Command::GetModel
            }
            Reserved::GetOption => {
                n(1)?;
                Command::GetOption(args[0].expect_keyword("an option name (a keyword)")?.clone())
            }
            Reserved::GetProof => {
                n(0)?;
                Command::GetProof
            }
            Reserved::GetUnsatAssumptions => {
                n(0)?;
                Command::GetUnsatAssumptions
            }
            Reserved::GetUnsatCore => {
                n(0)?;
                Command::GetUnsatCore
            }
            Reserved::GetValue => {
                n(1)?;
                let terms = args[0].expect_list("a list of terms")?.iter().map(term).collect::<Result<Vec<_>>>()?;
                Command::GetValue(NonEmpty::new(terms).ok_or_else(|| args[0].error("get-value needs at least one term"))?)
            }
            Reserved::Pop => {
                n(1)?;
                Command::Pop(args[0].expect_numeral("a numeral")?.clone())
            }
            Reserved::Push => {
                n(1)?;
                Command::Push(args[0].expect_numeral("a numeral")?.clone())
            }
            Reserved::Reset => {
                n(0)?;
                Command::Reset
            }
            Reserved::ResetAssertions => {
                n(0)?;
                Command::ResetAssertions
            }
            Reserved::SetInfo | Reserved::SetOption => {
                let mut attributes = Attribute::sequence_from_spanned(args)?;
                if attributes.len() != 1 {
                    return Err(node.error(format!("{name} takes one attribute, found {}", attributes.len())));
                }
                let attribute = attributes.remove(0);
                if name == Reserved::SetInfo {
                    Command::SetInfo(attribute)
                } else {
                    Command::SetOption(attribute)
                }
            }
            Reserved::SetLogic => {
                n(1)?;
                Command::SetLogic(args[0].expect_symbol("a logic name")?.clone())
            }
            other => return Err(head.error(format!("{other} is not a command name"))),
        };
        Ok(command)
    }
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_sexpr().fmt(f)
    }
}

fn datatype_dec(node: &Spanned) -> Result<DatatypeDec> {
    let (parameters, constructors) = match node.headed(Reserved::Par) {
        Some([params, constructors]) => {
            let params = params.expect_list("a list of sort parameters")?.iter().map(|p| p.expect_symbol("a sort parameter").cloned()).collect::<Result<Vec<_>>>()?;
            if params.is_empty() {
                return Err(node.error("par needs at least one sort parameter"));
            }
            (params, constructors)
        }
        Some(_) => return Err(node.expected("( par ( ⟨symbol⟩+ ) ( ⟨constructor_dec⟩+ ) )")),
        None => (Vec::new(), node),
    };
    let constructors = constructors.expect_list("a list of constructor declarations")?
        .iter()
        .map(|c| {
            let items = c.expect_list("a constructor declaration ( ⟨symbol⟩ ⟨selector_dec⟩* )")?;
            let Some((symbol, selectors)) = items.split_first() else {
                return Err(c.expected("a constructor declaration ( ⟨symbol⟩ ⟨selector_dec⟩* )"));
            };
            let selectors = selectors
                .iter()
                .map(|s| match s.as_list() {
                    Some([symbol, sort]) => Ok(SelectorDec { symbol: symbol.expect_symbol("a selector")?.clone(), sort: Sort::from_spanned(sort)? }),
                    _ => Err(s.expected("a selector declaration ( ⟨symbol⟩ ⟨sort⟩ )")),
                })
                .collect::<Result<Vec<_>>>()?;
            Ok(ConstructorDec { symbol: symbol.expect_symbol("a constructor")?.clone(), selectors })
        })
        .collect::<Result<Vec<_>>>()?;
    let constructors = NonEmpty::new(constructors).ok_or_else(|| node.error("a datatype needs at least one constructor"))?;
    Ok(DatatypeDec { parameters, constructors })
}

/// A script (§3.11): a sequence of commands.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Script {
    commands: Vec<Command>,
}

impl Script {
    /// The script of `commands`, in order.
    pub fn new(commands: Vec<Command>) -> Script {
        Script { commands }
    }

    /// The commands, in order.
    pub fn commands(&self) -> &[Command] {
        &self.commands
    }

    /// The commands, as a vector.
    pub fn into_commands(self) -> Vec<Command> {
        self.commands
    }

    /// Appends `command`.
    pub fn push(&mut self, command: Command) {
        self.commands.push(command);
    }

    /// Writes this script in `dialect`: one command per line, each ended
    /// by a line feed.
    pub fn write<W: fmt::Write + ?Sized>(&self, out: &mut W, dialect: &Dialect) -> fmt::Result {
        for command in &self.commands {
            command.write(out, dialect)?;
            out.write_char('\n')?;
        }
        Ok(())
    }

    /// The text of this script in `dialect`: one command per line.
    pub fn to_text(&self, dialect: &Dialect) -> String {
        let mut out = String::new();
        let _ = self.write(&mut out, dialect);
        out
    }

    /// Reads a script in strict SMT-LIB 2.7.
    ///
    /// ```
    /// let script = smtlib::Script::parse("(check-sat) ; a comment\n(exit)").unwrap();
    /// assert_eq!(script.commands().len(), 2);
    /// let error = smtlib::Script::parse("(check-sat)\n(assert)").unwrap_err();
    /// assert_eq!((error.kind(), error.position().map(|p| p.line())), (smtlib::ErrorKind::Syntax, Some(2)));
    /// ```
    pub fn parse(text: &str) -> Result<Script> {
        Script::parse_in(text, &Dialect::strict())
    }

    /// Reads a script in `dialect`.
    pub fn parse_in(text: &str, dialect: &Dialect) -> Result<Script> {
        Ok(Script { commands: Script::parse_located(text, dialect)?.into_iter().map(|(_, c)| c).collect() })
    }

    /// Reads a script in `dialect`, with the position of each command.
    pub fn parse_located(text: &str, dialect: &Dialect) -> Result<Vec<(Position, Command)>> {
        read_all(text, dialect)?.iter().map(|node| Ok((node.position(), Command::from_spanned_in(node, dialect)?))).collect()
    }
}

impl fmt::Display for Script {
    /// The text of the script in strict SMT-LIB 2.7, one command per line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write(f, &Dialect::strict())
    }
}

impl std::str::FromStr for Script {
    type Err = Error;
    fn from_str(text: &str) -> Result<Script> {
        Script::parse(text)
    }
}

impl std::str::FromStr for Command {
    type Err = Error;
    fn from_str(text: &str) -> Result<Command> {
        Command::parse(text)
    }
}

impl FromIterator<Command> for Script {
    fn from_iter<I: IntoIterator<Item = Command>>(commands: I) -> Script {
        Script { commands: commands.into_iter().collect() }
    }
}

impl Extend<Command> for Script {
    fn extend<I: IntoIterator<Item = Command>>(&mut self, commands: I) {
        self.commands.extend(commands);
    }
}

impl IntoIterator for Script {
    type Item = Command;
    type IntoIter = std::vec::IntoIter<Command>;
    fn into_iter(self) -> Self::IntoIter {
        self.commands.into_iter()
    }
}

impl<'a> IntoIterator for &'a Script {
    type Item = &'a Command;
    type IntoIter = std::slice::Iter<'a, Command>;
    fn into_iter(self) -> Self::IntoIter {
        self.commands.iter()
    }
}

/// The typed view of an `⟨option⟩` (Figure 3.8).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SolverOption {
    /// `:diagnostic-output-channel ⟨string⟩`
    DiagnosticOutputChannel(StringLiteral),
    /// `:global-declarations ⟨b_value⟩`
    GlobalDeclarations(bool),
    /// `:interactive-mode ⟨b_value⟩` (deprecated name of produce-assertions)
    InteractiveMode(bool),
    /// `:print-success ⟨b_value⟩`
    PrintSuccess(bool),
    /// `:produce-assertions ⟨b_value⟩`
    ProduceAssertions(bool),
    /// `:produce-assignments ⟨b_value⟩`
    ProduceAssignments(bool),
    /// `:produce-models ⟨b_value⟩`
    ProduceModels(bool),
    /// `:produce-proofs ⟨b_value⟩`
    ProduceProofs(bool),
    /// `:produce-unsat-assumptions ⟨b_value⟩`
    ProduceUnsatAssumptions(bool),
    /// `:produce-unsat-cores ⟨b_value⟩`
    ProduceUnsatCores(bool),
    /// `:random-seed ⟨numeral⟩`
    RandomSeed(Numeral),
    /// `:regular-output-channel ⟨string⟩`
    RegularOutputChannel(StringLiteral),
    /// `:reproducible-resource-limit ⟨numeral⟩`
    ReproducibleResourceLimit(Numeral),
    /// `:verbosity ⟨numeral⟩`
    Verbosity(Numeral),
    /// A solver-specific option (an attribute whose keyword is not predefined).
    Other(Attribute),
    /// A predefined option keyword with a value of the wrong form.
    Malformed(Attribute),
}

impl SolverOption {
    /// The typed view of `attribute` as an option of Figure 3.8.
    pub fn classify(attribute: &Attribute) -> SolverOption {
        let name = attribute.keyword().name();
        let value = attribute.value();
        let boolean = value.and_then(AttributeValue::as_bool);
        let numeral = match value {
            Some(AttributeValue::Constant(SpecConstant::Numeral(n))) => Some(n.clone()),
            _ => None,
        };
        let string = match value {
            Some(AttributeValue::Constant(SpecConstant::String(s))) => Some(s.clone()),
            _ => None,
        };
        let typed = match name {
            "diagnostic-output-channel" => string.map(SolverOption::DiagnosticOutputChannel),
            "global-declarations" => boolean.map(SolverOption::GlobalDeclarations),
            "interactive-mode" => boolean.map(SolverOption::InteractiveMode),
            "print-success" => boolean.map(SolverOption::PrintSuccess),
            "produce-assertions" => boolean.map(SolverOption::ProduceAssertions),
            "produce-assignments" => boolean.map(SolverOption::ProduceAssignments),
            "produce-models" => boolean.map(SolverOption::ProduceModels),
            "produce-proofs" => boolean.map(SolverOption::ProduceProofs),
            "produce-unsat-assumptions" => boolean.map(SolverOption::ProduceUnsatAssumptions),
            "produce-unsat-cores" => boolean.map(SolverOption::ProduceUnsatCores),
            "random-seed" => numeral.map(SolverOption::RandomSeed),
            "regular-output-channel" => string.map(SolverOption::RegularOutputChannel),
            "reproducible-resource-limit" => numeral.map(SolverOption::ReproducibleResourceLimit),
            "verbosity" => numeral.map(SolverOption::Verbosity),
            _ => return SolverOption::Other(attribute.clone()),
        };
        typed.unwrap_or_else(|| SolverOption::Malformed(attribute.clone()))
    }
}

/// The typed view of an `⟨info_flag⟩` (Figure 3.9).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum InfoFlag {
    /// `:all-statistics`
    AllStatistics,
    /// `:assertion-stack-levels`
    AssertionStackLevels,
    /// `:authors`
    Authors,
    /// `:error-behavior`
    ErrorBehavior,
    /// `:name`
    Name,
    /// `:reason-unknown`
    ReasonUnknown,
    /// `:version`
    Version,
    /// A solver-specific flag.
    Other(Keyword),
}

impl InfoFlag {
    /// The typed view of `keyword` as an info flag of Figure 3.9.
    pub fn classify(keyword: &Keyword) -> InfoFlag {
        match keyword.name() {
            "all-statistics" => InfoFlag::AllStatistics,
            "assertion-stack-levels" => InfoFlag::AssertionStackLevels,
            "authors" => InfoFlag::Authors,
            "error-behavior" => InfoFlag::ErrorBehavior,
            "name" => InfoFlag::Name,
            "reason-unknown" => InfoFlag::ReasonUnknown,
            "version" => InfoFlag::Version,
            _ => InfoFlag::Other(keyword.clone()),
        }
    }
}
