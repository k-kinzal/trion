//! Responses to `check-system` (description.md, "Check-system Response",
//! "Verbose Response", "Compact Response").
//!
//! ```text
//! (check-system-response
//!  :verbosity full | compact
//!  :query (q :result sat :model m :trace t)
//!  :query (q :result unsat :certificate c)
//!  :query (q :result unknown)
//!  :trace (t :prefix p :lasso l)          ; t = p l^ω
//!  :model (m M)                           ; M is a model in SMT-LIB format
//!  :trail (p ( (0 (x v) …) … (j (x v) …) ))
//!  :certificate (c :inv F :k n))
//! ```
//!
//! The document gives the format by one example with placeholders and
//! leaves parts open ("[to do]", "[Complete examples]"); this module reads
//! exactly the shape of that example:
//!
//! - `:verbosity` occurs once and is `full` or `compact`;
//! - a query result has `:result` and at most one each of `:model`,
//!   `:trace` and `:certificate`, whose values are names;
//! - a trace has both a prefix and a lasso trail ("Each witness is then
//!   represented by two trails");
//! - a model `M` is the response of SMT-LIB's `get-model` (SMT-LIB 2.7
//!   §3.11.1, `( ⟨model_response⟩* )`), each definition read by the
//!   `smtlib` crate;
//! - a trail is a list of numbered states, each a list of `(x v)` pairs;
//! - a certificate has `:inv F` (a term) and `:k n` (a numeral).
//!
//! Rules the shape does not state are not checked: that the names a
//! result uses are defined in the response, that states are numbered
//! consecutively, that a compact state lists only changed values, or that
//! a response answers the queries of the command it responds to.

use crate::error::{Error, Result};
use crate::syntax::{attributes, dialect, parenthesized, symbol, syntax, term};
use crate::validate;
use smtlib::lexicon::{Dialect, Numeral, Symbol};
use smtlib::response::ModelResponse;
use smtlib::sexpr::{read, Spanned};
use smtlib::Term;
use std::fmt;
use std::str::FromStr;

/// `:verbosity full` or `:verbosity compact`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Verbosity {
    /// Every state of a trail lists every variable.
    Full,
    /// Each trail starts with a fully specified state; later states list
    /// only the variables whose value changed.
    Compact,
}

impl Verbosity {
    fn as_str(self) -> &'static str {
        match self {
            Verbosity::Full => "full",
            Verbosity::Compact => "compact",
        }
    }
}

/// The `:result` of a query.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Answer {
    /// A trace exists.
    Sat,
    /// No trace exists.
    Unsat,
    /// "for timeouts and other cases".
    Unknown,
}

impl Answer {
    fn as_str(self) -> &'static str {
        match self {
            Answer::Sat => "sat",
            Answer::Unsat => "unsat",
            Answer::Unknown => "unknown",
        }
    }
}

/// `sat`, `unsat` or `unknown`.
impl fmt::Display for Answer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// `full` or `compact`.
impl fmt::Display for Verbosity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// `:query (q :result r :model m :trace t :certificate c)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QueryResult {
    name: Symbol,
    result: Answer,
    model: Option<Symbol>,
    trace: Option<Symbol>,
    certificate: Option<Symbol>,
}

impl QueryResult {
    /// The answer `result` to the query `name`, naming nothing else.
    pub fn new(name: Symbol, result: Answer) -> QueryResult {
        QueryResult { name, result, model: None, trace: None, certificate: None }
    }

    /// This result with `:model model`.
    pub fn with_model(mut self, model: Symbol) -> QueryResult {
        self.model = Some(model);
        self
    }

    /// This result with `:trace trace`.
    pub fn with_trace(mut self, trace: Symbol) -> QueryResult {
        self.trace = Some(trace);
        self
    }

    /// This result with `:certificate certificate`.
    pub fn with_certificate(mut self, certificate: Symbol) -> QueryResult {
        self.certificate = Some(certificate);
        self
    }

    /// The query answered.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// The answer.
    pub fn result(&self) -> Answer {
        self.result
    }

    /// The model of the free symbols, by name.
    pub fn model(&self) -> Option<&Symbol> {
        self.model.as_ref()
    }

    /// The witness trace, by name.
    pub fn trace(&self) -> Option<&Symbol> {
        self.trace.as_ref()
    }

    /// The proof certificate, by name.
    pub fn certificate(&self) -> Option<&Symbol> {
        self.certificate.as_ref()
    }
}

/// `:trace (t :prefix p :lasso l)`, the trace `p l^ω`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Trace {
    name: Symbol,
    prefix: Symbol,
    lasso: Symbol,
}

impl Trace {
    /// The trace `name` made of the trails `prefix` and `lasso`.
    pub fn new(name: Symbol, prefix: Symbol, lasso: Symbol) -> Trace {
        Trace { name, prefix, lasso }
    }

    /// The trace's name.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// The prefix trail, by name.
    pub fn prefix(&self) -> &Symbol {
        &self.prefix
    }

    /// The lasso trail, repeated forever, by name.
    pub fn lasso(&self) -> &Symbol {
        &self.lasso
    }
}

/// `:model (m M)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Model {
    name: Symbol,
    definitions: Vec<ModelResponse>,
}

impl Model {
    /// The model `name` with the `get-model` definitions `definitions`;
    /// their sorts and terms are checked as the module documentation of
    /// [`crate::syntax`] describes.
    pub fn new(name: Symbol, definitions: Vec<ModelResponse>) -> Result<Model> {
        for definition in &definitions {
            validate::model_response(definition, MODEL_DEPTH)?;
        }
        Ok(Model { name, definitions })
    }

    /// The model's name.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// The definitions of `M`, as in a `get-model` response.
    pub fn definitions(&self) -> &[ModelResponse] {
        &self.definitions
    }
}

/// `(k (x1 v1) … (xn vn))`: a numbered state.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct State {
    index: Numeral,
    assignments: Vec<(Symbol, Term)>,
}

impl State {
    /// The state numbered `index` with `assignments`; the values are
    /// checked as the module documentation of [`crate::syntax`] describes.
    pub fn new(index: Numeral, assignments: Vec<(Symbol, Term)>) -> Result<State> {
        for (_, value) in &assignments {
            validate::term(value, VALUE_DEPTH)?;
        }
        Ok(State { index, assignments })
    }

    /// The state's number.
    pub fn index(&self) -> &Numeral {
        &self.index
    }

    /// The values of the listed variables, in order.
    pub fn assignments(&self) -> &[(Symbol, Term)] {
        &self.assignments
    }
}

/// `:trail (p (states…))`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Trail {
    name: Symbol,
    states: Vec<State>,
}

impl Trail {
    /// The trail `name` made of `states`.
    pub fn new(name: Symbol, states: Vec<State>) -> Trail {
        Trail { name, states }
    }

    /// The trail's name.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// The states, in order.
    pub fn states(&self) -> &[State] {
        &self.states
    }
}

/// `:certificate (c :inv F :k n)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Certificate {
    name: Symbol,
    invariant: Term,
    k: Numeral,
}

impl Certificate {
    /// The certificate `name` with the invariant `invariant`, inductive at
    /// depth `k`; `invariant` is checked as the module documentation of
    /// [`crate::syntax`] describes.
    pub fn new(name: Symbol, invariant: Term, k: Numeral) -> Result<Certificate> {
        validate::term(&invariant, INVARIANT_DEPTH)?;
        Ok(Certificate { name, invariant, k })
    }

    /// The certificate's name.
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// The invariant `F`.
    pub fn invariant(&self) -> &Term {
        &self.invariant
    }

    /// The induction depth `n`.
    pub fn k(&self) -> &Numeral {
        &self.k
    }
}

/// An attribute of a response after `:verbosity`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ResponseItem {
    /// `:query`
    Query(QueryResult),
    /// `:trace`
    Trace(Trace),
    /// `:model`
    Model(Model),
    /// `:trail`
    Trail(Trail),
    /// `:certificate`
    Certificate(Certificate),
}

/// `(check-system-response :verbosity v items…)`.
///
/// ```
/// use moxi::response::{Answer, CheckSystemResponse};
/// let response: CheckSystemResponse = "(check-system-response :verbosity full
///   :query (q :result sat :trace t) :trace (t :prefix p :lasso l)
///   :trail (p ((0 (x 0)))) :trail (l ((0 (x 1)))))".parse()?;
/// assert_eq!(response.queries().next().map(|q| q.result()), Some(Answer::Sat));
/// assert_eq!(response.to_string().parse::<CheckSystemResponse>()?, response);
/// # Ok::<(), moxi::Error>(())
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CheckSystemResponse {
    verbosity: Verbosity,
    items: Vec<ResponseItem>,
}

/// The parentheses that enclose a definition of a `:model`, a value in a
/// `:trail`, and the invariant of a `:certificate`.
const MODEL_DEPTH: usize = 3;
const VALUE_DEPTH: usize = 5;
const INVARIANT_DEPTH: usize = 2;

/// The value of each attribute of `(name :k1 v1 … :kn vn)`, in the order
/// of `allowed`; each keyword is among `allowed` and occurs at most once.
fn named_attributes<'a, const N: usize>(node: &'a Spanned, what: &str, allowed: [&str; N]) -> Result<(Symbol, [Option<&'a Spanned>; N])> {
    let items = node.expect_list(what)?;
    let Some((name, rest)) = items.split_first() else {
        return Err(node.expected(what).into());
    };
    let name = symbol(name, &format!("the name in {what}"))?;
    let mut values = [None; N];
    for (at, keyword, value) in attributes(rest, what)? {
        let Some(slot) = allowed.iter().position(|a| *a == keyword.name()) else {
            return Err(syntax(at, format!("{keyword} is not an attribute of {what}; the attributes are {}", allowed.map(|a| format!(":{a}")).join(", "))));
        };
        if values[slot].replace(value).is_some() {
            return Err(syntax(at, format!("the attribute {keyword} occurs twice in {what}")));
        }
    }
    Ok((name, values))
}

impl CheckSystemResponse {
    /// The response with `verbosity` and the attributes `items`, in order.
    pub fn new(verbosity: Verbosity, items: Vec<ResponseItem>) -> CheckSystemResponse {
        CheckSystemResponse { verbosity, items }
    }

    /// Full or compact.
    pub fn verbosity(&self) -> Verbosity {
        self.verbosity
    }

    /// The attributes after `:verbosity`, in order.
    pub fn items(&self) -> &[ResponseItem] {
        &self.items
    }

    /// The query results, in order.
    pub fn queries(&self) -> impl Iterator<Item = &QueryResult> {
        self.items.iter().filter_map(|i| if let ResponseItem::Query(q) = i { Some(q) } else { None })
    }

    fn read(node: &Spanned, d: &Dialect) -> Result<CheckSystemResponse> {
        let items = node.expect_list("( check-system-response … )")?;
        let Some((head, rest)) = items.split_first().filter(|(head, _)| head.as_symbol().is_some_and(|s| s.as_str() == "check-system-response")) else {
            return Err(node.expected("( check-system-response … )").into());
        };
        let mut verbosity = None;
        let mut out = Vec::new();
        for (at, keyword, value) in attributes(rest, "check-system-response")? {
            match keyword.name() {
                "verbosity" => {
                    let v = match value.as_symbol().map(Symbol::as_str) {
                        Some("full") => Verbosity::Full,
                        Some("compact") => Verbosity::Compact,
                        _ => return Err(value.expected("full or compact").into()),
                    };
                    if verbosity.replace(v).is_some() {
                        return Err(syntax(at, ":verbosity occurs twice"));
                    }
                }
                "query" => {
                    let (name, [result, model, trace, certificate]) = named_attributes(value, "a query result ( q :result r … )", ["result", "model", "trace", "certificate"])?;
                    let Some(result) = result else {
                        return Err(syntax(value, format!("the query result {name} needs :result")));
                    };
                    let result = match result.as_symbol().map(Symbol::as_str) {
                        Some("sat") => Answer::Sat,
                        Some("unsat") => Answer::Unsat,
                        Some("unknown") => Answer::Unknown,
                        _ => return Err(result.expected("sat, unsat or unknown").into()),
                    };
                    let reference = |node: Option<&Spanned>, what: &str| node.map(|v| symbol(v, what)).transpose();
                    out.push(ResponseItem::Query(QueryResult {
                        name,
                        result,
                        model: reference(model, "the name of a model")?,
                        trace: reference(trace, "the name of a trace")?,
                        certificate: reference(certificate, "the name of a certificate")?,
                    }));
                }
                "trace" => {
                    let (name, [prefix, lasso]) = named_attributes(value, "a trace ( t :prefix p :lasso l )", ["prefix", "lasso"])?;
                    let trail = |node: Option<&Spanned>, key: &str| -> Result<Symbol> {
                        let v = node.ok_or_else(|| syntax(value, format!("the trace {name} needs :{key}: a witness is represented by two trails, a prefix and a lasso (description.md, \"Check-system Response\")")))?;
                        symbol(v, "the name of a trail")
                    };
                    out.push(ResponseItem::Trace(Trace { prefix: trail(prefix, "prefix")?, lasso: trail(lasso, "lasso")?, name }));
                }
                "model" => {
                    let [name, model] = value.expect_list("a model ( m M )")? else {
                        return Err(value.expected("a model ( m M )").into());
                    };
                    let name = symbol(name, "the name of a model")?;
                    let definitions = model
                        .expect_list("a model in SMT-LIB format ( ⟨model_response⟩* )")?
                        .iter()
                        .map(|definition| {
                            let read = ModelResponse::from_spanned_in(definition, d).map_err(|e| Error::from(e).or_at(definition.position()))?;
                            validate::model_response(&read, MODEL_DEPTH).map_err(|e| e.or_at(definition.position()))?;
                            Ok(read)
                        })
                        .collect::<Result<Vec<_>>>()?;
                    out.push(ResponseItem::Model(Model { name, definitions }));
                }
                "trail" => {
                    let [name, states] = value.expect_list("a trail ( p ( ⟨state⟩* ) )")? else {
                        return Err(value.expected("a trail ( p ( ⟨state⟩* ) )").into());
                    };
                    let states = states.expect_list("a list of states ( ( k (x v)* )* )")?.iter().map(|s| state(s, d)).collect::<Result<Vec<_>>>()?;
                    out.push(ResponseItem::Trail(Trail { name: symbol(name, "the name of a trail")?, states }));
                }
                "certificate" => {
                    let (name, [invariant, k]) = named_attributes(value, "a certificate ( c :inv F :k n )", ["inv", "k"])?;
                    let invariant = invariant.ok_or_else(|| syntax(value, format!("the certificate {name} needs :inv")))?;
                    let k = k.ok_or_else(|| syntax(value, format!("the certificate {name} needs :k")))?;
                    out.push(ResponseItem::Certificate(Certificate { name, invariant: term(invariant, INVARIANT_DEPTH, d)?, k: k.expect_numeral("a numeral")?.clone() }));
                }
                _ => {
                    return Err(syntax(
                        at,
                        format!("{keyword} is not an attribute of check-system-response: the attributes are :verbosity, :query, :trace, :model, :trail and :certificate"),
                    ))
                }
            }
        }
        let verbosity = verbosity.ok_or_else(|| syntax(head, "a check-system response needs :verbosity full or :verbosity compact (description.md, \"Check-system Response\")"))?;
        Ok(CheckSystemResponse { verbosity, items: out })
    }
}

fn state(node: &Spanned, d: &Dialect) -> Result<State> {
    let items = node.expect_list("a state ( k (x v)* )")?;
    let Some((index, assignments)) = items.split_first() else {
        return Err(node.expected("a state ( k (x v)* )").into());
    };
    let index = index.expect_numeral("the state's number (a numeral)")?.clone();
    let assignments = assignments
        .iter()
        .map(|a| {
            let [x, v] = a.expect_list("an assignment ( x v )")? else {
                return Err(a.expected("an assignment ( x v )").into());
            };
            Ok((symbol(x, "a variable (a symbol)")?, term(v, VALUE_DEPTH, d)?))
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(State { index, assignments })
}

/// Reads a response: one S-expression in the MoXI dialect.
impl FromStr for CheckSystemResponse {
    type Err = Error;

    fn from_str(text: &str) -> Result<CheckSystemResponse> {
        let d = dialect();
        CheckSystemResponse::read(&read(text, &d)?, &d)
    }
}

/// The text of the response in the MoXI dialect, one attribute per line.
/// Reading the text gives back an equal response.
impl fmt::Display for CheckSystemResponse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let d = dialect();
        let name = |s: &Symbol| s.to_text(&d);
        let numeral = |n: &Numeral| n.as_str().to_string();
        write!(f, "(check-system-response\n :verbosity {}", self.verbosity.as_str())?;
        for item in &self.items {
            f.write_str("\n ")?;
            match item {
                ResponseItem::Query(q) => {
                    write!(f, ":query ({} :result {}", name(&q.name), q.result.as_str())?;
                    for (key, value) in [("model", &q.model), ("trace", &q.trace), ("certificate", &q.certificate)] {
                        if let Some(v) = value {
                            write!(f, " :{key} {}", name(v))?;
                        }
                    }
                    f.write_str(")")?;
                }
                ResponseItem::Trace(t) => write!(f, ":trace ({} :prefix {} :lasso {})", name(&t.name), name(&t.prefix), name(&t.lasso))?,
                ResponseItem::Model(m) => write!(f, ":model ({} {})", name(&m.name), parenthesized(m.definitions.iter().map(|r| r.to_sexpr().to_text(&d))))?,
                ResponseItem::Trail(t) => {
                    let states = t.states.iter().map(|s| parenthesized(std::iter::once(numeral(&s.index)).chain(s.assignments.iter().map(|(x, v)| format!("({} {})", name(x), v.to_text(&d))))));
                    write!(f, ":trail ({} {})", name(&t.name), parenthesized(states))?;
                }
                ResponseItem::Certificate(c) => write!(f, ":certificate ({} :inv {} :k {})", name(&c.name), c.invariant.to_text(&d), numeral(&c.k))?,
            }
        }
        f.write_str(")")
    }
}
