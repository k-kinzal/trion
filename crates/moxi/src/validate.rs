//! What a term or sort must satisfy to be part of MoXI syntax, checked on
//! what the reader produces and on what constructors are given, so that
//! every value the crate holds prints as text that reads back to it.
//!
//! - None of what SMT-LIB 2.7 added to the term grammar of SMT-LIB 2.6:
//!   `lambda` and the `_` wildcard of match patterns. The document builds
//!   MoXI on "the SMT-LIB language" with "many-sorted first-order logic with
//!   equality and let binders" as its base logic ("Technical
//!   Preliminaries"); these productions are new in 2.7 and are rejected as
//!   [`ErrorKind::Unsupported`].
//! - No constant or binder of another dialect (an extended constant such as
//!   `-1`, a dialect binder): the MoXI dialect has neither, so the text of
//!   such a term would read back as a different term. A
//!   [`ErrorKind::Construction`] error.
//! - The text nests at most [`DEPTH_LIMIT`] parentheses, counting those
//!   of the context the term is printed in, so that the reader accepts it.
//!   An [`ErrorKind::Depth`] error, as in the reader.
//!
//! The traversals are those of the `smtlib` crate ([`Term::try_fold`],
//! [`Sort::fold`]), which are iterative; the parts of a term that are not
//! subterms (sorts, sorted variables, patterns, attribute values) are
//! measured here, attribute values with an explicit stack.

use crate::error::{Error, ErrorKind, Result};
use crate::syntax::DEPTH_LIMIT;
use smtlib::command::FunctionDef;
use smtlib::lexicon::SpecConstant;
use smtlib::response::ModelResponse;
use smtlib::sexpr::{Atom, SExpr};
use smtlib::term::{AttributeValue, Identifier, Pattern, QualIdentifier, SortedVar};
use smtlib::{Sort, Term};

fn unsupported(what: &str) -> Error {
    Error::new(ErrorKind::Unsupported, format!("{what} is SMT-LIB 2.7, which MoXI does not have: its terms are those of many-sorted first-order logic (description.md, \"Technical Preliminaries\")"))
}

fn constant(constant: &SpecConstant) -> Result<()> {
    match constant {
        SpecConstant::Extended(c) => Err(Error::new(ErrorKind::Construction, format!("{c} is an extended constant, which the MoXI dialect does not have; its text would read back as a different term"))),
        _ => Ok(()),
    }
}

fn most(depths: &[usize]) -> usize {
    depths.iter().copied().max().unwrap_or(0)
}

// Each function below returns the number of parentheses the text of its
// argument nests, its own included: 0 for a token.

fn identifier(identifier: &Identifier) -> usize {
    usize::from(!identifier.indices().is_empty())
}

fn sort_depth(sort: &Sort) -> usize {
    sort.fold(|sort, arguments| if arguments.is_empty() { identifier(sort.identifier()) } else { 1 + identifier(sort.identifier()).max(most(&arguments)) })
}

fn qualified(q: &QualIdentifier) -> usize {
    match q.sort() {
        Some(sort) => 1 + identifier(q.identifier()).max(sort_depth(sort)),
        None => identifier(q.identifier()),
    }
}

/// `((x S) …)`.
fn vars_depth(vars: &[SortedVar]) -> usize {
    1 + vars.iter().map(|v| 1 + sort_depth(v.sort())).max().unwrap_or(0)
}

fn pattern(pattern: &Pattern) -> Result<usize> {
    match pattern {
        Pattern::Symbol(_) => Ok(0),
        Pattern::Constructor(_, vars) if vars.iter().all(Option::is_some) => Ok(1),
        Pattern::Constructor(..) | Pattern::Wildcard => Err(unsupported("the wildcard pattern _")),
        _ => Err(Error::new(ErrorKind::Unsupported, "a kind of pattern this crate does not know")),
    }
}

/// `(v …)`, an attribute value list; walked with an explicit stack.
fn list_depth(items: &[SExpr]) -> Result<usize> {
    let mut deepest = 1;
    let mut stack: Vec<(&SExpr, usize)> = items.iter().map(|i| (i, 1)).collect();
    while let Some((item, depth)) = stack.pop() {
        match item {
            SExpr::Atom(Atom::Constant(c)) => constant(c)?,
            SExpr::Atom(_) => {}
            SExpr::List(items) => {
                deepest = deepest.max(depth + 1);
                stack.extend(items.iter().map(|i| (i, depth + 1)));
            }
        }
    }
    Ok(deepest)
}

fn term_depth(term: &Term) -> Result<usize> {
    term.try_fold(|term, children: Vec<usize>| {
        let first = children.first().copied().unwrap_or(0);
        Ok(match term {
            Term::Constant(c) => {
                constant(c)?;
                0
            }
            Term::Identifier(q) => qualified(q),
            Term::Application(q, _) => 1 + qualified(q).max(most(&children)),
            // `(let ((x t) …) body)`: the bindings' terms, then the body.
            Term::Let(..) => {
                let (bindings, body) = children.split_at(children.len().saturating_sub(1));
                1 + (2 + most(bindings)).max(most(body))
            }
            Term::Forall(vars, _) | Term::Exists(vars, _) => 1 + vars_depth(vars).max(first),
            // `(match t ((p body) …))`: the term, then each case's body.
            Term::Match(_, cases) => {
                let mut case = most(children.get(1..).unwrap_or(&[]));
                for c in cases.iter() {
                    case = case.max(pattern(c.pattern())?);
                }
                1 + first.max(2 + case)
            }
            Term::Annotated(_, attributes) => {
                let mut deepest = first;
                for a in attributes.iter() {
                    match a.value() {
                        Some(AttributeValue::Constant(c)) => constant(c)?,
                        Some(AttributeValue::List(items)) => deepest = deepest.max(list_depth(items)?),
                        _ => {}
                    }
                }
                1 + deepest
            }
            Term::Lambda(..) => return Err(unsupported("lambda")),
            Term::Binder(name, ..) => return Err(Error::new(ErrorKind::Construction, format!("{name} is a binder of another dialect; the MoXI dialect has none, so its text would read back as a different term"))),
            _ => return Err(Error::new(ErrorKind::Unsupported, "a kind of term this crate does not know")),
        })
    })
}

fn within(depth: usize) -> Result<()> {
    if depth > DEPTH_LIMIT {
        return Err(Error::new(ErrorKind::Depth, format!("the text would nest {depth} parentheses deep; the reader accepts at most {DEPTH_LIMIT}")));
    }
    Ok(())
}

/// Checks `term`, printed inside `outer` parentheses.
pub(crate) fn term(term: &Term, outer: usize) -> Result<()> {
    within(outer + term_depth(term)?)
}

/// Checks `sort`, printed inside `outer` parentheses.
pub(crate) fn sort(sort: &Sort, outer: usize) -> Result<()> {
    within(outer + sort_depth(sort))
}

/// Checks `((x S) …)`, printed inside `outer` parentheses.
pub(crate) fn sorted_vars(vars: &[SortedVar], outer: usize) -> Result<()> {
    within(outer + vars_depth(vars))
}

/// `f ((x S) …) S t`, the inside of `(define-fun …)`.
fn definition_depth(def: &FunctionDef) -> Result<usize> {
    Ok(vars_depth(def.parameters()).max(sort_depth(def.sort())).max(term_depth(def.body())?))
}

/// Checks `f ((x S) …) S t`, the inside of `(define-fun …)` at `depth`.
pub(crate) fn function_def(def: &FunctionDef, depth: usize) -> Result<()> {
    within(depth + definition_depth(def)?)
}

/// Checks a `get-model` definition whose own list opens inside `outer`
/// parentheses.
pub(crate) fn model_response(response: &ModelResponse, outer: usize) -> Result<()> {
    let inside = match response {
        ModelResponse::DefineFun(def) | ModelResponse::DefineFunRec(def) => definition_depth(def)?,
        // `(define-funs-rec ((f ((x S) …) S) …) (t …))`
        ModelResponse::DefineFunsRec(definitions) => {
            let mut deepest = 1;
            for (declaration, body) in definitions.iter() {
                deepest = deepest.max(2 + vars_depth(declaration.parameters()).max(sort_depth(declaration.sort()))).max(1 + term_depth(body)?);
            }
            deepest
        }
        _ => return Err(Error::new(ErrorKind::Unsupported, "a kind of model response this crate does not know")),
    };
    within(outer + 1 + inside)
}
