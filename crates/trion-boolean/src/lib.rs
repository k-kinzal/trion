//! Exact translation to Boolean negation normal form and the backend protocol.

mod worker;

use serde::{Deserialize, Serialize};
use trion_core::{sha256, Expr, Problem, Question, DEFINITIONS, SEMANTICS};

pub use worker::solve;

pub const ADAPTER: &str = "boolean-nnf/1";
pub const BACKEND: &str = "nnf-enumerator/1";
pub const PROTOCOL: &str = "nnf-work/1";
pub const STAGES: [&str; 2] = ["query-condition/1", "negation-normal-form/1"];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Constructor {
    True,
    False,
    Atom,
    Not,
    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QueryKind {
    Satisfiable,
    Entails,
}

/// The contract for an adapter to this NNF worker. The only supported
/// translation has exact polarity semantics and adds no assumptions.
pub struct Contract {
    pub id: &'static str,
    pub semantics: &'static str,
    pub definitions: &'static str,
    pub constructors: &'static [Constructor],
    pub queries: &'static [QueryKind],
}

pub const EXACT: Contract = Contract {
    id: ADAPTER,
    semantics: SEMANTICS,
    definitions: DEFINITIONS,
    constructors: &[
        Constructor::True,
        Constructor::False,
        Constructor::Atom,
        Constructor::Not,
        Constructor::And,
        Constructor::Or,
    ],
    queries: &[QueryKind::Satisfiable, QueryKind::Entails],
};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "applicability", content = "detail", rename_all = "snake_case")]
pub enum Preparation {
    Applicable(Request),
    Unsupported(String),
    PreconditionFailed(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Scope {
    AllValuations,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Approximation {
    Exact,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BackendSettings {
    pub max_assignments: u64,
    pub timeout_ms: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Request {
    pub protocol: String,
    pub adapter: String,
    pub backend: String,
    pub stages: [String; 2],
    pub document: String,
    pub query: String,
    pub semantics: String,
    pub definitions: String,
    pub scope: Scope,
    pub approximation: Approximation,
    pub added_assumptions: Vec<Term>,
    pub slots: usize,
    pub condition: Vec<Term>,
    pub settings: BackendSettings,
}

impl Request {
    pub fn id(&self) -> String {
        sha256(serde_json::to_vec(self).expect("well-formed request is serializable"))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", deny_unknown_fields)]
pub enum Term {
    Constant(bool),
    Literal { slot: u32, positive: bool },
    All(Box<Term>, Box<Term>),
    Any(Box<Term>, Box<Term>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Response {
    pub request: String,
    pub scope: Scope,
    pub reply: Reply,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Reply {
    Sat(Vec<bool>),
    Unsat,
    Unknown,
    ResourceLimit,
}

impl Contract {
    /// Check capabilities against the validated Core, then apply the two stages.
    pub fn prepare(&self, problem: &Problem, settings: BackendSettings) -> Preparation {
        if self.semantics != SEMANTICS || self.definitions != DEFINITIONS {
            return Preparation::PreconditionFailed(
                "incompatible semantics or definition environment".into(),
            );
        }
        let document = problem.document();
        let goal = match problem.query().question() {
            Question::Satisfiable if self.queries.contains(&QueryKind::Satisfiable) => None,
            Question::Entails(goal) if self.queries.contains(&QueryKind::Entails) => Some(goal),
            _ => return Preparation::Unsupported("query kind is not supported".into()),
        };
        if let Some(constructor) = document
            .premises()
            .iter()
            .chain(goal)
            .find_map(|expr| unsupported(expr, self.constructors))
        {
            return Preparation::Unsupported(format!(
                "constructor {constructor:?} is not supported"
            ));
        }
        let condition = query_condition(problem)
            .map(|(expr, polarity)| to_nnf(expr, polarity))
            .collect();
        Preparation::Applicable(Request {
            protocol: PROTOCOL.into(),
            adapter: self.id.into(),
            backend: BACKEND.into(),
            stages: STAGES.map(str::to_owned),
            document: document.id(),
            query: problem.query().id(),
            semantics: SEMANTICS.into(),
            definitions: DEFINITIONS.into(),
            scope: Scope::AllValuations,
            approximation: Approximation::Exact,
            added_assumptions: Vec::new(),
            slots: document.declarations().len(),
            condition,
            settings,
        })
    }
}

fn unsupported(expr: &Expr, allowed: &[Constructor]) -> Option<Constructor> {
    let (constructor, children): (_, &[_]) = match expr {
        Expr::True => (Constructor::True, &[]),
        Expr::False => (Constructor::False, &[]),
        Expr::Atom(_) => (Constructor::Atom, &[]),
        Expr::Not(child) => (Constructor::Not, &[child]),
        Expr::And(left, right) => (Constructor::And, &[left, right]),
        Expr::Or(left, right) => (Constructor::Or, &[left, right]),
    };
    if !allowed.contains(&constructor) {
        return Some(constructor);
    }
    children
        .iter()
        .find_map(|child| unsupported(child, allowed))
}

/// The query condition has the original premises plus, for entailment, a
/// negatively signed goal. A signed root avoids constructing a deeper tree.
fn query_condition(problem: &Problem) -> impl Iterator<Item = (&Expr, bool)> {
    let negated_goal = match problem.query().question() {
        Question::Satisfiable => None,
        Question::Entails(goal) => Some((goal, false)),
    };
    problem
        .document()
        .premises()
        .iter()
        .map(|expr| (expr, true))
        .chain(negated_goal)
}

fn to_nnf(expr: &Expr, positive: bool) -> Term {
    match expr {
        Expr::True => Term::Constant(positive),
        Expr::False => Term::Constant(!positive),
        Expr::Atom(slot) => Term::Literal {
            slot: *slot,
            positive,
        },
        Expr::Not(child) => to_nnf(child, !positive),
        Expr::And(left, right) | Expr::Or(left, right) => {
            let a = Box::new(to_nnf(left, positive));
            let b = Box::new(to_nnf(right, positive));
            if matches!(expr, Expr::And(..)) == positive {
                Term::All(a, b)
            } else {
                Term::Any(a, b)
            }
        }
    }
}
