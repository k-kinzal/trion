//! CNL input and provenance for propositional analysis.

mod parse;

use serde::{Deserialize, Serialize};
use std::fmt::Write;
use trion_core::{sha256, Expr, Problem, Question};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Diagnostic {
    pub rule: String,
    pub span: Span,
    pub reason: String,
    pub suggestion: Option<String>,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "status", content = "diagnostic", rename_all = "snake_case")]
pub enum Rejected {
    Ambiguous(Diagnostic),
    Unsupported(Diagnostic),
    Invalid(Diagnostic),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum Status {
    Accepted,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Root {
    Declaration(usize),
    Premise(usize),
    Question,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Mapping {
    pub root: Root,
    pub children: Vec<u8>,
    pub span: Span,
    pub rules: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Saved {
    status: Status,
    source: String,
    source_id: String,
    problem: Problem,
    mappings: Vec<Mapping>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Accepted(Saved);

impl Accepted {
    pub fn problem(&self) -> &Problem {
        &self.0.problem
    }

    pub fn mappings(&self) -> &[Mapping] {
        &self.0.mappings
    }

    pub fn id(&self) -> String {
        sha256(serde_json::to_vec(self).expect("accepted artifact is serializable"))
    }

    pub fn from_json(bytes: &[u8]) -> Result<Self, String> {
        serde_json::from_slice(bytes).map_err(|error| error.to_string())
    }

    pub fn canonical_cnl(&self) -> String {
        let document = self.problem().document();
        let names = document.declarations();
        let mut text = String::new();
        for name in names {
            writeln!(text, "proposition {name}.").unwrap();
        }
        for premise in document.premises() {
            text.push_str("assume ");
            print_expr(&mut text, premise, names);
            text.push_str(".\n");
        }
        match self.problem().query().question() {
            Question::Satisfiable => text.push_str("satisfiable.\n"),
            Question::Entails(goal) => {
                text.push_str("entails ");
                print_expr(&mut text, goal, names);
                text.push_str(".\n");
            }
        }
        text
    }
}

impl<'de> Deserialize<'de> for Accepted {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let saved = Saved::deserialize(deserializer)?;
        let rebuilt = formalize(&saved.source).map_err(|error| {
            serde::de::Error::custom(format!("saved input is no longer accepted: {error:?}"))
        })?;
        if rebuilt.0 != saved {
            return Err(serde::de::Error::custom(
                "saved input differs from the Core or provenance",
            ));
        }
        Ok(rebuilt)
    }
}

pub fn formalize(source: &str) -> Result<Accepted, Rejected> {
    let (problem, mappings) = parse::document(source)?;
    Ok(Accepted(Saved {
        status: Status::Accepted,
        source: source.into(),
        source_id: sha256(source),
        problem,
        mappings,
    }))
}

pub fn formalize_bytes(source: &[u8]) -> Result<Accepted, Rejected> {
    let text = std::str::from_utf8(source).map_err(|error| {
        let start = error.valid_up_to();
        let end = start + error.error_len().unwrap_or(source.len() - start);
        Rejected::Invalid(Diagnostic {
            rule: "CNL-UTF8".into(),
            span: Span { start, end },
            reason: "input is not valid UTF-8".into(),
            suggestion: Some("save the source as UTF-8".into()),
        })
    })?;
    formalize(text)
}

fn print_expr(out: &mut String, expr: &Expr, names: &[String]) {
    match expr {
        Expr::True => out.push_str("true"),
        Expr::False => out.push_str("false"),
        Expr::Atom(i) => out.push_str(&names[*i as usize]),
        Expr::Not(child) => {
            out.push_str("not ");
            print_expr(out, child, names);
        }
        Expr::And(left, right) | Expr::Or(left, right) => {
            out.push('(');
            print_expr(out, left, names);
            out.push_str(if matches!(expr, Expr::And(..)) {
                " and "
            } else {
                " or "
            });
            print_expr(out, right, names);
            out.push(')');
        }
    }
}
