//! Versioned CNL input and provenance for propositional analysis.

mod parse;

use serde::{Deserialize, Serialize};
use std::fmt::Write;
use trion_core::{sha256, Expr, Problem, Question};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Grammar {
    #[serde(rename = "propositional-cnl/1")]
    V1,
    #[serde(rename = "propositional-cnl/2")]
    V2,
}

pub const DEFAULT_GRAMMAR: Grammar = Grammar::V1;

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
    grammar: Grammar,
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

    pub fn grammar(&self) -> Grammar {
        self.0.grammar
    }

    pub fn mappings(&self) -> &[Mapping] {
        &self.0.mappings
    }

    pub fn id(&self) -> String {
        sha256(serde_json::to_vec(self).expect("accepted artifact is serializable"))
    }

    pub fn from_json(bytes: &[u8]) -> Result<Self, String> {
        let saved: Saved = serde_json::from_slice(bytes).map_err(|error| error.to_string())?;
        let rebuilt = formalize(&saved.source, saved.grammar)
            .map_err(|error| format!("saved input is no longer accepted: {error:?}"))?;
        if rebuilt.0 != saved {
            return Err("saved input differs from the versioned Core or provenance".into());
        }
        Ok(rebuilt)
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

pub fn formalize(source: &str, grammar: Grammar) -> Result<Accepted, Rejected> {
    let (problem, mappings) = parse::document(source, grammar)?;
    Ok(Accepted(Saved {
        status: Status::Accepted,
        grammar,
        source: source.into(),
        source_id: sha256(source),
        problem,
        mappings,
    }))
}

pub fn formalize_version(source: &str, version: Option<&str>) -> Result<Accepted, Rejected> {
    let grammar = match version {
        None => DEFAULT_GRAMMAR,
        Some("propositional-cnl/1") => Grammar::V1,
        Some("propositional-cnl/2") => Grammar::V2,
        Some(version) => {
            return Err(Rejected::Unsupported(Diagnostic {
                rule: "CNL-VERSION".into(),
                span: Span { start: 0, end: 0 },
                reason: format!("unavailable grammar version {version:?}"),
                suggestion: Some("select propositional-cnl/1 or propositional-cnl/2".into()),
            }));
        }
    };
    formalize(source, grammar)
}

pub fn formalize_bytes(source: &[u8], version: Option<&str>) -> Result<Accepted, Rejected> {
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
    formalize_version(text, version)
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
