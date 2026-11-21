//! classical-propositional interchange types and validation. See spec/propositional/core.trion and spec/obligations.trion.

use serde::de::{self, value::MapAccessDeserializer, IgnoredAny, MapAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::{fmt, marker::PhantomData};

pub const SEMANTICS: &str = "classical-propositional";
pub const SCHEMA: &str = "core-json";
pub const DEFINITIONS: &str = "empty";
pub const MAX_DEPTH: usize = 48;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Expr {
    True,
    False,
    Atom(u32),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DocumentData {
    semantics: String,
    schema: String,
    definitions: String,
    declarations: Vec<String>,
    premises: Vec<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CoreDocument(DocumentData);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Question {
    Satisfiable,
    Entails(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct QueryData {
    document: String,
    question: Question,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Query(QueryData);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Problem {
    document: CoreDocument,
    query: Query,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProblemData {
    document: CoreDocument,
    #[serde(deserialize_with = "object")]
    query: QueryData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    UnsupportedTag { field: &'static str, value: String },
    Name(String),
    Duplicate(String),
    TooManyDeclarations,
    Undeclared(u32),
    ExpressionDepth,
    WrongDocument,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedTag { field, value } => write!(f, "unsupported {field} {value:?}"),
            Self::Name(name) => write!(f, "invalid proposition name {name:?}"),
            Self::Duplicate(name) => write!(f, "duplicate declaration {name:?}"),
            Self::TooManyDeclarations => f.write_str("declaration table has too many slots"),
            Self::Undeclared(i) => write!(f, "undeclared proposition slot {i}"),
            Self::ExpressionDepth => write!(f, "expression exceeds exchange depth {MAX_DEPTH}"),
            Self::WrongDocument => f.write_str("query refers to a different document"),
        }
    }
}

impl std::error::Error for Error {}

pub fn valid_name(name: &str) -> bool {
    let mut bytes = name.bytes();
    bytes
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic())
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

fn check_expr(expr: &Expr, slots: usize, remaining: usize) -> Result<(), Error> {
    if remaining == 0 {
        return Err(Error::ExpressionDepth);
    }
    match expr {
        Expr::Atom(i) if *i as usize >= slots => Err(Error::Undeclared(*i)),
        Expr::Not(child) => check_expr(child, slots, remaining - 1),
        Expr::And(left, right) | Expr::Or(left, right) => {
            check_expr(left, slots, remaining - 1)?;
            check_expr(right, slots, remaining - 1)
        }
        Expr::True | Expr::False | Expr::Atom(_) => Ok(()),
    }
}

impl TryFrom<DocumentData> for CoreDocument {
    type Error = Error;

    fn try_from(data: DocumentData) -> Result<Self, Error> {
        for (field, expected, found) in [
            ("semantics", SEMANTICS, &data.semantics),
            ("schema", SCHEMA, &data.schema),
            ("definitions", DEFINITIONS, &data.definitions),
        ] {
            if found != expected {
                return Err(Error::UnsupportedTag {
                    field,
                    value: found.clone(),
                });
            }
        }
        if data
            .declarations
            .len()
            .checked_sub(1)
            .is_some_and(|last| u32::try_from(last).is_err())
        {
            return Err(Error::TooManyDeclarations);
        }
        let mut names = BTreeSet::new();
        for name in &data.declarations {
            if !valid_name(name) {
                return Err(Error::Name(name.clone()));
            }
            if !names.insert(name) {
                return Err(Error::Duplicate(name.clone()));
            }
        }
        for expr in &data.premises {
            check_expr(expr, data.declarations.len(), MAX_DEPTH)?;
        }
        Ok(Self(data))
    }
}

impl CoreDocument {
    pub fn new(declarations: Vec<String>, premises: Vec<Expr>) -> Result<Self, Error> {
        DocumentData {
            semantics: SEMANTICS.into(),
            schema: SCHEMA.into(),
            definitions: DEFINITIONS.into(),
            declarations,
            premises,
        }
        .try_into()
    }

    pub fn declarations(&self) -> &[String] {
        &self.0.declarations
    }

    pub fn premises(&self) -> &[Expr] {
        &self.0.premises
    }

    pub fn canonical_json(&self) -> String {
        serde_json::to_string(self).expect("validated document is serializable")
    }

    pub fn id(&self) -> String {
        sha256(self.canonical_json())
    }
}

impl Query {
    pub fn question(&self) -> &Question {
        &self.0.question
    }

    pub fn id(&self) -> String {
        sha256(serde_json::to_string(self).expect("validated query is serializable"))
    }
}

impl TryFrom<ProblemData> for Problem {
    type Error = Error;

    fn try_from(data: ProblemData) -> Result<Self, Error> {
        if data.query.document != data.document.id() {
            return Err(Error::WrongDocument);
        }
        if let Question::Entails(goal) = &data.query.question {
            check_expr(goal, data.document.declarations().len(), MAX_DEPTH)?;
        }
        Ok(Self {
            document: data.document,
            query: Query(data.query),
        })
    }
}

impl Problem {
    pub fn new(document: CoreDocument, question: Question) -> Result<Self, Error> {
        if let Question::Entails(goal) = &question {
            check_expr(goal, document.declarations().len(), MAX_DEPTH)?;
        }
        let query = Query(QueryData {
            document: document.id(),
            question,
        });
        Ok(Self { document, query })
    }

    pub fn document(&self) -> &CoreDocument {
        &self.document
    }

    pub fn query(&self) -> &Query {
        &self.query
    }
}

pub fn sha256(bytes: impl AsRef<[u8]>) -> String {
    format!("{:x}", Sha256::digest(bytes.as_ref()))
}

fn single_key<'de, M: MapAccess<'de>>(map: &mut M) -> Result<String, M::Error> {
    map.next_key()?
        .ok_or_else(|| de::Error::custom("expected one constructor key"))
}

fn finish_constructor<'de, M: MapAccess<'de>>(map: &mut M) -> Result<(), M::Error> {
    if map.next_key::<IgnoredAny>()?.is_some() {
        return Err(de::Error::custom("expected exactly one constructor key"));
    }
    Ok(())
}

impl<'de> Deserialize<'de> for Expr {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Expression;

        impl<'de> Visitor<'de> for Expression {
            type Value = Expr;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a propositional constant string or one constructor key")
            }

            fn visit_str<E: de::Error>(self, value: &str) -> Result<Expr, E> {
                match value {
                    "true" => Ok(Expr::True),
                    "false" => Ok(Expr::False),
                    _ => Err(E::unknown_variant(value, &["true", "false"])),
                }
            }

            fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<Expr, M::Error> {
                let key = single_key(&mut map)?;
                let expr = match key.as_str() {
                    "atom" => Expr::Atom(map.next_value()?),
                    "not" => Expr::Not(map.next_value()?),
                    "and" => {
                        let (left, right) = map.next_value()?;
                        Expr::And(left, right)
                    }
                    "or" => {
                        let (left, right) = map.next_value()?;
                        Expr::Or(left, right)
                    }
                    _ => {
                        return Err(de::Error::unknown_variant(
                            &key,
                            &["atom", "not", "and", "or"],
                        ))
                    }
                };
                finish_constructor(&mut map)?;
                Ok(expr)
            }
        }

        deserializer.deserialize_any(Expression)
    }
}

impl<'de> Deserialize<'de> for Question {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct QueryKind;

        impl<'de> Visitor<'de> for QueryKind {
            type Value = Question;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("\"satisfiable\" or one entails key")
            }

            fn visit_str<E: de::Error>(self, value: &str) -> Result<Question, E> {
                if value == "satisfiable" {
                    Ok(Question::Satisfiable)
                } else {
                    Err(E::unknown_variant(value, &["satisfiable"]))
                }
            }

            fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<Question, M::Error> {
                let key = single_key(&mut map)?;
                if key != "entails" {
                    return Err(de::Error::unknown_variant(&key, &["entails"]));
                }
                let goal = map.next_value()?;
                finish_constructor(&mut map)?;
                Ok(Question::Entails(goal))
            }
        }

        deserializer.deserialize_any(QueryKind)
    }
}

fn object<'de, D: Deserializer<'de>, T: Deserialize<'de>>(deserializer: D) -> Result<T, D::Error> {
    struct Object<T>(PhantomData<T>);

    impl<'de, T: Deserialize<'de>> Visitor<'de> for Object<T> {
        type Value = T;

        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("an object with named fields")
        }

        fn visit_map<M: MapAccess<'de>>(self, map: M) -> Result<T, M::Error> {
            T::deserialize(MapAccessDeserializer::new(map))
        }
    }

    deserializer.deserialize_map(Object(PhantomData))
}

impl<'de> Deserialize<'de> for CoreDocument {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Self::try_from(object::<D, DocumentData>(deserializer)?).map_err(de::Error::custom)
    }
}

impl<'de> Deserialize<'de> for Problem {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Self::try_from(object::<D, ProblemData>(deserializer)?).map_err(de::Error::custom)
    }
}
