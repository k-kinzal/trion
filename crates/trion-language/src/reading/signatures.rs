//! Argument checking of declared verbal predicates before formulas are built.

use super::lexicon::Lexicon;
use super::model::{np_key, participle_base, role_nps};
use super::rules::{self, Call};
use super::vocabulary::{verb_lemma, VocabEntry};
use crate::diagnostic::{Diagnostic, SpecRef};
use crate::document::SpecSet;
use crate::syntax::ast::{Np, RolePp};
use std::collections::{BTreeMap, BTreeSet};

const KINDS: [&str; 4] = ["entity", "object", "attribute", "value"];

/// Canonical signature names for tooling and specification mappings.
pub(super) fn sort_name(written: &str, lex: &Lexicon) -> String {
    let kind = written.to_lowercase();
    if KINDS.contains(&kind.as_str()) || kind == "proposition" {
        return kind;
    }
    lex.resolve(&lex.canon(written))
}

#[derive(Debug)]
enum Sort {
    Kind(String),
    Named(String),
    Proposition,
}

impl Sort {
    fn name(&self) -> &str {
        match self {
            Self::Kind(name) | Self::Named(name) => name,
            Self::Proposition => "proposition",
        }
    }

    fn accepts(&self, name: &str, kind: &str) -> bool {
        match self {
            Self::Kind(expected) => {
                expected == kind
                    || (["entity", "object"].contains(&expected.as_str())
                        && ["entity", "object"].contains(&kind))
            }
            Self::Named(expected) => expected == name,
            Self::Proposition => false,
        }
    }
}

struct Signature {
    arguments: Vec<Sort>,
    origin: SpecRef,
}

fn argument_name(np: &Np, lex: &Lexicon, carriers: &BTreeSet<String>) -> String {
    let mut np = np.clone();
    np.relative = None;
    let mut bare = np.clone();
    bare.modifiers.retain(|word| {
        !matches!(
            word.to_lowercase().as_str(),
            "second" | "third" | "fourth" | "fifth" | "sixth" | "other"
        )
    });
    let kind = super::nominal::name(&bare, lex);
    if carriers.contains(&kind) {
        kind
    } else {
        np_key(&np, lex)
    }
}

fn check_call(
    call: Call<'_>,
    name: &str,
    signature: &Signature,
    lex: &Lexicon,
    table: &BTreeMap<String, VocabEntry>,
    carriers: &BTreeSet<String>,
) -> Result<(), String> {
    let Some(actor) = call.actor else {
        return Err(format!("predicate `{name}` needs an actor of type `{}`. Supply an explicit agent or use the active voice", signature.arguments[0].name()));
    };
    let mut actual: Vec<(Vec<&Np>, &str)> = vec![(actor.nouns().iter().collect(), "entity")];
    if let Some(object) = call.object {
        actual.push((object.nouns().iter().collect(), "object"));
    }
    for role in call.roles {
        if call.passive && matches!(role, RolePp::Agent(_)) {
            continue;
        }
        let nouns = role_nps(role);
        if !nouns.is_empty() {
            actual.push((nouns, "object"));
        }
    }
    if call.content {
        actual.push((Vec::new(), "proposition"));
    }
    if actual.len() != signature.arguments.len() {
        let expected = signature
            .arguments
            .iter()
            .map(Sort::name)
            .collect::<Vec<_>>()
            .join(", ");
        return Err(format!(
            "predicate `{name}` expects ({expected}), with {} arguments. This use supplies {}",
            signature.arguments.len(),
            actual.len()
        ));
    }
    for (at, (expected, (nouns, kind))) in signature.arguments.iter().zip(actual).enumerate() {
        if kind == "proposition" && !matches!(expected, Sort::Proposition) {
            return Err(format!(
                "argument {} of `{name}` expects `{}` but this use supplies a proposition",
                at + 1,
                expected.name()
            ));
        }
        for noun in nouns {
            let actual = argument_name(noun, lex, carriers);
            let declared = table
                .get(&actual)
                .and_then(|entry| entry.declared_kind.as_deref())
                .unwrap_or(kind);
            let declared = if declared == "class" && carriers.contains(&actual) {
                kind
            } else {
                declared
            };
            if !expected.accepts(&actual, declared) {
                return Err(format!("argument {} of `{name}` expects `{}` but this use supplies `{actual}` ({declared})", at + 1, expected.name()));
            }
        }
    }
    Ok(())
}

pub(super) fn check(
    set: &SpecSet,
    lex: &Lexicon,
    table: &BTreeMap<String, VocabEntry>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let documents = || {
        set.packages
            .iter()
            .flat_map(|package| &package.documents)
            
    };
    let mut signatures = BTreeMap::new();
    for doc in documents() {
        let scoped = lex.in_document(doc);
        for decl in &doc.predicates {
            let name = scoped.local_name(&decl.name);
            let at = SpecRef::point(
                &decl.file,
                decl.line,
                &format!("predicate {}({})", decl.name, decl.signature.join(", ")),
            );
            let mut arguments = Vec::with_capacity(decl.signature.len());
            for written in &decl.signature {
                let kind = written.to_lowercase();
                if KINDS.contains(&kind.as_str()) {
                    arguments.push(Sort::Kind(kind));
                } else if kind == "proposition" {
                    arguments.push(Sort::Proposition);
                } else {
                    match scoped.resolve_explicit(written) {
                        Ok(ty) if scoped.known(&ty) && table.get(&ty).is_some_and(|entry| {
                            entry.signature.is_none()
                                && entry.declared_kind.as_deref().is_none_or(|kind| matches!(kind, "entity" | "object" | "class"))
                        }) => arguments.push(Sort::Named(ty)),
                        Ok(_) => diagnostics.push(Diagnostic::error("UNRESOLVED_TERM", format!("predicate `{name}` needs a known argument type for `{written}` in the declaring namespace"), vec![at.clone()])),
                        Err(message) => diagnostics.push(Diagnostic::error("UNRESOLVED_TERM", message, vec![at.clone()])),
                    }
                }
            }
            if !arguments.is_empty() && arguments.len() == decl.signature.len() {
                signatures.insert(
                    name,
                    Signature {
                        arguments,
                        origin: at,
                    },
                );
            }
        }
    }
    if signatures.is_empty() {
        return;
    }

    let carriers: BTreeSet<String> = documents()
        .flat_map(|doc| {
            let scoped = lex.in_document(doc);
            doc.individuals
                .iter()
                .map(move |decl| scoped.resolve(&scoped.canon(&decl.name)))
        })
        .collect();
    for doc in documents() {
        let scoped = lex.in_document(doc);
        for spec in doc.specs.iter().chain(&doc.symbol_sources) {
            let at = SpecRef {
                id: spec.display_id(),
                file: spec.file.clone(),
                line: spec.line,
                text: spec.sentence.source.clone(),
            };
            let mut seen = BTreeSet::new();
            rules::calls(&spec.sentence, &mut |call| {
                let lemma = if call.passive {
                    participle_base(&call.verb.to_lowercase(), &scoped)
                } else {
                    verb_lemma(call.verb, &scoped)
                };
                let name = match scoped.resolve_explicit(&lemma) {
                    Ok(name) => name,
                    Err(message) => {
                        if seen.insert(message.clone()) {
                            diagnostics.push(Diagnostic::error(
                                "AMBIGUOUS_TERM",
                                message,
                                vec![at.clone()],
                            ));
                        }
                        return;
                    }
                };
                let Some(signature) = signatures.get(&name) else {
                    return;
                };
                if let Err(message) = check_call(call, &name, signature, &scoped, table, &carriers)
                {
                    if seen.insert(message.clone()) {
                        diagnostics.push(Diagnostic::error(
                            "vocabulary-kind-conflict",
                            message,
                            vec![at.clone(), signature.origin.clone()],
                        ));
                    }
                }
            });
        }
    }
}
