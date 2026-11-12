//! Reads which syntactic forms a sentence uses, in the vocabulary of EARS.
//!
//! The forms are plain values, so a specification set decides what is
//! acceptable: `stdlib/ears` encloses them in a closed domain, and a form
//! outside that domain needs an `extend` declaration.

use super::ast::*;

/// The syntactic forms of a sentence: one EARS pattern when the sentence has
/// one, and every form that lies outside the EARS patterns.
pub fn syntax_forms(s: &Sentence) -> Vec<&'static str> {
    let mut forms = Vec::new();
    let core = match &s.core {
        Core::Conjoined { items } => items.first().unwrap_or(&s.core),
        other => other,
    };
    match core {
        Core::Definition { .. } => return vec!["Definition"],
        Core::Description { .. } | Core::Relation { .. } | Core::Existence { .. } | Core::Conjoined { .. } => forms.push("Description"),
        Core::Deontic { modal, negated, .. } => {
            forms.push(pattern(&s.frames));
            match modal {
                Modal::Shall => {}
                Modal::Must => forms.push("Must"),
                Modal::Should => forms.push("Recommendation"),
                Modal::May => forms.push("Permission"),
            }
            if *negated {
                forms.push("Prohibition");
            }
        }
    }
    let temporal = |keyword: &str| matches!(keyword.to_ascii_lowercase().as_str(), "after" | "once" | "upon" | "before" | "until" | "during" | "on");
    if s.frames.states.iter().any(|f| temporal(&f.keyword)) || s.frames.trigger.as_ref().is_some_and(|t| temporal(&t.keyword)) {
        forms.push("Temporal-opener");
    }
    if s.exception.is_some() {
        forms.push("Exception");
    }
    if s.purpose.is_some() {
        forms.push("Purpose");
    }
    forms
}

/// The EARS pattern of a sentence's frames.
fn pattern(frames: &Frames) -> &'static str {
    let scoped = !frames.scopes.is_empty();
    let stated = !frames.states.is_empty();
    let trigger = frames.trigger.as_ref().map(|t| t.keyword.to_ascii_lowercase());
    match (scoped, stated, trigger.as_deref()) {
        (false, false, None) => "Ubiquitous",
        (true, false, None) => "Optional-feature",
        (false, true, None) => "State-driven",
        (false, false, Some("if")) => "Unwanted-behaviour",
        (false, false, Some(_)) => "Event-driven",
        _ => "Complex",
    }
}
