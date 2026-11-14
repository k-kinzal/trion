//! The claims of a verification, kept apart.
//!
//! One analysis decides several things, and each says something else: that
//! the statements without normative force have a model, that a behaviour
//! keeps every contract, that each situation has a response, that a
//! property follows. A result names the claim that it is about, the bounds
//! under which the claim was examined, and what stands behind the verdict.
//! No verdict of one claim is shown as the verdict of another.
//!
//! Beside the claims stand the meaning obligations: the parts of normative
//! statements that the reading accepted and gave no meaning. While one is
//! left, a claim that was proved was proved of a weaker text, so it is not
//! proved of the statements as they are written.

use super::*;
use trion_language::reading::Silence;

/// The verdict of a claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Verdict {
    /// The claim holds of the stated text within the stated bounds, and the
    /// evidence that the claim names was checked.
    Proved,
    /// The claim fails within the stated bounds.
    Refuted,
    /// The meaning and the question are defined, and the question is not
    /// decided: the reason says why.
    Unknown,
    /// A part of the meaning has no rule, or no method decides the claim.
    Unsupported,
    /// The text that the claim is about is not well formed.
    Invalid,
    /// A proof did not check, or two checkers disagreed.
    Error,
    /// Nothing asked for the claim.
    NotRequested,
}

impl Verdict {
    pub fn as_str(self) -> &'static str {
        match self {
            Verdict::Proved => "proved",
            Verdict::Refuted => "refuted",
            Verdict::Unknown => "unknown",
            Verdict::Unsupported => "unsupported",
            Verdict::Invalid => "invalid",
            Verdict::Error => "error",
            Verdict::NotRequested => "not_requested",
        }
    }
}

/// The bounds under which a claim was examined. They are bounds of the
/// analysis and not of the specification: a statement that closes a domain
/// states the domain, and a bound of the search states only how far the
/// search looked.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AnalysisRange {
    /// The moments of each trace; the rest of the trace follows them.
    pub moments: usize,
    /// The individuals of each type, when a statement is read over individuals.
    pub individuals: Option<usize>,
    /// The individuals of each type that the settings asked for.
    pub individuals_requested: usize,
    /// The decisions that one query may make; no limit when null.
    pub decisions: Option<u64>,
}

impl AnalysisRange {
    /// The range as a phrase of a report.
    pub fn phrase(&self) -> String {
        let individuals = self.individuals.map_or(String::new(), |n| format!(", domains of {n} individuals"));
        let decisions = self.decisions.map_or(String::new(), |n| format!(", {n} decisions for each query"));
        format!("traces of {} moments{individuals}{decisions}", self.moments)
    }
}

/// A part of a normative statement that was accepted and has no meaning
/// rule, or whose meaning no claim examines.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Obligation {
    /// `unread_part`, `ungrounded_statement`, `undefined_quality`.
    pub reason: String,
    /// The code of the diagnostic that reports the part.
    pub code: String,
    pub statement: Option<SpecRef>,
    /// What is left unread and what would give it a meaning.
    pub message: String,
}

/// One claim with its verdict and what the verdict covers.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Claim {
    /// `background_sat`, `contract_sat`, `situation_total`,
    /// `property_entails`, `scenario_satisfiable`, `scenario_reachable`,
    /// `reactive_realizable` or `implementation_conforms`.
    pub claim: String,
    /// The block that asks for the claim, when a block does.
    pub subject: Option<String>,
    pub verdict: Verdict,
    /// Why the verdict is not `proved` or `refuted`, as a code:
    /// `resource_limit`, `quantifier_method_incomplete`,
    /// `unresolved_meaning`, `malformed_block`, `no_method`, and so on.
    pub reason: Option<String>,
    /// The claim holds because nothing is in its range: no situation, or
    /// premises without a model. Such a claim is proved and counts for nothing.
    pub vacuous: bool,
    /// Whether the package is verified only when this claim is proved.
    pub required: bool,
    /// What the claim says, in a sentence.
    pub statement: String,
    /// What the claim does not say.
    pub not_claimed: String,
    pub range: AnalysisRange,
    /// Whether the verdict holds beyond the range. No method of this
    /// edition lifts a result: the abstraction of the rest of the trace and
    /// the bound of the domains are assumed and not proved.
    pub lifted: bool,
    /// How the formulas relate to the meaning: `exact within the range`, or
    /// `over-approximation` when a part of the text was left out.
    pub relation: String,
    pub method: String,
    /// What stands behind the verdict.
    pub evidence: Vec<String>,
    /// The statements whose unread parts keep the claim from being proved.
    pub unresolved: Vec<String>,
}

/// What the claims and the obligations make of a package.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Claims {
    pub claims: Vec<Claim>,
    pub obligations: Vec<Obligation>,
}

impl Claims {
    /// Each required claim that is not proved, or is proved of nothing.
    pub fn unproved(&self) -> Vec<&Claim> {
        self.claims.iter().filter(|c| c.required && (c.verdict != Verdict::Proved || c.vacuous)).collect()
    }

    /// The claim of a name that no block asks for.
    pub fn of(&self, name: &str) -> Option<&Claim> {
        self.claims.iter().find(|c| c.claim == name && c.subject.is_none())
    }
}

const NOT_CLAIMED: [(&str, &str, &str); 8] = [
    ("background_sat", "the statements without normative force have a model", "that each situation that a use of the system needs is among the models"),
    ("contract_sat", "a behaviour keeps every contract", "that each situation that can occur has a response"),
    ("situation_total", "each situation that the statements without normative force allow has a response that keeps every statement that applies in it", "that a system can choose the response without knowing what the environment does later"),
    ("property_entails", "the property holds in every model of its premises", "any property that the check does not state"),
    ("scenario_satisfiable", "the situation of the scenario is allowed by the statements without normative force", "that a behaviour reaches the situation from an initial state"),
    ("scenario_reachable", "a behaviour reaches the scenario from an initial state", "that the scenario always occurs"),
    ("reactive_realizable", "a strategy answers each history that it has observed", "that a program follows the strategy"),
    ("implementation_conforms", "the behaviours of an implementation are among those that the statements allow", "any purpose that the statements do not state"),
];

fn sentences(name: &str) -> (String, String) {
    NOT_CLAIMED.iter().find(|(claim, _, _)| *claim == name).map_or((String::new(), String::new()), |(_, says, not)| (says.to_string(), not.to_string()))
}

/// The meaning obligations of a package: each unread part, each statement
/// that constrains nothing, and each quality that nothing defines.
pub(super) fn obligations(silence: &Silence) -> Vec<Obligation> {
    let of = |reason: &str, d: &Diagnostic| Obligation { reason: reason.to_string(), code: d.code.clone(), statement: d.refs.first().cloned(), message: d.message.clone() };
    silence.opaque.iter().map(|d| of("unread_part", d)).chain(silence.ungrounded.iter().map(|d| of("ungrounded_statement", d))).chain(silence.inexpressible.iter().map(|d| of("undefined_quality", d))).collect()
}

/// What the analysis decided, as claims.
pub(super) struct Decided<'a> {
    pub model: &'a Model,
    pub requested: Bounds,
    /// Whether the statements without normative force have a model.
    pub background: Status,
    pub consistency: &'a ConsistencyResult,
    pub checks: &'a [CheckOutcome],
    pub unrealizable: &'a [SpecRef],
    pub searched: bool,
}

/// Builds the claims of an analysis.
pub(super) fn claims(decided: &Decided, obligations: Vec<Obligation>) -> Claims {
    let range = AnalysisRange { moments: decided.requested.trace_length.max(2), individuals: decided.model.instance_scope, individuals_requested: decided.requested.scope, decisions: decided.requested.decisions };
    let mut unresolved: Vec<String> = obligations.iter().filter_map(|o| o.statement.as_ref()).map(|r| r.id.clone()).collect();
    unresolved.sort();
    unresolved.dedup();
    let open = !obligations.is_empty();
    let relation = if open { "over-approximation: the unread parts are left out, so a model of the formulas need not be a model of the statements" } else { "exact within the range: the rest of the trace and the bound of the domains are assumed" };
    let limit = |status: Status| (status == Status::Unknown).then(|| if decided.searched { "resource_limit".to_string() } else { "not_searched".to_string() });
    let claim = |name: &str, subject: Option<String>, verdict: Verdict, reason: Option<String>, vacuous: bool, required: bool, evidence: Vec<String>| {
        let (statement, not_claimed) = sentences(name);
        // A model of a weaker text proves nothing of the text: what was
        // proved with a part unread is not proved, and a refutation of the
        // weaker text is a refutation of the text.
        let (verdict, reason) = match verdict {
            Verdict::Proved if open && required => (Verdict::Unsupported, Some("unresolved_meaning".to_string())),
            other => (other, reason),
        };
        Claim { claim: name.to_string(), subject, verdict, reason, vacuous, required, statement, not_claimed, range: range.clone(), lifted: false, relation: relation.to_string(), method: decided.consistency.method.clone(), evidence, unresolved: if required { unresolved.clone() } else { Vec::new() } }
    };
    let of_status = |status: Status| match status {
        Status::Satisfiable => Verdict::Proved,
        Status::Unsatisfiable => Verdict::Refuted,
        Status::Unknown => Verdict::Unknown,
    };
    let model = |what: &str| vec![format!("a model of {what} within the range, found by the built-in solver")];
    let refutation = |what: &str| vec![format!("a refutation of {what} within the range, found by the built-in solver")];
    let evidence = |status: Status, what: &str| match status {
        Status::Satisfiable => model(what),
        Status::Unsatisfiable => refutation(what),
        Status::Unknown => Vec::new(),
    };
    let mut out = Vec::new();
    out.push(claim("background_sat", None, of_status(decided.background), limit(decided.background), false, true, evidence(decided.background, "the statements without normative force")));
    // Without a model of the background no behaviour exists, whatever the contracts say.
    let status = if decided.background == Status::Unsatisfiable { Status::Unsatisfiable } else { decided.consistency.status };
    out.push(claim("contract_sat", None, of_status(status), limit(status), false, true, evidence(status, "the contracts")));
    let total = if decided.background == Status::Unsatisfiable {
        // No situation can occur: each of them has a response, and that says nothing.
        claim("situation_total", None, Verdict::Proved, None, true, true, vec!["no situation can occur: the statements without normative force have no model".to_string()])
    } else {
        match decided.consistency.verdict.as_str() {
            "consistent" => claim("situation_total", None, Verdict::Proved, None, false, true, vec![decided.consistency.situations.clone().unwrap_or_default()]),
            "inconsistent" => claim("situation_total", None, Verdict::Refuted, None, false, true, vec!["a situation that can occur, in which the statements that apply cannot all be kept".to_string()]),
            _ => claim("situation_total", None, Verdict::Unknown, Some(if !decided.searched { "not_searched" } else if decided.requested.decisions.is_some() { "resource_limit" } else { "quantifier_method_incomplete" }.to_string()), false, true, decided.consistency.situations.clone().into_iter().collect()),
        }
    };
    out.push(total);
    // The premises of a check are the background and the definitions that
    // reach its sides. Where they have no model the check is not proved
    // (`check-environment-inconsistent`): it would follow whatever it says.
    for check in decided.checks {
        let (verdict, reason) = match check.result.as_str() {
            "proved" => (Verdict::Proved, None),
            "refuted" => (Verdict::Refuted, None),
            "invalid" => (Verdict::Invalid, Some("malformed_block".to_string())),
            "unsupported" => (Verdict::Unsupported, Some("unresolved_meaning".to_string())),
            _ => (Verdict::Unknown, Some("resource_limit".to_string())),
        };
        out.push(claim("property_entails", Some(format!("check {}", check.name)), verdict, reason, false, true, Vec::new()));
    }
    // No block of this edition states a scenario, a strategy or an implementation.
    for name in ["scenario_satisfiable", "scenario_reachable", "implementation_conforms"] {
        out.push(claim(name, None, Verdict::NotRequested, None, false, false, Vec::new()));
    }
    // A guarantee that no system can keep refutes the strategy; nothing
    // proves one. A refuted claim is required: a package whose statements no
    // system can keep is not verified, whoever asked.
    out.push(if decided.unrealizable.is_empty() {
        claim("reactive_realizable", None, Verdict::NotRequested, None, false, false, Vec::new())
    } else {
        claim("reactive_realizable", None, Verdict::Refuted, None, false, true, decided.unrealizable.iter().map(|r| format!("`{}` requires a response that the environment can always come before", r.id)).collect())
    });
    Claims { claims: out, obligations }
}
