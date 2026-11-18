//! Diagnostics: every finding is reported through [`Diagnostic`], under a
//! code of the registry [`CODES`].

use serde::Serialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Error,
    Warning,
    Info,
}

/// The position and source text of a specification or declaration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SpecRef {
    pub id: String,
    pub file: String,
    pub line: usize,
    pub text: String,
}

impl SpecRef {
    /// A place in a file that has no identifier of its own: it is named by
    /// its file and its line.
    pub fn point(file: &str, line: usize, text: &str) -> SpecRef {
        SpecRef { id: format!("{file}:{line}"), file: file.to_string(), line, text: text.to_string() }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Diagnostic {
    pub severity: Severity,
    /// The machine-readable kind, such as `contradiction`, `shape-violation`
    /// or `missing-case`.
    pub code: String,
    pub message: String,
    pub refs: Vec<SpecRef>,
}

impl Diagnostic {
    pub fn error(code: &str, message: impl Into<String>, refs: Vec<SpecRef>) -> Self {
        debug_assert!(CODES.contains(&code), "the diagnostic code `{code}` is not registered in CODES");
        Self {
            severity: Severity::Error,
            code: code.to_string(),
            message: message.into(),
            refs,
        }
    }

    pub fn warning(code: &str, message: impl Into<String>, refs: Vec<SpecRef>) -> Self {
        debug_assert!(CODES.contains(&code), "the diagnostic code `{code}` is not registered in CODES");
        Self {
            severity: Severity::Warning,
            code: code.to_string(),
            message: message.into(),
            refs,
        }
    }

    pub fn info(code: &str, message: impl Into<String>, refs: Vec<SpecRef>) -> Self {
        debug_assert!(CODES.contains(&code), "the diagnostic code `{code}` is not registered in CODES");
        Self {
            severity: Severity::Info,
            code: code.to_string(),
            message: message.into(),
            refs,
        }
    }
}

/// Every code that trion can report. A diagnostic with a code outside this
/// list is a defect, and a debug build stops on it, so that no code exists
/// without a place in `trion check --codes`.
pub const CODES: &[&str] = &[
    "alias-conflict",
    "alias-cycle",
    "AMBIGUOUS_REFERENCE",
    "AMBIGUOUS_TERM",
    "check-refuted",
    "compatibility-revision",
    "compatibility-source-unknown",
    "detail-not-refining",
    "context-dependent",
    "composite-not-distributive",
    "composite-not-its-expansion",
    "context-second-trigger",
    "contradiction",
    "incompatible",
    "detail-incomplete",
    "obligation-unproved",
    "CYCLIC_DEFINITION",
    "CYCLIC_REFINEMENT",
    "definition-collapsed",
    "definition-in-context",
    "derivation-refused",
    "DUPLICATE_ID",
    "example-failed",
    "example-invalid",
    "extend-open-domain",
    "flow-guard-obligation",
    "FLOW_BAD_REFERENCE",
    "FLOW_START",
    "INCLUDE_CYCLE",
    "INCOMPLETE_FLOW_CHOICE",
    "inexpressible-property",
    "manifest-vocabulary-mode",
    "missing-case",
    "missing-required-form",
    "MISSING_PREDICATE",
    "MISSING_SOURCE",
    "NAME_COLLISION",
    "namespace-package",
    "namespace-unknown",
    "NOT_CONTROLLED_ENGLISH",
    "order-dependent",
    "OVERLAPPING_FLOW_GUARDS",
    "package-in-include",
    "package-mismatch",
    "package-missing",
    "parse-block",
    "parse-check",
    "parse-citation",
    "parse-compatibility",
    "parse-composition",
    "parse-concept",
    "parse-diagram",
    "parse-diagram-kind",
    "parse-example",
    "parse-flow",
    "parse-form-regex",
    "parse-form-rule",
    "parse-include",
    "parse-name",
    "parse-note",
    "parse-package",
    "parse-placement",
    "parse-priority",
    "parse-reference",
    "parse-refinement",
    "parse-role-line",
    "parse-scenario",
    "parse-sentence",
    "parse-source",
    "parse-spec-id",
    "priority-unsupported",
    "prover-failed",
    "recommendation-violation",
    "relation-not-local",
    "result-stale",
    "round-trip-differs",
    "scenario-differs",
    "scenario-failed",
    "scenario-invalid",
    "scenario-unsupported",
    "sentence-not-one-contract",
    "shape-violation",
    "source-changed",
    "source-coverage-below-minimum",
    "source-kind-unknown",
    "source-quote-ambiguous",
    "source-quote-not-found",
    "source-quote-partial",
    "source-quote-unused",
    "source-unreadable",
    "syntax-not-allowed",
    "system-undeclared",
    "UNBOUND_VARIABLE",
    "ungrounded",
    "UNGROUPED_RESPONSE_OPERATORS",
    "unit-mismatch",
    "unrealizable",
    "unresolved-import",
    "UNRESOLVED_CITATION",
    "UNRESOLVED_REFERENCE",
    "UNRESOLVED_TEMPORAL_SCOPE",
    "UNRESOLVED_TERM",
    "unsourced",
    "UNSUPPORTED_DIAGRAM_KIND",
    "UNSUPPORTED_FLOW_CYCLE",
    "UNSUPPORTED_SEMANTICS",
    "vocabulary-kind-ambiguous",
    "vocabulary-kind-conflict",
    "vocabulary-redeclared",
    "vocabulary-similar",
    "vocabulary-unknown-kind",
    "witness-refused",
];
