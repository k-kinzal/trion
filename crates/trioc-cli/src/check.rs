//! Findings as every command writes them, and what a normative statement
//! says that no rule reads.

use trion_language::{Diagnostic, Severity};
use trion_verification::Analysis;

/// The meaning obligations of an analysis as diagnostics: what a normative
/// statement says and no rule reads. Every view reports them as errors.
pub fn unread_of(analysis: &Analysis) -> Vec<Diagnostic> {
    let silence = &analysis.silence;
    silence.opaque.iter().chain(&silence.ungrounded).chain(&silence.inexpressible).cloned().collect()
}

/// How a diagnostic is written: its level and code, its message, and the
/// places that it is about.
pub fn written(d: &Diagnostic) -> String {
    let level = match d.severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
        Severity::Info => "info",
    };
    let mut out = format!("{level}[{}]: {}\n", d.code, d.message);
    for r in &d.refs {
        out.push_str(&format!("  {}:{} [{}] {}\n", r.file, r.line, r.id, r.text));
    }
    out
}
