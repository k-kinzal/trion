//! URIs of the symbols that reading treats specially: LF's application and
//! λ-abstraction, which the rule `LFHOAS` makes notations build, the type of
//! notation literals and the bracketing notations of `mmt?mmt`
//! (`api/utils/mmt.scala`, `api/notations/NotationExtension.scala`; the
//! URIs are those that MMT/urtheories declares).

use std::sync::OnceLock;

use crate::uri::{GlobalName, MPath};

fn module(s: &str) -> MPath {
    // the arguments are the constant URIs below, which parse
    MPath::parse_plain(s).unwrap_or_else(|e| unreachable!("{s}: {e}"))
}

macro_rules! symbol_path {
    ($(#[$doc:meta])* $name:ident, $module:expr, $sym:expr) => {
        $(#[$doc])*
        pub fn $name() -> GlobalName {
            static CELL: OnceLock<GlobalName> = OnceLock::new();
            CELL.get_or_init(|| module($module).sym($sym)).clone()
        }
    };
}

symbol_path!(
    /// `urtheories?LambdaPi?apply`: application.
    apply, "http://cds.omdoc.org/urtheories?LambdaPi", "apply"
);
symbol_path!(
    /// `urtheories?LambdaPi?lambda`: λ-abstraction.
    lambda, "http://cds.omdoc.org/urtheories?LambdaPi", "lambda"
);
symbol_path!(
    /// `mmt?mmt?notation`: the type of notation literals.
    notation_type, "http://cds.omdoc.org/mmt?mmt", "notation"
);
symbol_path!(
    /// `mmt?mmt?brackets`: bracketing, not part of the term.
    brackets_sym, "http://cds.omdoc.org/mmt?mmt", "brackets"
);
symbol_path!(
    /// `mmt?mmt?andrewsDot`.
    andrews_dot, "http://cds.omdoc.org/mmt?mmt", "andrewsDot"
);
symbol_path!(
    /// `mmt?mmt?andrewsDotRight`.
    andrews_dot_right, "http://cds.omdoc.org/mmt?mmt", "andrewsDotRight"
);

/// `mmt?mmt?brackets` and the two Andrews dots: bracketing, not part of the term.
pub fn brackets() -> [GlobalName; 3] {
    [brackets_sym(), andrews_dot(), andrews_dot_right()]
}
