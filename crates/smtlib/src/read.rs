//! A helper shared by the readers that turn [`Spanned`] trees into syntax.

use crate::error::Result;
use crate::sexpr::Spanned;

/// Checks that `items` (the arguments after a head) has exactly `n` items.
pub(crate) fn arity(node: &Spanned, items: &[Spanned], n: usize, production: &str) -> Result<()> {
    if items.len() == n {
        Ok(())
    } else {
        Err(node.error(format!("{production} takes {n} argument(s), found {}", items.len())))
    }
}
