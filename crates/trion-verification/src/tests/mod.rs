//! Tests below the interface of the crate: the search and its certificates,
//! the environment of a question, and formulas of the proof rebuilt beside
//! it. The tests of the interface itself are in `tests/`.

// The helpers are those of `tests/`: there they are a crate of their own,
// so their items are public.
#[allow(unreachable_pub)]
#[path = "../../tests/common/checker.rs"]
mod checker;
#[allow(unreachable_pub)]
#[path = "../../tests/common/mod.rs"]
mod common;

mod certificates;
mod proof;
mod solver;
mod verification;
