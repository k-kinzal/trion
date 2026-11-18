//! Tests below the interface of the crate: the certificates of the solver
//! that decides the obligations for `trioc`, and the decision of an
//! obligation. The tests of the interface itself are in `tests/`.

// The helpers are those of `tests/`: there they are a crate of their own,
// so their items are public.
#[allow(unreachable_pub, dead_code)]
#[path = "../../../trion-checker/src/certificate.rs"]
mod checker;
#[allow(unreachable_pub)]
#[path = "../../tests/common/mod.rs"]
mod common;

mod certificates;
mod solver;
mod verification;
