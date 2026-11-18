//! What a prover is asked: the questions of an obligation as an SMT-LIB
//! script and as MoXI queries, so that any solver or model checker decides
//! them again, and the checks of the witnesses that answer the satisfiable
//! ones.

mod alethe_proof;
mod cpc_proof;
mod derivation;
pub(crate) mod smt;

pub use derivation::{derive, Derivation};
pub use smt::{asked, moxi_script, moxi_text, problem, questions, script_of, Check, Names, Questions, LOGIC};

/// The crates of the formats that the questions and their proofs are
/// written in, whose values this module returns.
pub use {alethe, eunoia, moxi, smtlib};
