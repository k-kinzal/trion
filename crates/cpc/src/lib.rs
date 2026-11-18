//! cpc: reading the proofs that cvc5 1.4.2 writes in its Cooperating Proof
//! Calculus, and writing them as proof files that Ethos checks.
//!
//! # Specification
//!
//! The Eunoia signature of CPC in `proofs/eo/cpc` of cvc5 at the tag
//! `cvc5-1.4.2` (<https://github.com/cvc5/cvc5/tree/cvc5-1.4.2/proofs/eo/cpc>),
//! entry points `Cpc.eo` and `expert/CpcExpert.eo`, and the script
//! `contrib/get-ethos-checker` of the same tag, which builds checkable proof
//! files from cvc5's output. The language of the signature is Eunoia as
//! defined by the Ethos user manual at Ethos commit
//! `08e4aa40c4f8a6e00833f10e8d8985777e424027`, which that script pins; this
//! crate reads and prints it with the `eunoia` crate and models nothing of
//! Eunoia itself; the SMT-LIB responses around the proofs are read with the
//! `smtlib` crate.
//!
//! The crate contains no file of cvc5 or Ethos. A [`ProofDocument`] includes
//! the signature from the directory the caller names, as `get-ethos-checker`
//! does.
//!
//! | Module | Implements |
//! | - | - |
//! | [`output`] | reading cvc5's output for the commands sent: SMT-LIB responses (read by `smtlib`) and CPC proofs (read by `eunoia`) |
//! | [`document`] | self-contained proof documents (the includes of `cpc_gen.sh` plus one proof), optionally with a `reference` to the problem |
//!
//! # Example
//!
//! ```no_run
//! use cpc::{ProofDocument, SessionOptions, Variant};
//!
//! // a problem and cvc5's output for it
//! let problem = std::fs::read_to_string("problem.smt2")?;
//! let output = std::fs::read_to_string("problem.out")?; // cvc5 --dump-proofs --proof-format-mode=cpc
//! let commands = cpc::smtlib::Script::parse(&problem)?.into_commands();
//! let options = SessionOptions::new().with_dump_proofs(true);
//! for doc in ProofDocument::from_cvc5_output(&output, &commands, options, "/opt/cvc5/proofs/eo/cpc", Variant::Expert)? {
//!     doc.write(std::path::Path::new("."), "proof.eo", None)?; // then: ethos proof.eo
//! }
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! # What is specific to CPC, and what is not
//!
//! The crate is a bridge: it is the one place that needs both `smtlib` (the
//! responses around the proofs) and `eunoia` (the proofs), so that neither of
//! those depends on the other. Of what it holds:
//!
//! - **Specific to CPC and cvc5 1.4.2:**
//!   - the entry points of the signature, `Cpc.eo` and `expert/CpcExpert.eo`
//!     ([`Variant`]);
//!   - where cvc5 puts a proof in its output: after `unsat` under
//!     `--dump-proofs`, and as the response to `get-proof`, in both cases a
//!     parenthesized list of Eunoia commands ([`read_session`]);
//!   - the shape of `cpc_gen.sh`'s documents: the includes, then the proof
//!     ([`ProofDocument`]).
//! - **Generic, from Ethos and Eunoia:** the syntax of the proofs (all of it is
//!   the `eunoia` crate's); `include` and `reference` and their rules (a
//!   document that references its problem must not declare the problem's
//!   symbols, manual "Validation Proofs via Reference Inputs"); and keeping
//!   the files a document is written to inside one directory.
//! - **Generic, from SMT-LIB:** every response other than a proof, read by
//!   the `smtlib` crate for the command it answers.
//!
//! # Format only
//!
//! The crate reads and writes; it checks no proof. A proof that names a rule
//! CPC does not have, gives a rule the wrong number of premises, or uses a
//! premise out of scope reads and prints as written. Ethos decides whether a
//! document is a well-formed and valid CPC proof; this crate never claims it.
//!
//! # Tools of the tests
//!
//! The crate runs no tool and reads no file it is not given. Its tests use
//! the official signature and two tools, which are not part of the
//! repository: Ethos is the judge of every document the tests build. The tests look for them when they run: tools in the
//! repository's `.tools/bin`, then on `PATH`; the signature in
//! `$CPC_SIGNATURE_DIR`, else `.tools/cvc5-signature`. A test whose input is
//! missing prints what it needs and passes without checking, unless
//! `CPC_REQUIRE_TOOLS=1` is set, which makes it fail; a tool of another
//! version always fails it.
//!
//! | Input | Pinned version | Used by |
//! | - | - | - |
//! | `.tools/cvc5-signature` | `proofs/eo/cpc` of cvc5 tag `cvc5-1.4.2` | `tests/ethos.rs`: the documents include it |
//! | cvc5 | 1.4.2 | `tests/proofs.rs` and `tests/sessions.rs`: the stored outputs are its output (`CPC_UPDATE_CORPUS=1` regenerates them) |
//! | Ethos | 0.2.5, commit `08e4aa40c4f8a6e00833f10e8d8985777e424027` (pinned by cvc5 1.4.2's `contrib/get-ethos-checker`) | `tests/ethos.rs`: every document built here is accepted by Ethos, and mutated ones are refused |

#![warn(unreachable_pub)]

/// The examples of `README.md`, compiled and run as doctests.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
struct ReadmeDoctests;

pub mod document;
pub mod output;

pub use smtlib;

pub use document::{DocumentError, ProofDocument, Variant};
pub use output::{read_proofs, read_responses, read_session, Answer, OutputError, Proof, Response, SessionOptions};
