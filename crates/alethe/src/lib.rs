//! The Alethe proof format: reading and writing the concrete syntax of
//! proofs, and reading the proofs a solver prints.
//!
//! ```
//! let text = "(assume h1 (= a b))\n(step t1 (cl (= b a)) :rule symm :premises (h1))\n";
//! let proof = alethe::Proof::parse(text)?;
//! assert_eq!(proof.to_text(), text);
//! # Ok::<(), alethe::Error>(())
//! ```
//!
//! # Specification
//!
//! *The Alethe Proof Format: An Evolving Specification and Reference*,
//! Haniel Barbosa, Mathias Fleury, Pascal Fontaine, Hans-Jörg Schurr et
//! al., typeset 2025-11-19. The document states "Version not known"; this
//! crate follows that typeset of it, archived at
//! <https://web.archive.org/web/2025id_/https://verit.gitlabpages.uliege.be/alethe/specification.pdf>
//! (original location <https://verit.gitlabpages.uliege.be/alethe/specification.pdf>).
//! Section and page numbers in this crate refer to that document. Where the
//! document is silent, the reference is the source of Carcara's development
//! branch at commit `20bf49c5ce31089ac83118574c888669355aaae1` (Apache-2.0,
//! <https://github.com/ufmg-smite/carcara/tree/20bf49c5ce31089ac83118574c888669355aaae1>),
//! cited by file relative to that commit's tree.
//!
//! | Module | Implements |
//! | - | - |
//! | [`term`] | Figure 2 (p. 9): ⟨proof_term⟩ as `smtlib` terms read in the Alethe dialect (⟨rational⟩, ⟨nonpositive_numeral⟩, ⟨nonpositive_decimal⟩, `choice`), the restriction of ⟨symbol⟩, the SMT-LIB 2.6 subset; §4.1 (p. 24): the concrete syntax `(_ @bvn i)` of the bit-vector constant |
//! | [`proof`] | §2.1 and Figure 2: `assume`, `step`, `anchor`, `define-fun`, ⟨clause⟩, the annotations and their order |
//! | [`output`] | Splitting solver output into responses and proofs |
//!
//! Everything that is SMT-LIB comes from the `smtlib` crate: the lexer,
//! S-expressions, terms, sorts, `define-fun` and their printer. The Alethe
//! additions to the lexicon are switches of its reader ([`dialect`]).
//!
//! # The problem of a proof
//!
//! "Every Alethe proof is associated with an SMT-LIB problem that is proved
//! by the Alethe proof. This can either be a concrete problem file or, if
//! the incremental solving commands of SMT-LIB are used, the implicit
//! problem constructed at the invocation of a get-proof command" (§2.1).
//! The problem is an SMT-LIB script, which the `smtlib` crate reads and
//! prints; this crate has no type for it. When a solver prints several
//! proofs for one script, the problem of each is the problem the script
//! has built at the check command the proof answers: for instance the
//! script's prefix ending at that command. Choosing and storing it is the
//! consumer's business, and so are files: Carcara reads a problem file and
//! a proof file holding the commands of [`Proof::to_text`].
//!
//! # Scope: syntax only
//!
//! This crate reads and writes the grammar. It does not check the static
//! semantics of a proof (unique indices, premises in scope, closed
//! anchors, well-sorted terms, assumptions that are assertions of the
//! problem, the rule list of §5.2) nor whether a step follows by its rule.
//! Both are obtained by running a proof checker such as Carcara on the
//! output; the tests of this crate do so (`tests/carcara.rs`). Nor does it
//! read or write files.
//!
//! # Supported subset
//!
//! Read and printed: the whole proof grammar of Figure 2 — `assume`,
//! `step` with `:rule`, `:premises`, `:args`, the `:discharge` annotation
//! of cvc5, veriT and Carcara, and any extra attributes (kept and printed
//! back); `anchor` with `:step` and a context of variables and
//! `(:= (x S) t)` mappings; `define-fun`; proof terms with `choice`,
//! rationals and nonpositive literals. The printer is total, and
//! [`Proof::parse`] of [`Proof::to_text`] gives back an equal proof.
//!
//! Rejected as syntax errors: commands other than the four, a conclusion
//! that is not `(cl …)`, the predefined annotations out of order or
//! repeated, `:premises ()`, `:args ()`, a `choice` over other than one
//! variable, the removed context form `(:= x t)`, and a ⟨symbol⟩ that
//! spells a number literal (`|-1|`; Figure 2).
//!
//! Rejected as unsupported: what SMT-LIB 2.7 added to the grammar of terms
//! of SMT-LIB 2.6 (`lambda`, the `_` wildcard of `match` patterns), since
//! Figure 2 takes ⟨term⟩ from SMT-LIB 2.6 ([`term`]). The HO-Core symbols
//! `@` and `->` are theory symbols, read as symbols. Nesting deeper than the reader's limit is an
//! [`ErrorKind::Depth`] error; the limit is stated at [`dialect`].
//!
//! # Where the specification is read one way among several
//!
//! - Step arguments are terms, not the ⟨step_arg⟩ tuples of Figure 2
//!   ([`proof`]).
//! - Every list headed by `choice` is the binder, so `choice` cannot be
//!   applied as a function in a proof ([`term`]).
//! - `(_ @bvn i)` is the bit vector of width n encoding i, as §4.1 writes
//!   it ("We write (_ @bv𝑛 𝑖 ) for bv𝑖𝑛"), the reverse of SMT-LIB's
//!   `(_ bvX n)` ([`term::bv_constant`]).
//!
//! # Evidence
//!
//! The tests read the examples of the document verbatim (cited by example
//! and page) and print them back; read proofs produced by cvc5 1.4.2 for
//! propositional, QF_UF, QF_LIA, QF_LRA, QF_BV and quantified problems
//! (kept in `tests/corpus`) and print them back; check by property tests
//! that printing then reading gives back generated proofs, deep and large
//! ones included, that the nesting the constructors count is the nesting
//! of the printed text, and that reading arbitrary or mangled text returns
//! a value or an error and never panics; and run Carcara on the proofs
//! this crate writes.
//!
//! The reference tools are pinned. A test that needs one is marked
//! `#[ignore]` with a message naming the tool and version, and is run with
//! `cargo test -- --include-ignored`; it then looks for the tool in the
//! repository's `.tools/bin`, then on `PATH`, checks its version, and fails
//! if it is missing.
//!
//! | Tool | Version | Used by |
//! | - | - | - |
//! | `cvc5` | cvc5 1.4.2 | `tests/regenerate.rs`: the corpus is what it prints, and fresh proofs read back |
//! | `carcara` | development branch, commit `20bf49c5ce31089ac83118574c888669355aaae1` (`carcara --version` contains "git 20bf49c") | `tests/carcara.rs`: it accepts the corpus proofs with their problems, refuses mutations of them, and its reading of the bit-vector constant is recorded |

#![warn(unreachable_pub, missing_docs)]

mod error;
pub mod output;
pub mod proof;
pub mod term;

pub use error::{Error, ErrorKind, Result};
pub use output::{read_output, read_proofs, SolverResponse};
pub use proof::{Anchor, Assume, Command, ContextAssignment, DefineFun, Proof, Step};
pub use term::dialect;
