# Local verification of propositional analysis

The baseline commit was `ef14d84`. All runs recorded here were local. The first implementation check used working-tree content identifier `5307a8a5a1fb8a2dc7fbc0570fcad48b1a32fcf0d3aabbd127b819d91813e9c4`. Each section records results for the configuration at the time of that run.

The initial changes added a propositional fragment, an equivalent grammar extension, and an exact backend. The [evidence index](evidence-index.md) traces F01–F08. The existing entry points handle timed A/G contracts and MMT. Propositional artifacts use JSON and the definition environment `empty/1`. [Design decision 001](../decisions/001-foundation-scope.md) and [architecture survey](current-architecture.md)

## Demonstration

Run these commands from the repository root. P represents a valid card and Q represents permission to enter. Q follows from the two premises, and the CLI prints `entails`. The analysis record checker evaluates all four valuations against the original expressions and confirms that the premises have a model.

```sh
cargo build --locked -p trion-cli --bins
target/debug/trion formalize tests/fixtures/propositional/card.cnl > target/card.core.json
target/debug/trioc analyze target/card.core.json > target/card.analysis.json
target/debug/trioc replay target/card.analysis.json
```

Run `target/debug/trioc replay tests/fixtures/propositional/card.analysis.json` to check the saved [analysis record](../../tests/fixtures/propositional/card.analysis.json). Separate commands handle conversion and analysis. The alternate spelling `assume if P then Q.` expands to the same Core under `--grammar propositional-cnl/2`.

On acceptance, `trion formalize` emits an artifact that records the input status. Ambiguous, unsupported, and invalid inputs produce a diagnostic with a location and exit code 1. `trioc analyze` writes the record to standard output and a summary to standard error. Unknown, contradictory premises, and timeouts also return exit code 1. Exit code 0 from `replay` indicates that the saved result agreed with the replay.

The default backend and reference limits are 4,096 valuations each. The backend timeout is 5,000 ms, and `process-runner/1` reads at most 1 MiB of output. The record retains the original question and the guarantee scope when a setting limits the search. The worker is deterministic.

## First implementation checks

The local environment was macOS arm64, Rust 1.92.0, Lean 4.35.0, and Python 3.9.6. `Cargo.lock` pinned the Cargo dependencies.

| Check | Command or method | Result |
| --- | --- | --- |
| Propositional model | Lean theorem and axiom checks | All 13 target theorems passed, including a rerun in an empty working directory with just the model and tool configuration. |
| Existing A/G model | `lake build` in `formal/` | Passed. |
| Standalone Core and forbidden dependencies | Cargo build and dependency checks | Passed. Adding a backend dependency to the actual Cargo graph caused rejection. |
| Workspace regression | `PROPTEST_RNG_SEED=19 cargo test --locked --workspace --quiet` | 1,193 passed, 0 failed, 22 pre-existing ignored. |
| Fault injection | Mutations to the implementation at the time | All 11 caused their corresponding tests to fail. Workspace tests also covered forced termination, modified evidence, and a bounded answer. |
| CLI demonstration and replay | Commands in the demonstration | Confirmed entailment of Q and premise consistency. Replayed the saved record and reproduced it byte for byte with the same settings. |

Lean checks the M01–M04 model. Worked examples, independent comparison, and fault injection check the Rust implementation, serialization, and process integration. The [extension rules](../../spec/extensions.trion) govern confirmation of source intent and future migrations. [Verification and trust boundary](trust-boundary.md)

## Checks after moving the requirements to trion

The checked content identifier was `6901e9cb615fb776e7f59114363aa3313f414e66e195ca18add5afb4ed592f1c`. `trion` converted the standalone propositional requirements package of that revision to MMT without warnings or errors. `trioc prove` proved the two A/G obligations for consistency and compatibility at three moments and three individuals. M01–M04 check the propositional model separately.

- Fourteen CLI and self-hosting tests passed, including the check that the propositional requirements generate contracts for F01–F08.
- `cargo test --locked` passed 22 tests across the five crates for Core, reference evaluation, CNL, backend, and analysis.
- The Lean theorem and dependency checks passed.

## Checks after integration into the current trion specification

The checked content identifier was `9b1a32a4ff0df9d30b51ed180f259546645f507a5b914ed12d960858f95ae291`. The [current trion specification](../../spec/trion.trion) includes [propositional analysis](../../spec/propositional/analysis.trion). Replay uses the semantics version in the saved artifact.

- `trion . --out target/current-spec-mmt` wrote MMT and `trioc prove target/current-spec-mmt` proved all 13 bounded obligations at the default bounds. The conversion reported the same vocabulary warning as the baseline.
- Thirteen self-hosting and CLI tests passed. They confirmed that the current specification includes F01–F08 and that the saved analysis record can be replayed.
- Lean rechecked all 13 target theorems.

## Checks after revising names and verification tooling

Git tree `3ac200e8101f9eff0f88655b415854fe3528465a` identifies the checked snapshot. A temporary index and `git write-tree` captured the working tree, excluding this record. The saved propositional semantics identifier was `classical-propositional/1`. The demonstration records were regenerated from their original inputs.

- `trion . --out target/propositional-current-spec` and `trioc prove target/propositional-current-spec` proved 13 bounded obligations from the current specification.
- `cargo check --locked -p trion-core` and `cargo test --locked -p trion-cli --test self_hosting --test analysis_cli` passed. The dependency test rejected `smtlib` when it was added to Core as a build dependency in a copy.
- `cargo test --locked --workspace --test adapters --test fault_injection` passed nine tests. The tests exercised abnormal termination and timeout in an actual Rust child process.
- `cargo mutants` from cargo-mutants 27.1.0 detected all 11 selected mutations. They exercised candidate binding, external response classification, model checking, and exhaustive reference enumeration.
- `lake build` passed in `formal/`. Lean's `#guard_msgs` checked the propositional model's theorems and their axioms.
- `PROPTEST_RNG_SEED=19 cargo test --locked --workspace --quiet` recorded 1,194 passed, 0 failed, and 22 pre-existing ignored.

## Checks after separating proof obligations and surface syntax

Git tree `f1de3d3fcc8d5c1bbe213279a6378fec54cf5878` identifies the source and dependency configuration. A temporary Git index captured the working tree without this record.

- `trion` converted a standalone copy of `spec/obligations.trion` with an empty project environment. `trioc prove` proved its two document obligations.
- `trion` converted the full specification and `trioc prove` proved all 14 recorded obligations. The new `check/CARD-ACCESS` proved both premise satisfiability and entailment. [Executable check](../../spec/grammar.trion)
- All 17 self-hosting and analysis CLI tests passed. The MMT cases covered both conditional spellings, a counterexample to the converse, contradictory premises, the empty valuation, and rejection outside the pinned grammar. [Self-hosting tests](../../crates/trion-cli/tests/self_hosting.rs) and [CLI tests](../../crates/trion-cli/tests/analysis_cli.rs)
- `cargo test --workspace --locked --offline` recorded 1,197 passed, 0 failed, and 22 pre-existing ignored.
- `lake build` passed in `formal/`. The Lean gate covers the model and the NNF adapter contract. The MMT mapping has its separate CLI conformance tests. [Trust boundary](trust-boundary.md)

## Completion audit

Git tree `726705e229ed821933661fab886536d04ae8b47f` identifies the audited source and dependency configuration, captured without this record.

- `lake build` passed in a fresh directory. Lean checked preservation of formula truth and both kinds of propositional MMT obligation, with the axiom lists guarded. Removing the premises from the modeled MMT counterexample condition caused the preservation proof to fail. [MMT preservation theorems](../../formal/Trion/Propositional.lean)
- The locked Rust workspace build and all 42 targeted conformance and regression tests passed locally. The preceding section records the full workspace run with the external tools.

## Core-bound evidence in the MMT proof path

Git tree `9890b38d1d15b04f5eb40df81a942ef1929a3392` identifies the specification, formal model, implementation, and locked dependencies. The tree excludes the verification records under `record/`.

The executable `check CARD-ACCESS` binds the original checked input to the MMT questions. The proof report records the original grammar and Core, the lowered questions, the solver answers and certificate evidence, the bounds, and the result. For the converse, the verified counterexample is `P=false, Q=true`. Contradictory premises record classical entailment and a contradictory premise set, which refute the asserted nonvacuous obligation. [Executable check](../../spec/grammar.trion) · [Evidence acceptance and replay](../../crates/trioc-cli/src/propositional.rs)

Build the binaries and reproduce the proof and replay from the repository root.

```sh
cargo build --locked -p trion-cli --bins
target/debug/trion . --out target/propositional-mmt
target/debug/trioc prove target/propositional-mmt --json > target/propositional-mmt-proof.json
target/debug/trioc replay target/propositional-mmt-proof.json --form target/propositional-mmt
```

- `lake build` passed from a clean export of the source tree. The Lean kernel checked M01–M04 and the axiom guards, including the MMT formula and question preservation theorems.
- The current trion specification generated 14 obligations. `trioc prove` proved all 14. The propositional check had consistent premises, exhaustive evidence over four valuations, and the entailment conclusion. Replaying the saved report against the MMT archive rechecked its propositional result.
- `cargo test --workspace --locked --offline` passed with Rust 1.92.0. The run recorded 1,198 passed, 0 failed, and 22 pre-existing ignored. It included the external MMT type check of the self-hosting form, rechecking archived evidence, and the old form readback.

### Fault injection

An isolated export of the same tree was changed one fault at a time. Every mutation compiled and caused the named test to fail. The unknown and timeout cases were run separately. The local command was `cargo test --offline --locked -p PACKAGE --test TARGET -- TEST --exact`. For the dependency case Cargo updated the isolated lockfile before the test checked the actual dependency graph.

| Required fault | Injected change | Test that detected it |
| --- | --- | --- |
| Reverse an implication | Swap the operands of the written implication in the CNL lowering. | [`published_implication_expands_and_prints`](../../tests/grammar/propositional.rs) |
| Drop a constraint during translation | Omit the first premise of a multiple-premise MMT check. The independent evaluator rejects the lowered result for the card example. | [`propositional_checks_are_decided_from_the_mmt_form`](../../crates/trion-cli/tests/analysis_cli.rs) |
| Lose the empty valuation | Skip the visit for an empty assignment, losing the counterexample to entailment of false. | [`empty_universe_is_a_single_valuation`](../../tests/conformance/core.rs) |
| Ignore an unsupported constructor | Consume an unknown Core constructor and replace it with truth. | [`rejects_corrupt_forms_and_queries`](../../tests/conformance/core.rs) |
| Promote unknown or timeout to success | Return entailment after unknown and after timeout, in separate runs. | [`unknown_timeouts_and_malformed_output_do_not_become_success`](../../tests/fault-injection/analysis.rs) |
| Accept evidence from another question or premise set | Bypass the request identity check and pass a valuation that happens to satisfy the new question. | [`alien_evidence_is_refused_even_if_its_valuation_works`](../../tests/fault-injection/analysis.rs) |
| Change a fixed grammar version | Admit the second grammar's conditional spelling in the first grammar. | [`grammar_versions_pin_the_extension_and_old_associations`](../../tests/grammar/propositional.rs) |
| Insert an assumption into the original Core | Add positive P to the saved premises of the open question `entails P`. | [`replay_rejects_added_assumptions_and_fabricated_guarantees`](../../tests/fault-injection/analysis.rs) |
| Add a backend dependency to Core | Add the `smtlib` crate to the Core manifest. | [`the_core_has_no_language_or_backend_dependencies`](../../crates/trion-cli/tests/self_hosting.rs) |
| Omit the scope of a limited search | Suppress scope in the MMT result of a run with a decision limit. The Boolean adapter separately receives fabricated responses with missing or unsupported scopes. | [`mmt_propositional_proof_reports_limits_and_checked_certificates`](../../crates/trion-cli/tests/analysis_cli.rs) · [`bounded_and_missing_scope_responses_are_refused`](../../tests/fault-injection/analysis.rs) |

## Native specification tables

Git tree `83252f9f219ef1b93b7b5ba10d3ffb288e5c66a2` identifies the verified source with the records under `record/` excluded. This change adds document syntax and adopts it in the three specification files. Statement cells use the existing controlled sentence reader, including the surrounding scope. Reference cells use the existing package reference check and preserve the row that associates a surface form with a canonical obligation. [Obligation definitions](../../spec/obligations.trion) · [Grammar mappings](../../spec/grammar.trion) · [Extension syntax and mappings](../../spec/extensions.trion)

- `cargo test --workspace --locked --offline --test tables --test self_hosting --test pattern_ledger --test code_fixtures --test mmt_form --test document_rules --test analysis_cli` passed 51 targeted tests. They covered standalone obligations, ordinary and tabular statements with the same MMT meaning, both document renderers, invalid rows and unresolved references, and external MMT type checking.
- `lake build` passed in `formal/`. Conversion of the current specification wrote 11 tables in both HTML and Markdown. `trioc prove` proved all 14 obligations in the emitted MMT archive.
