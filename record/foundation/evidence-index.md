# Propositional analysis evidence index

This index links the normative definitions, the Lean theorems, and the Rust conformance tests. The [local verification record](propositional-verification.md) identifies the snapshots and reports the results. The [trust boundary](trust-boundary.md) records the scope of each check and the remaining trust assumptions.

| Requirement | Normative definition and mechanical checks | Conformance tests and faults detected |
| --- | --- | --- |
| F01. Versioned normative semantics | [Core](../../spec/propositional/core.trion) and [proof obligations](../../spec/obligations.trion). Lean checks M01 and M02. | [Worked examples](../../tests/adapters/boolean.rs) and [grammar tests](../../tests/grammar/propositional.rs) catch reversed implications. |
| F02. Closed formal structure | [Well-formedness and interchange](../../spec/propositional/core.trion). Lean limits the domain with `Expr n` and `Fin n`. | [Core conformance tests](../../tests/conformance/core.rs) reject unknown constructors, extra fields, out-of-range references, malformed data, and duplicates. |
| F03. Independent Core | [Design decision](../decisions/001-foundation-scope.md) and [extension rules](../../spec/extensions.trion). | [Cargo dependency graph](../../crates/trion-cli/tests/self_hosting.rs) and [adapter replacement](../../tests/architecture/propositional.rs) catch prohibited dependencies and unchecked backend capability. |
| F04. Premise and question tracking | [Proof obligations](../../spec/obligations.trion), [results](../../spec/propositional/results.trion), and [CNL provenance](../../spec/grammar.trion). | [CLI tests](../../crates/trion-cli/tests/analysis_cli.rs) and [fault injection](../../tests/fault-injection/analysis.rs) reject altered premises and answers bound to a different question or premise set. MMT readback checks the lowered questions against their archived Core. |
| F05. Translation conditions and preservation | [NNF contract](../../spec/propositional/translation.trion), [propositional MMT mapping](../../spec/extensions.trion), and [M03 theorems](../../formal/Trion/Propositional.lean). | [Independent comparison](../../tests/adapters/boolean.rs), [adapter replacement](../../tests/architecture/propositional.rs), [fault injection](../../tests/fault-injection/analysis.rs), and [MMT readback tests](../../crates/trion-cli/tests/analysis_cli.rs). |
| F06. Conclusions bound to evidence | [Results](../../spec/propositional/results.trion). Lean checks M04. | [Result acceptance](../../tests/adapters/boolean.rs), [fault injection](../../tests/fault-injection/analysis.rs), and [CLI tests](../../crates/trion-cli/tests/analysis_cli.rs) exercise invalid candidates, contradictory premises, unknown, interruption, timeout, and absent scope. The MMT tests also exercise the exhaustive and checked certificate evidence paths. |
| F07. Version pinning and replay | [Interchange](../../spec/propositional/core.trion) and [extension rules](../../spec/extensions.trion). | [Version pinning](../../tests/grammar/propositional.rs) and [replay](../../crates/trion-cli/tests/analysis_cli.rs) reject changes to old interpretations, version mismatches, and tampering with translation or evidence. |
| F08. Scope of guarantees | [Trust boundary](trust-boundary.md), [translation contract](../../spec/propositional/translation.trion), and [results](../../spec/propositional/results.trion). | [Lean checks](../../formal/Trion/Propositional.lean), [limited-result injection](../../tests/fault-injection/analysis.rs), and [local verification](propositional-verification.md). |

## M01–M04

The [trust boundary](trust-boundary.md) lists the theorems and axioms of the [Lean model](../../formal/Trion/Propositional.lean). Runtime tests for M04 check that each valuation over three propositions can serve as the sole witness to a question and that zero propositions have exactly one witness, the empty valuation. [Core conformance tests](../../tests/conformance/core.rs)

The independent comparison generates 32 cases for each proposition count from zero to four. It uses a maximum expression depth of five, up to three premises, and seed `0x8af7_239b_0061_c45d`. It generates constants, declared references, negation, conjunction, and disjunction, alternating satisfiability and entailment questions. Additional comparisons fix the premises to each valuation or consistently rename the propositions. Hand-worked examples cover implication, its converse, contradiction, and the empty valuation. The tests define the properties separately from the input generator. [Conformance tests](../../tests/adapters/boolean.rs) and [QuickCheck paper](https://research.chalmers.se/en/publication/237427)

## Completion criteria

| Criterion from Section 15 | Evidence |
| --- | --- |
| F01–F08, all constructors, and well-formedness | The requirement table, [self-hosting checks](../../crates/trion-cli/tests/self_hosting.rs), and [Core specification](../../spec/propositional/core.trion). |
| M01–M04, their premises and axioms | [Lean model](../../formal/Trion/Propositional.lean) and [trust boundary](trust-boundary.md). |
| Deployed CLI, independent evaluation, and Core dependencies | [End-to-end tests](../../crates/trion-cli/tests/analysis_cli.rs), [generated comparison](../../tests/adapters/boolean.rs), and [Cargo dependency checks](../../crates/trion-cli/tests/self_hosting.rs). |
| Traceability of premises, questions, translations, evidence, and scope | [End-to-end tests](../../crates/trion-cli/tests/analysis_cli.rs) and [F04–F07 fault injection](../../tests/fault-injection/analysis.rs). |
| Ambiguity, unsupported input or backend, unknown, contradiction, and failure | [Grammar tests](../../tests/grammar/propositional.rs), [result tests](../../tests/adapters/boolean.rs), and [process failure tests](../../tests/fault-injection/analysis.rs). |
| Detection of individual faults | [Fault injection](../../tests/fault-injection/analysis.rs), [dependency checks](../../crates/trion-cli/tests/self_hosting.rs), and [the per-fault verification record](propositional-verification.md). |
| Grammar extension and replacement with a restricted adapter | [Architecture tests](../../tests/architecture/propositional.rs). |
| Version pinning, evidence replay, and migration | [Interchange](../../spec/propositional/core.trion), [migration rules](../../spec/extensions.trion), and [version regression tests](../../tests/grammar/propositional.rs). |
| Handling of undefined diagram, table, and pseudocode semantics | [Extension rules](../../spec/extensions.trion) and [rejection tests](../../tests/grammar/propositional.rs). |
| Model proofs, conformance tests, and confirmation of source intent | [Trust boundary](trust-boundary.md) and [source provenance contract](../../spec/extensions.trion). |
| Evidence bound to one snapshot | [Git snapshot and verification results](propositional-verification.md). |
| Local verification | [Verification record](propositional-verification.md) for the locked workspace build, Rust conformance tests, and Lean checks. |
| Native tables and obligation mappings | [Table conformance tests](../../crates/trion-cli/tests/tables.rs) and [self-hosting tests](../../crates/trion-cli/tests/self_hosting.rs) check equivalent MMT readings, direct references to the independent obligation file, source locations, rendering, and rejection of malformed rows. |
