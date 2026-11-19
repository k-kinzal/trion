# Verification and trust boundary

## Gate 1. The formal model

We check the [propositional model](../../formal/Trion/Propositional.lean) with the Lean 4.35.0 toolchain pinned under `formal/`. During `lake build`, `#guard_msgs` checks the recorded list of axioms used by the theorems. Those axioms are propositional extensionality (`propext`) and quotient soundness (`Quot.sound`). The verification trusts the Lean kernel, those two axioms, and the review of whether the theorems express the normative specification.

| Requirement | Theorems and scope | Preconditions |
| --- | --- | --- |
| M01 | `eval_correct` relates the recursive Boolean evaluator to a separately defined truth predicate. | Finite trees and total valuations. Every reference is a `Fin n`. |
| M02 | `expand_correct` preserves the predicate semantics of implication during expansion. | Well-formed surface trees. Parsing text is outside the theorem's scope. |
| M03 | `query_condition_exact`, `translate_exact`, and `target_query_exact` cover the NNF adapter. `mmt_formula_exact` preserves truth at every valuation. `mmt_question_exact` preserves satisfiability and nonvacuous entailment for the propositional MMT fragment. | Total valuations over the same declaration slots. Each distinct declared name denotes one nullary MMT relation. |
| M04 | `witness_correct`, `valuations_complete`, `valuation_count`, `empty_valuation`, `cut_off`, `exclusion_correct`, `unsat_sound`, and `entails_sound` establish witness and exhaustive-check soundness. | Finite declarations covering every reference, finite expression trees, and a sufficient budget for exhaustive conclusions. |

For zero slots, `empty_valuation` and `valuations_complete` cover the empty valuation. Evaluation, expansion, translation, and valuation generation use structural recursion. The model and the reference evaluator both enumerate the false branch of the first slot before the true branch.

## Gate 2. Implementation conformance

The Rust implementation shares the Core expression type, slot order, and validated document and question between input processing, the reference evaluator, and the adapter. The reference evaluator's recursion and enumeration are independent of the backend's NNF translation, evaluation, and enumeration.

Conformance tests and fault injection exercise the correspondence between Rust and the model, the grammar, JSON and digests, dependency direction, result acceptance and reporting, and OS process control. Whether the grammar's interpretation captures the intent of source material depends on the source conventions or a confirmation record.

The MMT theorems cover the Boolean formulas and the questions they form. The MMT reader checks that each propositional obligation agrees with its archived Core input. The certificate checker verifies backend answers against the MMT questions. The reference evaluator independently checks recovered valuations against the original Core and compares each decided answer with enumeration when the budget covers all valuations. Larger universal results carry checked certificate evidence. The Rust lowering, MMT reader and serializer, witness recovery, and the binding and replay code are exercised by conformance and fault injection. [MMT lowering](../../crates/trion-verification/src/analysis/references.rs) · [Evidence acceptance and replay](../../crates/trioc-cli/src/propositional.rs) · [CLI conformance tests](../../crates/trion-cli/tests/analysis_cli.rs)

The Lean reference discusses theorem validation and the trusted checker. [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
