# 001 Introducing propositional analysis

Timed assume-guarantee (A/G) contracts ask questions beyond the scope of propositional valuations, such as whether an implementation can respond to every admissible input. We chose classical two-valued propositional logic for the initial analysis. The requirements are part of [the current trion specification](../../spec/trion.trion). [Propositional analysis requirements](../../spec/propositional/analysis.trion)

`trion formalize` validates the input and saves the formal artifact and its provenance as JSON. `trioc analyze` produces an analysis record bound to that artifact. The semantics identifier `classical-propositional/1` fixes how the artifact is interpreted. A conversion between A/G contracts and propositional logic needs a defined domain and a semantic preservation contract.

The backend worker checks finite Boolean problems in negation normal form. Running it in a separate process allows the runner to distinguish a timeout or forced termination from acceptance of a result. The reference evaluator evaluates Core expressions directly. [Evidence for F01–F08](../foundation/evidence-index.md)
