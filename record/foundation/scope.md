# Initial scope of propositional analysis

The initial analysis covered classical two-valued logic over declared propositions. Its expressions used truth, falsity, negation, conjunction, and disjunction, with implication as syntactic sugar. Its questions were premise satisfiability and entailment. An empty declaration environment has exactly one valuation, the empty valuation. [Current propositional analysis specification](../../spec/propositional/analysis.trion)

| Premises and question | Expected result |
| --- | --- |
| Assume P. Does P follow? | P follows from consistent premises. |
| Assume P → Q and P. Does Q follow? | Q follows from consistent premises. |
| Assume P → Q and Q. Does P follow? | The valuation P = false and Q = true refutes entailment. |
| Assume P and ¬P. Does Q follow? | Q follows vacuously because the premises contradict each other. |
| Does false follow with no declarations or premises? | The empty valuation is a counterexample. |
| Reference undeclared R or declare P twice. | Invalid. |
| Write `P and Q or R` without parentheses. | Ambiguous, even with valid declarations and tokens. |
| Write `always Q`. | Unsupported. |

The initial work excluded A/G responsibility and duties, arithmetic, quantification, state updates, time, probability, concurrency, general recursion, context-dependent references, and automatic extraction from diagrams or tables. We chose a versioned empty definition environment. Named definitions, approximate adapters, certificate formats, a semantic contract connecting to A/G, and encoding into the existing MMT form were follow-up design topics.

See the [architecture survey](current-architecture.md) for the treatment of existing assets and [decision 001](../decisions/001-foundation-scope.md) for the rationale.
