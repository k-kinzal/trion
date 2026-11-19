# Architecture at the start of the work

The baseline was `ef14d84`. The table records the architecture at that revision. Expected results for propositional inputs follow from the current definition. [Propositional semantics and interchange](../../spec/propositional/core.trion)

| Asset | Entry points and responsibilities at the baseline | Treatment |
| --- | --- | --- |
| `AGENTS.md`, `spec/*.trion`, `spec/semantics/`, `spec/patterns/ledger.toml` | A/G contracts, responsibility, time and individuals, and the pattern ledger | Retained. Added propositional analysis to the current specification. |
| `formal/Trion/`, `formal/Oracle.lean` | Contract sets, merging, sentence expansion, document soundness, and the expansion oracle. Lean 4.35.0 | Retained. Reused the toolchain to check a separate model of propositional analysis. |
| `trion-language` | `document.rs` and `syntax/` process input. `reading/` interprets it using `trion-solver::Formula`. | Kept outside Core so Core can meet F03. |
| `trion-solver`, `trion-verification` | Arithmetic, quantification, proof search, responsibility, time, structure, proof obligations, and output formats | Retained. The initial propositional analysis used a separate, small translation contract. |
| `trion-checker` | `eval.rs` checks concrete behavior. `derive.rs` rechecks readings. Both use existing language and formula types. | Retained. The propositional reference evaluator uses an independent implementation. |
| `trion-cli`, `trioc-cli`, `mmt` | `trion --out` converts to MMT and documents. `trioc prove` decides each obligation and produces supported proof formats. | Retained. Added entry points and an interchange format for propositional analysis. |
| `smtlib`, `alethe`, `cpc`, `eunoia`, `moxi` | Backend format libraries and tests with external checkers | Kept outside the propositional analysis path. That path checks evidence against the original expressions. |
| `stdlib/`, `editors/`, `trion-lsp` | Vocabulary, editor integration, and the language server | Retained. Editor enhancements were outside the initial scope. |
| Rust crate tests and `formal/lakefile.lean` | Existing regression tests for contracts, readings, and proof formats, plus the Lean build. | Retained. Added local propositional conformance and dependency checks. |

We inspected dependencies with `cargo tree --workspace --locked --depth 1 -e normal`, read entry points in the libraries and CLI, and checked the formal model with `lake build` in `formal/`. The survey excluded a full review of legacy patterns against the propositional acceptance criteria, conversion between the existing MMT form and propositional analysis, and manual editor testing. [Local verification results](propositional-verification.md)
