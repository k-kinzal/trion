# moxi

Reading and writing [MoXI](https://github.com/ModelChecker/IL), the model
checking intermediate language: an abstract syntax, a reader (text to syntax,
with line and column on every error) and a printer (syntax to text, total, and
read back to an equal value) for MoXI scripts and `check-system` responses.

The crate follows `description.md` of the MoXI repository at commit
`b5156d5ead225fceb37a40b1ec337968ea2c767b` (2025-03-31). Sorts, terms and
symbols are those of the [`smtlib`](../smtlib) crate (SMT-LIB 2.7), read in a
dialect that admits `'` in simple symbols for next-state variables.

```rust
use moxi::{Command, Script};

fn main() -> Result<(), moxi::Error> {
    let script: Script = "(set-logic QF_LIA)
(define-system Delay :input ((i Int)) :output ((o Int))
  :init (= o 0)
  :trans (= o' i))
(check-system Delay :input ((i Int)) :output ((o Int))
  :reachable (r (> o 3))
  :query (q (r)))".parse()?;

    let Command::DefineSystem(delay) = &script.commands()[1] else { unreachable!() };
    assert_eq!(delay.input().map(|vars| vars.len()), Some(1));
    assert_eq!(script.to_string().parse::<Script>()?, script);
    Ok(())
}
```

Syntax can also be built with constructors (`DefineSystem::new(name).with_input(…)?`,
`CheckSystem::new(name).with_attribute(…)`, `moxi::parse_term`) and printed
with `Display`. Constructors reject what the reader could not have produced
(SMT-LIB 2.7 term productions, constants and binders of other dialects, text
nested deeper than the reader accepts), so printed text always reads back to
an equal value.

## What is checked, and what is not

The crate reads and writes the grammar. It rejects what the grammar of the
document rules out: commands other than the five adopted SMT-LIB commands and
`declare-enum-sort`, `define-system`, `check-system` (unadopted SMT-LIB
commands are reported as unsupported); unknown, repeated or misplaced
attributes; values of the wrong shape; the productions SMT-LIB 2.7 added to
the term grammar (`lambda`, the `_` pattern; MoXI terms are those of SMT-LIB
2.6), reported as unsupported; text nested deeper than the limit of
`moxi::dialect()`, which is smtlib's default (a `Depth` error; reading,
printing and dropping are iterative).

It does **not** check static semantics: declarations, sorts, the arity of
theory symbols, where primed variables may occur, whether subsystems match the
systems they instantiate, whether queries name defined formulas, or logic
restrictions. A program that produces MoXI should run its output through a
MoXI tool, such as the sort checker of
[moxi-mc-flow](https://github.com/ModelChecker/moxi-mc-flow), in its tests.

## Tests

- `tests/description_examples.rs`: every example of the document, verbatim,
  with the verdict of the reader and the position of each error.
- `tests/reader.rs`: the reader's rules one by one.
- `tests/properties.rs`: round trips over generated syntax, deep and large
  inputs, and a reader that never panics on random or mangled text.
- `tests/differential.rs`: comparison with moxi-mc-flow (commit
  `b61c98188d246e157a6f5f759b012749855b8fbc`) on its corpus and on generated
  scripts. These tests are ignored by default; run them with
  `cargo test -p moxi -- --include-ignored` after placing moxi-mc-flow in
  `.tools/moxi-mc-flow` at the repository root or setting `MOXI_MC_FLOW` to
  its directory (they need `python3`). moxi-mc-flow is GPLv3; none of its files
  is part of this crate.
