# smtlib

The syntax of [SMT-LIB](https://smt-lib.org/) version 2.7: an abstract
syntax, a reader (text to syntax, with line and column on every error) and a
printer (syntax to text, total, and read back to an equal value) for
S-expressions, sorts, terms, scripts and command responses.

The crate follows *The SMT-LIB Standard, Version 2.7* (Barrett, Fontaine,
Tinelli; release 2026-09-09), Chapter 3 and Appendix B. It has no
dependencies, starts no threads and has no build script.

```rust
use smtlib::{Command, Script, Term};

fn main() -> Result<(), smtlib::Error> {
    let script: Script = "(set-logic QF_LIA)
(declare-const x Int)
(assert (! (> x 0) :named positive))
(check-sat)".parse()?;

    let Command::Assert(term) = &script.commands()[2] else { unreachable!() };
    assert!(matches!(term, Term::Annotated(..)));
    assert_eq!(script.to_string().parse::<Script>()?, script);

    let error = "(assert (> x 0)".parse::<Script>().unwrap_err();
    assert_eq!(error.position().map(|p| (p.line(), p.column())), Some((1, 1)));
    Ok(())
}
```

Responses are read by the command they answer:

```rust
use smtlib::{Dialect, GeneralResponse, Script};

let script = Script::parse("(declare-const x Int) (check-sat) (get-value (x))").unwrap();
let answers = GeneralResponse::parse_session("sat ((x 1))", script.commands(), false, &Dialect::strict()).unwrap();
assert_eq!(answers.len(), 2);
```

## What the crate is, and is not

It is the grammar. Every production of Appendix B is read and printed,
including the additions of 2.7 (`declare-sort-parameter`, `define-const`,
`lambda`, the `_` wildcard in patterns, terms in `check-sat-assuming` and
`get-unsat-assumptions`). Every `+` of the grammar is a `NonEmpty`, so a
value built through the API prints as text the grammar accepts.

It does not check sorts, declarations, theory signatures, logics, the order
of model definitions, or what a command means in a session; it knows no
theory or logic. Theory and logic declarations (§3.7, §3.10) are read as
S-expressions only.

## Dialects

The default `Dialect` is strict SMT-LIB 2.7. A format built on SMT-LIB can
add, explicitly: characters in simple symbols (`with_symbol_char`, as MoXI
does with `'`), the literals `-1`, `-1.5` and `1/2`
(`with_extended_literals`, as Alethe writes them), binders named by a symbol
(`with_binder`, such as `choice`), and the nesting limit (`with_max_depth`).

## Limits

- The reader rejects nesting deeper than the dialect's limit (1000 by
  default) with an error of kind `Depth`. Reading, printing, traversal
  (`Term::iter`, `Term::fold`) and dropping are iterative; the derived
  `Clone`, `PartialEq`, `Hash`, `Ord` and `Debug` recurse, and are tested at
  the limit on a 2 MiB stack in a debug build.
- `Term`, `Sort`, `SExpr` and `Spanned` implement `Drop` (to drop without
  recursion), so they are matched by reference rather than destructured by
  move.
- SMT-LIB 2.6 is read as far as 2.7 reads it; there is no 2.6 mode.

## Evidence

- `tests/reference_examples.rs`: the examples of the reference, section by
  section, read, printed and read back.
- `tests/properties.rs`: `parse(print(x)) == x` on generated values of every
  syntax type, deep and wide ones included; the reader never panics on
  random or mangled text; values at the depth limit on a 2 MiB stack.
- `tests/differential.rs`: cvc5 1.4.2 and z3 4.15.4 (from `.tools/bin` or
  `PATH`, versions checked). Ignored by default; run with
  `cargo test -p smtlib -- --ignored`, where a missing tool fails the test.
