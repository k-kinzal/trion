# eunoia

The Eunoia language of the [Ethos](https://github.com/cvc5/ethos) proof
checker in Rust: abstract syntax, a parser and a printer.

The language is the one described by the Ethos user manual at commit
`08e4aa40c4f8a6e00833f10e8d8985777e424027` (Ethos 0.2.5, the version that
cvc5 1.4.2 pins). Where the manual leaves a reading open, the Ethos sources at
that commit decide; the crate documentation cites the file for each such
place, and lists the constructs that are not supported.

- **Parser.** Every command of the manual's grammar is read, with errors at
  line and column (in characters). A part of a larger text is read with its
  positions in that text (`parse_script_at`), so a reader of a solver's
  output need not copy or re-read anything.
- **Printer.** Printing is total and reads back to an equal value. Where the
  grammar requires at least one element (`<x>+`), the abstract syntax holds a
  `NonEmpty`, so no value prints outside the grammar.
- **Grammar only.** The crate gives no meaning to a script: declarations,
  rules, scopes and types are for Ethos to check. Its tests run Ethos on the
  printed form of every regression test of Ethos and require the same verdict
  and output as on the original.
- **Robust.** Terms of any depth are handled with explicit stacks (parser,
  printer, `Clone`, `PartialEq`, `Hash`, `Debug`, `Drop`); no input makes the
  crate panic; reading is linear in the length of the text.

## Example

```rust
use eunoia::{parse_script, Command, ParseErrorKind, Position, Script, Step, Symbol, Term};

let script = parse_script("(declare-const p Bool)\n(assume @p1 p)")?;
assert_eq!(script.position(1), Some(Position::new(2, 1)));

// build a command and print the script
let mut step = Step::new(Symbol::new("@p2").unwrap(), Symbol::new("refl").unwrap());
step.conclusion = Some(Term::symbol("p").unwrap());
step.premises = Some(vec![Term::symbol("@p1").unwrap()]);
let mut script: Script = script;
script.push(Command::Step(step));
assert_eq!(script.to_string(), "(declare-const p Bool)\n(assume @p1 p)\n(step @p2 p :rule refl :premises (@p1))\n");

// errors say where
let err = parse_script("(assume @p1 (! p))").unwrap_err();
assert!(matches!(err.kind, ParseErrorKind::Syntax(_)));
assert_eq!(err.position, Position::new(1, 17));
# Ok::<(), eunoia::ParseError>(())
```

## Tests

Besides unit, robustness (100 000 levels of nesting) and property tests
(round trips, reader totality), the conformance tests read the manual's
examples and Ethos's regression tests from the Ethos sources at the pinned
commit and run Ethos 0.2.5; neither is part of this crate (see the crate
documentation for where the tests look for them).
