# alethe

Reading and writing the [Alethe proof format](https://verit.gitlabpages.uliege.be/alethe/specification.pdf)
(*The Alethe Proof Format: An Evolving Specification and Reference*, typeset 2025-11-19).

The crate models the grammar only (Figure 2 of the specification):

- `Proof`, `Command` (`Assume`, `Step`, `Anchor`, `DefineFun`) and `ContextAssignment`, with
  constructors that keep the grammar's invariants, a reader with line:column errors, and a printer
  whose output reads back to an equal value;
- proof terms as `smtlib` terms read in the Alethe dialect (number literals `-1`, `-1.5`, `1/2`
  and the `choice` binder), with the restriction of ⟨symbol⟩ and the SMT-LIB 2.6 subset;
- splitting solver output into its responses and proofs (`read_output`, `read_proofs`).

It reads and writes text, not files: storing a proof next to its SMT-LIB problem (for instance as
`<stem>.smt2` and `<stem>.smt2.alethe`, the naming Carcara uses) is the caller's business.

```rust
let text = "(assume h1 (= a b))\n(step t1 (cl (= b a)) :rule symm :premises (h1))\n";
let proof = alethe::Proof::parse(text).unwrap();
assert_eq!(proof.to_text(), text);
```

It does not check whether a proof is well formed beyond its syntax (unique indices, premises in
scope, sorts, the rule list) or valid. Run a proof checker such as
[Carcara](https://github.com/ufmg-smite/carcara) on the output for that; the tests of this crate do.

## Tests

`cargo test` runs the specification's examples, a corpus of cvc5 1.4.2 proofs and property tests.
The tests that run external tools (cvc5 1.4.2 and Carcara at commit `20bf49c`) are ignored by
default; with the tools in the repository's `.tools/bin` or on `PATH`, run them with
`cargo test -- --include-ignored`.
