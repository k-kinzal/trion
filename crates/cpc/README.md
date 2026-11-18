# cpc

Reading the proofs that [cvc5](https://cvc5.github.io/) 1.4.2 writes in its
Cooperating Proof Calculus (CPC), and writing them as proof files that
[Ethos](https://github.com/cvc5/ethos) checks.

- **Output.** `read_session` reads what cvc5 printed for the commands that
  were sent: SMT-LIB responses with the `smtlib` crate, CPC proofs (Eunoia
  text) with the `eunoia` crate, in one linear pass, with positions in the
  whole output. The caller says whether cvc5 ran with `--dump-proofs` and
  `print-success`.
- **Documents.** `ProofDocument` is a self-contained proof file as cvc5's
  `contrib/get-ethos-checker` writes it: the includes of the CPC signature
  (`Cpc.eo`, and `expert/CpcExpert.eo` for the expert variant) from a
  directory the caller names, then the proof. It is built from cvc5's output
  or from any script, can reference the SMT-LIB problem instead of declaring
  its symbols, prints to text that reads back to the same commands, and is
  written only inside the directory it is given.

The crate reads and writes; it checks no proof. Whether a document is a
well-formed and valid CPC proof is for Ethos to say. The crate contains no
file of cvc5 or Ethos.

## Example

```rust,no_run
use cpc::{ProofDocument, SessionOptions, Variant};

// `cvc5 --dump-proofs --proof-format-mode=cpc problem.smt2 > problem.out`
let problem = std::fs::read_to_string("problem.smt2")?;
let output = std::fs::read_to_string("problem.out")?;
let commands = cpc::smtlib::Script::parse(&problem)?.into_commands();
let options = SessionOptions::new().with_dump_proofs(true);

let sig_dir = "/opt/cvc5/proofs/eo/cpc"; // the caller's copy of cvc5's signature
for (k, doc) in ProofDocument::from_cvc5_output(&output, &commands, options, sig_dir, Variant::Expert)?.into_iter().enumerate() {
    doc.write(std::path::Path::new("."), &format!("proof-{k}.eo"), None)?; // then: ethos proof-0.eo
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Tests

The tests use the official signature, cvc5 1.4.2 and Ethos 0.2.5, which are
not part of this crate; they look for them when they run (see the crate
documentation). Ethos accepts every document the tests build from cvc5's
output and refuses mutated ones.
