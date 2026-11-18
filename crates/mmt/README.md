# mmt

Reading and writing the language of [MMT](https://uniformal.github.io/)
v27.0.0 in Rust, with the standard library only and without a JVM: the
surface syntax of `.mmt` files and archives, MMT URIs, OpenMath-style objects,
and objects read and printed by the notations that theories declare.

The crate models the grammar and what reading needs. Objects can only be read
with the notations in scope, so a `Library` elaborates theories (meta-theories,
includes, the declarations before an object) to know them. It does not
type-check, does not check that a symbol exists before it is used, and knows
no theory of its own: LF's notations come from the theories that you load (for
example the MMT/urtheories archive). Static validity is MMT's verdict; run
`mmt.jar` on the output where it matters.

```rust
use mmt::{Library, uri::DPath};

fn main() -> Result<(), mmt::Error> {
    let src = "namespace http://cds.omdoc.org/mmt❚
theory mmt =
  brackets # ( 1 ) prec -1000005❙
❚
namespace http://example.org/logic❚
import m http://cds.omdoc.org/mmt❚
theory Logic =
  include m?mmt❙
  and # 1 ∧ 2 prec 10❙
  true❙
❚";
    let mut lib = Library::new();
    let base: DPath = "http://example.org/logic.mmt".parse()?;
    let read = lib.add_source(src, &base, None);
    assert!(read.is_ok(), "{:?}", read.errors());

    let logic = "http://example.org/logic?Logic".parse()?;
    let scope = lib.object_scope(&logic)?;
    let object = scope.parse("true ∧ (true ∧ true)")?;
    assert_eq!(object.term().to_string(), "(and true (and true true))");
    assert_eq!(scope.print(&object)?, "true ∧ (true ∧ true)");
    Ok(())
}
```

- `Document::parse` reads the structure of a file (theories, constants and
  their components as text) and `Display` writes it back; every error has a
  line and column.
- `Library::add_source`, `load_archives` and `add_theory` elaborate theories;
  `ObjectScope::parse` and `print` read and write objects in the scope of a
  theory; `Library::print_theories` writes theories as a document that reads
  back as the same theories. The printer reads every object back and refuses
  what would read differently.
- Nesting is bounded by `Limits` (default 200 levels, safe on a 2 MiB stack in
  an unoptimized build); deeper input is an error of kind `ErrorKind::Limit`,
  never a stack overflow. The crate spawns no thread; raise the limit and run
  on a larger stack if you need more.

The crate documentation lists the supported subset of the language and what
is rejected as unsupported (views, structures, label arguments, ambiguous
notations, and some lexer extensions).

The tests that compare with MMT itself or read MMT/urtheories need
`.tools/mmt.jar` (MMT v27.0.0), `.tools/bin/java` and `.tools/urtheories`
(commit 8bc91e38df43decdd55b1eda471c4d7b9c75dfdd) in the repository root; they
are ignored by default (`cargo test -p mmt -- --ignored`). No file of MMT or
MMT/urtheories is part of this crate.
