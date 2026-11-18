import Lake

open Lake DSL

package «trion-formal» where
  leanOptions := #[⟨`warningAsError, true⟩]

/-- The two principles of the trion language as mathematics: what a contract says, when a
sentence abbreviates several sentences, and why each rule of the composite vocabulary
distributes or refuses. -/
@[default_target]
lean_lib Trion

/-- Answers, for each shape of a sentence on its standard input, what the expansion gives:
the implementation is tested against it. -/
@[default_target]
lean_exe «trion-oracle» where
  root := `Oracle
