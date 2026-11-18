/-!
# Contracts

A sentence is read as assume-guarantee contracts. A contract is kept by a behaviour when
the behaviour meets the guarantee wherever it meets the assumption, and a set of contracts
is kept when each contract of the set is kept. This is the whole meaning of a
specification: the conjunction of its contracts.
-/

namespace Trion

/-- An assume-guarantee contract over behaviours. -/
structure Contract (Behaviour : Type) where
  assume : Behaviour → Prop
  guarantee : Behaviour → Prop

variable {Behaviour : Type}

/-- A behaviour keeps a contract: where the assumption holds, so does the guarantee. -/
def Contract.kept (contract : Contract Behaviour) (behaviour : Behaviour) : Prop :=
  contract.assume behaviour → contract.guarantee behaviour

/-- A behaviour keeps a set of contracts: it keeps each of them. -/
def kept (contracts : List (Contract Behaviour)) (behaviour : Behaviour) : Prop :=
  ∀ contract ∈ contracts, contract.kept behaviour

/-- Keeping two sets of contracts is keeping their union. -/
theorem kept_append (first second : List (Contract Behaviour)) (behaviour : Behaviour) :
    kept (first ++ second) behaviour ↔ kept first behaviour ∧ kept second behaviour := by
  unfold kept
  constructor
  · intro all
    exact ⟨fun c h => all c (List.mem_append_left _ h), fun c h => all c (List.mem_append_right _ h)⟩
  · intro ⟨left, right⟩ c h
    cases List.mem_append.mp h with
    | inl h => exact left c h
    | inr h => exact right c h

/-- The order in which the contracts of a specification are stated does not matter, and
neither does stating a contract twice: only which contracts are stated. -/
theorem kept_of_same_members (first second : List (Contract Behaviour))
    (same : ∀ contract, contract ∈ first ↔ contract ∈ second) (behaviour : Behaviour) :
    kept first behaviour ↔ kept second behaviour := by
  unfold kept
  constructor
  · intro all c h
    exact all c ((same c).mpr h)
  · intro all c h
    exact all c ((same c).mp h)

end Trion
