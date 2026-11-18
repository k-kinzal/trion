import Trion.Contract

/-!
# Merging

Contract theory has two ways to combine contracts. Conjunction is the plain set of
contracts: each contract is owed its guarantee wherever its own assumption holds. Merging
(Incer, *The Algebra of Contracts*, Def. 5.1.1) joins the assumptions as well: the merged
contract is owed its guarantee only where every assumption holds.

Composite vocabulary is an abbreviation for a set of simple sentences, so it can only be
conjunction. This file shows that merging is still reachable as an abbreviation: giving
each contract the assumptions that it shares, and then taking the plain set, is merging.
A shared condition block and a sentence that only assumes are therefore read by
distributing their assumption over the sentences in their scope, and never as a contract
beside them: as a member of the set an assumption alone changes nothing.

`Trion.kept` is the implementation side of a set of contracts read as their conjunction:
a behaviour keeps each contract. `asked` below is the environment side of the same
conjunction: some assumption holds. Together they are the saturated contract
(∨ Aᵢ, ∧ (Aᵢ → Gᵢ)) of the set.
-/

namespace Trion

variable {Behaviour : Type}

/-- The environment side of a set of contracts read as their conjunction: some assumption
holds. -/
def asked (contracts : List (Contract Behaviour)) (behaviour : Behaviour) : Prop :=
  ∃ contract ∈ contracts, contract.assume behaviour

/-- A contract under one more assumption that it shares with other contracts. -/
def Contract.under (shared : Behaviour → Prop) (contract : Contract Behaviour) : Contract Behaviour :=
  ⟨fun b => shared b ∧ contract.assume b, contract.guarantee⟩

/-- Merging of the assumption-only contract `(shared, ⊤)` with the conjunction of a set of
contracts has the guarantee `kept ∨ ¬(shared ∧ asked)`. Giving the shared assumption to
each contract of the set and taking the plain set of the results has the same guarantee. -/
theorem shared_assumption_guarantee (shared : Behaviour → Prop) (contracts : List (Contract Behaviour))
    (behaviour : Behaviour) :
    kept (contracts.map (Contract.under shared)) behaviour ↔
      (kept contracts behaviour ∨ ¬(shared behaviour ∧ asked contracts behaviour)) := by
  unfold kept asked Contract.kept
  constructor
  · intro each
    cases Classical.em (shared behaviour) with
    | inl holds =>
      exact Or.inl fun contract member assumed =>
        each (contract.under shared) (List.mem_map.mpr ⟨contract, member, rfl⟩) ⟨holds, assumed⟩
    | inr fails => exact Or.inr fun both => fails both.1
  · intro either widened member
    obtain ⟨contract, inside, same⟩ := List.mem_map.mp member
    subst same
    intro ⟨holds, assumed⟩
    cases either with
    | inl all => exact all contract inside assumed
    | inr none => exact (none ⟨holds, contract, inside, assumed⟩).elim

/-- ... and the same assumption: the shared assumption together with some assumption of
the set. -/
theorem shared_assumption_assumption (shared : Behaviour → Prop) (contracts : List (Contract Behaviour))
    (behaviour : Behaviour) :
    asked (contracts.map (Contract.under shared)) behaviour ↔
      (shared behaviour ∧ asked contracts behaviour) := by
  unfold asked
  constructor
  · intro ⟨widened, member, assumed⟩
    obtain ⟨contract, inside, same⟩ := List.mem_map.mp member
    subst same
    exact ⟨assumed.1, contract, inside, assumed.2⟩
  · intro ⟨holds, contract, inside, assumed⟩
    exact ⟨contract.under shared, List.mem_map.mpr ⟨contract, inside, rfl⟩, holds, assumed⟩

/-- Merging of two contracts in general: each contract under the assumption of the other,
as a plain set, has the guarantee of the merged contract `(G₁ ∧ G₂) ∨ ¬(A₁ ∧ A₂)` (with
`Gᵢ` saturated) and its assumption `A₁ ∧ A₂`. -/
theorem merging_is_sharing (first second : Contract Behaviour) (behaviour : Behaviour) :
    kept [second.under first.assume, first.under second.assume] behaviour ↔
      ((first.kept behaviour ∧ second.kept behaviour) ∨
        ¬(first.assume behaviour ∧ second.assume behaviour)) := by
  unfold kept Contract.kept Contract.under
  constructor
  · intro each
    cases Classical.em (first.assume behaviour ∧ second.assume behaviour) with
    | inl both =>
      refine Or.inl ⟨fun _ => ?_, fun _ => ?_⟩
      · exact each ⟨fun b => second.assume b ∧ first.assume b, first.guarantee⟩
          (List.Mem.tail _ (List.Mem.head _)) (And.intro both.2 both.1)
      · exact each ⟨fun b => first.assume b ∧ second.assume b, second.guarantee⟩
          (List.Mem.head _) (And.intro both.1 both.2)
    | inr fails => exact Or.inr fails
  · intro either contract member
    cases member with
    | head =>
      intro ⟨one, other⟩
      cases either with
      | inl kept => exact kept.2 other
      | inr fails => exact (fails ⟨one, other⟩).elim
    | tail _ member =>
      cases member with
      | head =>
        intro ⟨other, one⟩
        cases either with
        | inl kept => exact kept.1 one
        | inr fails => exact (fails ⟨one, other⟩).elim
      | tail _ member => cases member

/-- The plain set of contracts is not their merging: a contract whose own assumption holds
is owed its guarantee, whether or not another assumption holds. So a sentence that only
assumes cannot be read as a contract of its own beside the others: as a member of the set
it changes nothing. -/
theorem assumption_alone_changes_nothing (shared : Behaviour → Prop) (contracts : List (Contract Behaviour))
    (behaviour : Behaviour) :
    kept (⟨shared, fun _ => True⟩ :: contracts) behaviour ↔ kept contracts behaviour := by
  unfold kept
  constructor
  · intro all contract member
    exact all contract (List.Mem.tail _ member)
  · intro all contract member
    cases member with
    | head => exact fun _ => trivial
    | tail _ member => exact all contract member

end Trion
