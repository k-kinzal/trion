import Trion.Contract

/-!
# Distribution

Composite vocabulary abbreviates several sentences in one. A sentence may be replaced by
the sentences that it abbreviates only where both say the same: where the claim of the
sentence distributes over its parts. This file states, for each rule of the composite
vocabulary, the fact that the rule rests on.

A rule that expands a sentence rests on an equivalence: the contract of the whole is kept
exactly when the contract of each part is kept. A rule that refuses a sentence, or keeps
it as one requirement, rests on a counterexample: a case in which the whole and the parts
differ. So no rule is a convention: each follows from what contracts mean.
-/

namespace Trion

variable {Behaviour : Type}

/-! ## What distributes -/

/-- Parts joined by `and` under the conditions of one sentence: the contract of the
conjunction is kept exactly when the contract of each part is kept. The conditions are
the frames of the sentence (`Where`, `While`, `When`, `If`) and its exception (`unless`):
all of them are part of the assumption, and each part keeps all of them.

This is the rule for `and` between verb phrases, between the objects of a verb, between
the phrases of a role, and between whole clauses. -/
theorem and_distributes (assume first second : Behaviour → Prop) (behaviour : Behaviour) :
    (Contract.mk assume fun b => first b ∧ second b).kept behaviour ↔
      kept [⟨assume, first⟩, ⟨assume, second⟩] behaviour := by
  unfold kept Contract.kept
  constructor
  · intro whole contract member
    cases member with
    | head => exact fun holds => (whole holds).1
    | tail _ member =>
      cases member with
      | head => exact fun holds => (whole holds).2
      | tail _ member => cases member
  · intro parts holds
    exact ⟨parts ⟨assume, first⟩ (List.Mem.head _) holds,
      parts ⟨assume, second⟩ (List.Mem.tail _ (List.Mem.head _)) holds⟩

/-- A subject that names every thing of a kind (`the`, `each`, `every`, `all`, `any`):
what holds of each thing for both parts holds of each thing for either part, and the
reverse. So a sentence with such a subject may repeat the subject in each part. -/
theorem every_distributes {Thing : Type} (first second : Thing → Prop) :
    (∀ thing, first thing ∧ second thing) ↔ (∀ thing, first thing) ∧ (∀ thing, second thing) :=
  ⟨fun both => ⟨fun thing => (both thing).1, fun thing => (both thing).2⟩,
    fun ⟨left, right⟩ thing => ⟨left thing, right thing⟩⟩

/-- `or` under `not`: denying that one of two things is done denies each of them. So
`shall not A or B` abbreviates `shall not A` and `shall not B`. -/
theorem denied_or_distributes (first second : Prop) : ¬(first ∨ second) ↔ ¬first ∧ ¬second :=
  ⟨fun neither => ⟨fun holds => neither (Or.inl holds), fun holds => neither (Or.inr holds)⟩,
    fun ⟨left, right⟩ either => either.elim left right⟩

/-! ## What does not distribute -/

/-- `or` without `not` is a choice, and a choice is one requirement: doing one of two
things is not doing both. So `shall A or B` is one sentence with one contract. -/
theorem choice_is_one_requirement : ∃ first second : Prop, ¬((first ∨ second) ↔ (first ∧ second)) :=
  ⟨True, False, fun same => (same.mp (Or.inl trivial)).2⟩

/-- `and` under `not`: denying two things together is not denying each of them. The text
`shall not A and B` does not say which is meant, so the sentence is not read as either. -/
theorem denied_and_does_not_distribute : ∃ first second : Prop, ¬(¬(first ∧ second) ↔ (¬first ∧ ¬second)) :=
  ⟨True, False, fun same => (same.mp fun both => both.2).1 trivial⟩

/-- A coordination inside a condition is one assumption: a claim under two conditions
together is not the claim under each of them. So `When A and B, …` is one sentence. -/
theorem condition_is_one_assumption :
    ∃ first second claim : Prop, ¬(((first ∧ second) → claim) ↔ ((first → claim) ∧ (second → claim))) :=
  ⟨True, False, False, fun same => (same.mp fun both => both.2).1 trivial⟩

/-- A counted subject (`some`, `at least n`, `exactly n`): that some thing does both is
not that some thing does the one and some thing does the other. The two sentences would
not speak of the same thing, so a sentence with a counted subject is not distributed. -/
theorem some_does_not_distribute :
    ∃ first second : Bool → Prop,
      ¬((∃ thing, first thing ∧ second thing) ↔ ((∃ thing, first thing) ∧ (∃ thing, second thing))) := by
  refine ⟨(· = true), (· = false), ?_⟩
  intro same
  obtain ⟨thing, one, other⟩ := same.mpr ⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩
  rw [one] at other
  exact Bool.noConfusion other

/-- A subject with `no`: that no thing does both is not that no thing does the one and no
thing does the other. So a sentence with such a subject is not distributed. -/
theorem no_does_not_distribute :
    ∃ first second : Bool → Prop,
      ¬((¬∃ thing, first thing ∧ second thing) ↔ ((¬∃ thing, first thing) ∧ (¬∃ thing, second thing))) := by
  refine ⟨(· = true), (· = false), ?_⟩
  intro same
  have none : ¬∃ thing : Bool, thing = true ∧ thing = false := by
    intro ⟨thing, one, other⟩
    rw [one] at other
    exact Bool.noConfusion other
  exact (same.mp none).1 ⟨true, rfl⟩

/-- `only when`: that the parts together require a condition is not that each part
requires it. So a sentence whose claim abbreviates several requirements and that ends
with `only when` is not distributed. -/
theorem only_when_does_not_distribute :
    ∃ first second condition : Prop,
      ¬(((first ∧ second) → condition) ↔ ((first → condition) ∧ (second → condition))) :=
  ⟨True, False, False, fun same => (same.mp fun both => both.2).1 trivial⟩

/-- `exactly when`: that the parts together stand with a condition is not that each part
stands with it. So such a sentence is not distributed. -/
theorem exactly_when_does_not_distribute :
    ∃ first second condition : Prop,
      ¬(((first ∧ second) ↔ condition) ↔ ((first ↔ condition) ∧ (second ↔ condition))) :=
  ⟨True, False, False, fun same =>
    (same.mp ⟨fun both => both.2, fun condition => condition.elim⟩).1.mp trivial⟩

/-- A measure after the last of several verb phrases: bounding the last phrase is not
bounding each phrase. The text does not say which is meant, so the sentence is not read
as either. -/
theorem measure_readings_differ :
    ∃ first second firstBounded secondBounded : Prop,
      ¬((first ∧ (second ∧ secondBounded)) ↔ ((first ∧ firstBounded) ∧ (second ∧ secondBounded))) :=
  ⟨True, True, False, True, fun same => (same.mp ⟨trivial, trivial, trivial⟩).1.2⟩

end Trion
