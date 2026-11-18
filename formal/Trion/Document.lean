import Trion.Contract
import Trion.Merging

/-!
# A correct specification document

A document is read as the conjunction of the contracts of its simple sentences, after the
composite vocabulary is expanded and each assumption sentence is distributed over the
sentences in its scope (`Trion.Merging`). This file states what makes such a document
correct, after Benveniste et al., *Contracts for Systems Design* (INRIA RR-8147):

* consistency: an implementation exists;
* compatibility: an environment exists;
* correctness against a reference: the document refines the reference;
* completeness against a reference: the document refines the reference, or no
  consistent and compatible document refines both.

Consistency is read for a system that accepts every input of its environment: for each
input some behaviour with that input keeps every contract. Without this, a document that
says "when the door opens, the bell shall ring" and "when the door opens, the bell shall
not ring" would be consistent, kept by a system that never lets the door open.

This file states the propositions over whole behaviours. It does not state that an
implementation answers each input from what it has seen so far; the reactive reading adds
that causality.
-/

namespace Trion

variable {Behaviour Input : Type}

/-! ## The four properties -/

/-- Some behaviour keeps every contract. This is less than consistency. -/
def satisfiable (contracts : List (Contract Behaviour)) : Prop :=
  ∃ behaviour, kept contracts behaviour

/-- Consistency: for each input of the environment, some behaviour with that input keeps
every contract. An implementation that accepts every input exists. -/
def consistent (input : Behaviour → Input) (contracts : List (Contract Behaviour)) : Prop :=
  ∀ given, ∃ behaviour, input behaviour = given ∧ kept contracts behaviour

/-- Compatibility: some behaviour of the environment meets an assumption of the document. -/
def compatible (contracts : List (Contract Behaviour)) : Prop :=
  ∃ behaviour, asked contracts behaviour

/-- Refinement: the finer document accepts every environment of the coarser one, and
every behaviour that keeps the finer document keeps the coarser one. -/
def refines (fine coarse : List (Contract Behaviour)) : Prop :=
  (∀ behaviour, asked coarse behaviour → asked fine behaviour) ∧
    (∀ behaviour, kept fine behaviour → kept coarse behaviour)

/-- Incompleteness against a reference (RR-8147, §completeness): the document does not
refine the reference, but together with the reference it is consistent and compatible,
so more sentences would make it refine the reference. -/
def incomplete (input : Behaviour → Input) (reference document : List (Contract Behaviour)) : Prop :=
  ¬refines document reference ∧ consistent input (document ++ reference) ∧
    compatible (document ++ reference)

/-! ## Facts about them -/

/-- Consistency gives satisfiability wherever the environment has an input at all. -/
theorem satisfiable_of_consistent [Nonempty Input] (input : Behaviour → Input)
    (contracts : List (Contract Behaviour)) (holds : consistent input contracts) :
    satisfiable contracts := by
  obtain ⟨behaviour, _, keeps⟩ := holds (Classical.choice (inferInstance : Nonempty Input))
  exact ⟨behaviour, keeps⟩

theorem refines_refl (contracts : List (Contract Behaviour)) : refines contracts contracts :=
  ⟨fun _ asks => asks, fun _ keeps => keeps⟩

theorem refines_trans (fine middle coarse : List (Contract Behaviour))
    (lower : refines fine middle) (upper : refines middle coarse) : refines fine coarse :=
  ⟨fun b asks => lower.1 b (upper.1 b asks), fun b keeps => upper.2 b (lower.2 b keeps)⟩

/-- A document together with more sentences refines the document. -/
theorem append_refines_left (first second : List (Contract Behaviour)) :
    refines (first ++ second) first := by
  refine ⟨fun b ⟨contract, member, assumed⟩ => ⟨contract, List.mem_append_left _ member, assumed⟩, ?_⟩
  intro b keeps
  exact ((kept_append first second b).mp keeps).1

theorem append_refines_right (first second : List (Contract Behaviour)) :
    refines (first ++ second) second := by
  refine ⟨fun b ⟨contract, member, assumed⟩ => ⟨contract, List.mem_append_right _ member, assumed⟩, ?_⟩
  intro b keeps
  exact ((kept_append first second b).mp keeps).2

/-- An incomplete document has a completion: the document together with the reference is
consistent and compatible and refines both. -/
theorem incomplete_has_completion (input : Behaviour → Input)
    (reference document : List (Contract Behaviour)) (gap : incomplete input reference document) :
    ∃ completed, refines completed document ∧ refines completed reference ∧
      consistent input completed ∧ compatible completed :=
  ⟨document ++ reference, append_refines_left _ _, append_refines_right _ _, gap.2.1, gap.2.2⟩

/-- Sentences only remove behaviours: a behaviour that keeps a document with more sentences
keeps the document without them. So no sentence can lift or soften another; a default
that a later sentence overrides is not a meaning that a set of contracts can have. -/
theorem more_sentences_fewer_behaviours (first second : List (Contract Behaviour))
    (behaviour : Behaviour) (keeps : kept (first ++ second) behaviour) : kept first behaviour :=
  ((kept_append first second behaviour).mp keeps).1

/-- ... and consistency is lost, never gained, by adding sentences. -/
theorem consistent_of_append (input : Behaviour → Input) (first second : List (Contract Behaviour))
    (holds : consistent input (first ++ second)) : consistent input first := by
  intro given
  obtain ⟨behaviour, same, keeps⟩ := holds given
  exact ⟨behaviour, same, more_sentences_fewer_behaviours first second behaviour keeps⟩

/-! ## Opposite responses to one trigger

"When the message is stored, the API shall notify the author" and "When the message is
stored, the API shall not notify the author" are two contracts with one assumption and
opposite guarantees. They are kept exactly where the trigger does not happen. Whether the
document is consistent depends on who decides the trigger:

* if no sentence requires the trigger and the system may avoid it for every input, the
  two sentences are consistent: the system that never stores keeps them, vacuously;
* if a sentence requires the trigger ("the API shall store the message"), the system that
  never stores is excluded, and the document is inconsistent;
* if the environment decides the trigger ("when the door opens"), a system that accepts
  every input cannot avoid it, and the document is inconsistent, although it is
  satisfiable. -/

/-- Two sentences that answer one trigger with opposite responses. -/
def opposite (trigger response : Behaviour → Prop) : List (Contract Behaviour) :=
  [⟨trigger, response⟩, ⟨trigger, fun b => ¬response b⟩]

/-- The obligation of a condition, with no assumption. -/
def obliged (condition : Behaviour → Prop) : Contract Behaviour :=
  ⟨fun _ => True, condition⟩

theorem opposite_kept (trigger response : Behaviour → Prop) (behaviour : Behaviour) :
    kept (opposite trigger response) behaviour ↔ ¬trigger behaviour := by
  unfold kept opposite Contract.kept
  constructor
  · intro each happens
    exact each ⟨trigger, fun b => ¬response b⟩ (List.Mem.tail _ (List.Mem.head _)) happens
      (each ⟨trigger, response⟩ (List.Mem.head _) happens)
  · intro avoided contract member happens
    exact (avoided (by cases member with
      | head => exact happens
      | tail _ member => cases member with
        | head => exact happens
        | tail _ member => cases member)).elim

/-- Where the system may avoid the trigger for every input, and nothing requires it, the
two sentences are consistent: vacuously. -/
theorem opposite_consistent_when_avoidable (input : Behaviour → Input)
    (trigger response : Behaviour → Prop)
    (avoidable : ∀ given, ∃ behaviour, input behaviour = given ∧ ¬trigger behaviour) :
    consistent input (opposite trigger response) := by
  intro given
  obtain ⟨behaviour, same, avoided⟩ := avoidable given
  exact ⟨behaviour, same, (opposite_kept trigger response behaviour).mpr avoided⟩

/-- A sentence that requires the trigger excludes the system that avoids it: with it, the
two sentences are inconsistent. -/
theorem opposite_inconsistent_when_required [Nonempty Input] (input : Behaviour → Input)
    (trigger response : Behaviour → Prop) :
    ¬consistent input (obliged trigger :: opposite trigger response) := by
  intro holds
  obtain ⟨behaviour, _, keeps⟩ := holds (Classical.choice (inferInstance : Nonempty Input))
  have happens : trigger behaviour := keeps (obliged trigger) (List.Mem.head _) trivial
  have avoided : ¬trigger behaviour :=
    (opposite_kept trigger response behaviour).mp fun contract member => keeps contract (List.Mem.tail _ member)
  exact avoided happens

/-- Where the environment can force the trigger, a system that accepts every input cannot
avoid it: the two sentences are inconsistent. -/
theorem opposite_inconsistent_when_forced (input : Behaviour → Input)
    (trigger response : Behaviour → Prop)
    (forced : ∃ given, ∀ behaviour, input behaviour = given → trigger behaviour) :
    ¬consistent input (opposite trigger response) := by
  intro holds
  obtain ⟨given, forces⟩ := forced
  obtain ⟨behaviour, same, keeps⟩ := holds given
  exact (opposite_kept trigger response behaviour).mp keeps (forces behaviour same)

/-- ... although they are satisfiable wherever some behaviour lacks the trigger: so
satisfiability alone does not make a document consistent. -/
theorem opposite_satisfiable_when_absent (trigger response : Behaviour → Prop)
    (absent : ∃ behaviour, ¬trigger behaviour) : satisfiable (opposite trigger response) := by
  obtain ⟨behaviour, avoided⟩ := absent
  exact ⟨behaviour, (opposite_kept trigger response behaviour).mpr avoided⟩

end Trion
