/-!
# Expansion

The composite vocabulary as a function. A sentence is described by its shape: how many
subjects `and` joins and whether they are counted, the verb phrases that `and` joins, each
with the number of its objects and whether a measure follows it, and whether a clause about
the whole claim (`only when`, `exactly when`) ends the sentence.

`expand` gives the sentences that a sentence of a shape abbreviates, each named by its
verb phrase, its subject and its object, or the rule that refuses the sentence. The
implementation is tested against this function on every shape within a bound: it gives
the same sentences in the same order and refuses the same sentences by the same rule.
-/

namespace Trion

/-- A verb phrase of a sentence: the number of its objects (one or more, joined so that
each is required or each is denied), and whether a measure follows it. -/
structure Phrase where
  objects : Nat
  measured : Bool
  deriving Repr, DecidableEq

/-- The shape of a sentence. -/
structure Shape where
  subjects : Nat
  counted : Bool
  phrases : List Phrase
  whole : Bool
  deriving Repr, DecidableEq

/-- The rule that refuses a sentence. -/
inductive Refusal where
  /-- The subject is counted, and several sentences would repeat it. -/
  | counted
  /-- A measure follows the last of several verb phrases and not each of them. -/
  | measure
  /-- A clause about the whole claim ends a sentence that abbreviates several. -/
  | whole
  deriving Repr, DecidableEq

/-- One sentence of an expansion: the numbers of its verb phrase, of its subject and of
its object. -/
abbrev Part := Nat × Nat × Nat

/-- The subjects and the objects of one verb phrase, each subject with each object. -/
def combinations (subjects objects : Nat) : List (Nat × Nat) :=
  (List.range subjects).flatMap fun subject => (List.range objects).map fun object => (subject, object)

/-- The sentences of the verb phrases from a number on, in their order: for each verb
phrase, each subject with each object. -/
def parts (subjects : Nat) : Nat → List Phrase → List Part
  | _, [] => []
  | number, phrase :: rest =>
    (combinations subjects phrase.objects).map (fun (subject, object) => (number, subject, object))
      ++ parts subjects (number + 1) rest

/-- The number of sentences that a shape abbreviates. -/
def count (shape : Shape) : Nat :=
  shape.subjects * (shape.phrases.map Phrase.objects).sum

/-- A measure follows the last verb phrase of several, and some earlier one has none. -/
def measuredLast (phrases : List Phrase) : Bool :=
  match phrases.getLast? with
  | some last => phrases.length > 1 && last.measured && phrases.dropLast.any fun phrase => !phrase.measured
  | none => false

/-- Several sentences would repeat the subject: several verb phrases, or several objects
of one verb phrase. -/
def repeated (shape : Shape) : Bool :=
  shape.phrases.length > 1 || shape.phrases.any fun phrase => phrase.objects > 1

/-- The sentences that a sentence of a shape abbreviates, or the rule that refuses it. -/
def expand (shape : Shape) : Except Refusal (List Part) :=
  if shape.counted && repeated shape then .error .counted
  else if measuredLast shape.phrases then .error .measure
  else if shape.whole && count shape > 1 then .error .whole
  else .ok (parts shape.subjects 0 shape.phrases)

/-- Each subject stands with each object, and nothing else does. -/
theorem mem_combinations (subjects objects subject object : Nat) :
    (subject, object) ∈ combinations subjects objects ↔ subject < subjects ∧ object < objects := by
  simp [combinations, List.mem_flatMap, List.mem_map, List.mem_range]

/-- A sentence with one subject, one verb phrase and one object is simple: it abbreviates
itself, whatever stands around it. -/
theorem simple_expands_to_itself (counted whole measured : Bool) :
    expand ⟨1, counted, [⟨1, measured⟩], whole⟩ = .ok [(0, 0, 0)] := by
  cases counted <;> cases whole <;> cases measured <;> rfl

/-- A counted subject is never repeated: a sentence that would repeat it is refused. -/
theorem counted_is_not_repeated (shape : Shape) (counted : shape.counted = true)
    (several : repeated shape = true) : expand shape = .error .counted := by
  simp [expand, counted, several]

/-- A sentence that is expanded abbreviates exactly the sentences of its parts: nothing
is refused in part, and nothing is added. -/
theorem expanded_is_every_part (shape : Shape) (result : List Part)
    (expanded : expand shape = .ok result) : result = parts shape.subjects 0 shape.phrases := by
  unfold expand at expanded
  split at expanded
  · cases expanded
  · split at expanded
    · cases expanded
    · split at expanded
      · cases expanded
      · exact (Except.ok.inj expanded).symm

end Trion
