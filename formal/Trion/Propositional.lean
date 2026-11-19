import Init

set_option warningAsError true

namespace Trion.Propositional

abbrev Valuation (n : Nat) := Fin n → Bool

inductive Expr (n : Nat) where
  | top | bot | atom (index : Fin n)
  | neg (x : Expr n)
  | both (x y : Expr n)
  | either (x y : Expr n)

/-- A separate recursive interpretation into propositions. Using Fin n enforces
    the reference condition for every atom in a finite, well-formed tree. -/
def Truth (v : Valuation n) : Expr n → Prop
  | .top => True
  | .bot => False
  | .atom i => v i = true
  | .neg x => ¬ Truth v x
  | .both x y => Truth v x ∧ Truth v y
  | .either x y => Truth v x ∨ Truth v y

def eval (v : Valuation n) : Expr n → Bool
  | .top => true
  | .bot => false
  | .atom i => v i
  | .neg x => !eval v x
  | .both x y => eval v x && eval v y
  | .either x y => eval v x || eval v y

/-- M01. Lean checks structural termination of both definitions. -/
theorem eval_correct (v : Valuation n) (e : Expr n) :
    eval v e = true ↔ Truth v e := by
  induction e with
  | neg x ih => simp [eval, Truth, ← ih]
  | both x y ihx ihy => simp [eval, Truth, ihx, ihy]
  | either x y ihx ihy => simp [eval, Truth, ihx, ihy]
  | top | bot | atom => simp [eval, Truth]

inductive Surface (n : Nat) where
  | top | bot | atom (index : Fin n)
  | neg (x : Surface n)
  | both (x y : Surface n)
  | either (x y : Surface n)
  | implies (x y : Surface n)

def surfaceTruth (v : Valuation n) : Surface n → Prop
  | .top => True
  | .bot => False
  | .atom i => v i = true
  | .neg x => ¬ surfaceTruth v x
  | .both x y => surfaceTruth v x ∧ surfaceTruth v y
  | .either x y => surfaceTruth v x ∨ surfaceTruth v y
  | .implies x y => surfaceTruth v x → surfaceTruth v y

def expand : Surface n → Expr n
  | .top => .top
  | .bot => .bot
  | .atom i => .atom i
  | .neg x => .neg (expand x)
  | .both x y => .both (expand x) (expand y)
  | .either x y => .either (expand x) (expand y)
  | .implies x y => .either (.neg (expand x)) (expand y)

/-- M02. The implication clause of surfaceTruth is independent of expand. -/
theorem expand_correct (v : Valuation n) (e : Surface n) :
    Truth v (expand e) ↔ surfaceTruth v e := by
  induction e with
  | neg x ih => simp [expand, Truth, surfaceTruth, ih]
  | both x y ihx ihy | either x y ihx ihy =>
    simp [expand, Truth, surfaceTruth, ihx, ihy]
  | implies x y ihx ihy =>
    simp only [expand, surfaceTruth, ← ihx, ← ihy, ← eval_correct, eval]
    cases eval v (expand x) <;> cases eval v (expand y) <;> simp
  | top | bot | atom => simp [expand, Truth, surfaceTruth]

inductive Question (n : Nat) where
  | satisfiable
  | entails (goal : Expr n)

def Premises (v : Valuation n) (ps : List (Expr n)) : Prop :=
  ∀ p ∈ ps, Truth v p

def Candidate (v : Valuation n) (ps : List (Expr n)) : Question n → Prop
  | .satisfiable => Premises v ps
  | .entails goal => Premises v ps ∧ ¬ Truth v goal

def condition (ps : List (Expr n)) : Question n → List (Expr n)
  | .satisfiable => ps
  | .entails goal => ps ++ [.neg goal]

theorem query_condition_exact (v : Valuation n) (ps : List (Expr n)) (q : Question n) :
    Premises v (condition ps q) ↔ Candidate v ps q := by
  cases q with
  | satisfiable => rfl
  | entails goal =>
    constructor
    · intro h
      exact ⟨fun p hp => h p (List.mem_append_left _ hp),
        h (.neg goal) (List.mem_append_right _ (by simp))⟩
    · intro ⟨hps, hgoal⟩ p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hps p hp
      · have he : p = .neg goal := List.mem_singleton.mp hp
        subst p
        exact hgoal

inductive Target (n : Nat) where
  | constant (value : Bool)
  | literal (slot : Fin n) (positive : Bool)
  | all (x y : Target n)
  | any (x y : Target n)

def targetEval (v : Valuation n) : Target n → Bool
  | .constant b => b
  | .literal i positive => v i == positive
  | .all x y => targetEval v x && targetEval v y
  | .any x y => targetEval v x || targetEval v y

def translate (positive : Bool) : Expr n → Target n
  | .top => .constant positive
  | .bot => .constant (!positive)
  | .atom i => .literal i positive
  | .neg x => translate (!positive) x
  | .both x y =>
    if positive then .all (translate true x) (translate true y)
    else .any (translate false x) (translate false y)
  | .either x y =>
    if positive then .any (translate true x) (translate true y)
    else .all (translate false x) (translate false y)

/-- M03, including the identity correspondence of target slots and atoms. -/
theorem translate_exact (v : Valuation n) (e : Expr n) (positive : Bool) :
    targetEval v (translate positive e) = (eval v e == positive) := by
  induction e generalizing positive with
  | neg x ih => cases positive <;> cases he : eval v x <;> simp [translate, eval, ih, he]
  | both x y ihx ihy | either x y ihx ihy =>
    cases positive <;> cases hx : eval v x <;> cases hy : eval v y <;>
      simp [translate, eval, targetEval, ihx, ihy, hx, hy]
  | top | bot | atom => cases positive <;> simp [translate, targetEval, eval]

theorem target_query_exact (v : Valuation n) (ps : List (Expr n)) (q : Question n) :
    ((condition ps q).map (translate true)).all (targetEval v) = true ↔
      Candidate v ps q := by
  rw [← query_condition_exact, List.all_eq_true]
  simp [Premises, translate_exact, eval_correct]

/-- The propositional fragment of the MMT form. A nullary relation is
    identified by its slot in the table of distinct declared names. -/
inductive MmtFormula (n : Nat) where
  | truth | relation (slot : Fin n)
  | neg (x : MmtFormula n)
  | both (x y : MmtFormula n)
  | either (x y : MmtFormula n)

def mmtTruth (v : Valuation n) : MmtFormula n → Prop
  | .truth => True
  | .relation i => v i = true
  | .neg x => ¬ mmtTruth v x
  | .both x y => mmtTruth v x ∧ mmtTruth v y
  | .either x y => mmtTruth v x ∨ mmtTruth v y

def toMmt : Expr n → MmtFormula n
  | .top => .truth
  | .bot => .neg .truth
  | .atom i => .relation i
  | .neg x => .neg (toMmt x)
  | .both x y => .both (toMmt x) (toMmt y)
  | .either x y => .either (toMmt x) (toMmt y)

theorem mmt_formula_exact (v : Valuation n) (e : Expr n) :
    mmtTruth v (toMmt e) ↔ Truth v e := by
  induction e with
  | top | bot | atom => simp [mmtTruth, toMmt, Truth]
  | neg x ih => simp [mmtTruth, toMmt, Truth, ih]
  | both x y ihx ihy | either x y ihx ihy =>
    simp [mmtTruth, toMmt, Truth, ihx, ihy]

inductive MmtQuestion (n : Nat) where
  | satisfiable (formulas : List (MmtFormula n))
  | unsatisfiable (formulas : List (MmtFormula n))
  | both (left right : MmtQuestion n)

def mmtHolds : MmtQuestion n → Prop
  | .satisfiable fs => ∃ v, ∀ f ∈ fs, mmtTruth v f
  | .unsatisfiable fs => ¬ ∃ v, ∀ f ∈ fs, mmtTruth v f
  | .both x y => mmtHolds x ∧ mmtHolds y

def mmtQuestion (ps : List (Expr n)) : Question n → MmtQuestion n
  | .satisfiable => .satisfiable (ps.map toMmt)
  | .entails goal => .both (.satisfiable (ps.map toMmt))
      (.unsatisfiable (ps.map toMmt ++ [.neg (toMmt goal)]))

def CheckHolds (ps : List (Expr n)) : Question n → Prop
  | .satisfiable => ∃ v, Premises v ps
  | .entails goal => (∃ v, Premises v ps) ∧ ¬ ∃ v, Candidate v ps (.entails goal)

/-- The encoded obligation asks exactly for satisfiability or nonvacuous
    entailment. This concerns the formulas and the questions in the form. -/
theorem mmt_question_exact (ps : List (Expr n)) (q : Question n) :
    mmtHolds (mmtQuestion ps q) ↔ CheckHolds ps q := by
  have mapped (xs : List (Expr n)) (v : Valuation n) :
      (∀ f ∈ xs.map toMmt, mmtTruth v f) ↔ Premises v xs := by
    simp [List.mem_map, Premises, mmt_formula_exact]
  cases q with
  | satisfiable => simp only [mmtHolds, mmtQuestion, CheckHolds, mapped]
  | entails goal =>
    rw [mmtQuestion, mmtHolds, CheckHolds, mmtHolds, mmtHolds]
    have counterexamples : ps.map toMmt ++ [.neg (toMmt goal)] =
        (condition ps (.entails goal)).map toMmt := by
      simp [condition, toMmt]
    rw [counterexamples]
    simp only [mapped, query_condition_exact]

def prepend (bit : Bool) (v : Valuation n) : Valuation (n + 1) :=
  Fin.cases bit v

/-- The same false/true prefix recursion as the reference evaluator's traversal. -/
def valuations : (n : Nat) → List (Valuation n)
  | 0 => [Fin.elim0]
  | n + 1 => (valuations n).map (prepend false) ++ (valuations n).map (prepend true)

theorem empty_valuation : (valuations 0).length = 1 := rfl

theorem valuation_count (n : Nat) : (valuations n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [valuations, ih, Nat.pow_succ, Nat.mul_two]

/-- M04. Every assignment, including the unique empty assignment, is generated. -/
theorem valuations_complete (v : Valuation n) : v ∈ valuations n := by
  induction n with
  | zero =>
    have h : v = Fin.elim0 := funext fun i => Fin.elim0 i
    simp [valuations, h]
  | succ n ih =>
    let tail : Valuation n := fun i => v i.succ
    have ht : tail ∈ valuations n := ih tail
    have hv : prepend (v 0) tail = v := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [prepend]
      · simp [prepend, tail]
    cases hb : v 0 with
    | false =>
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨tail, ht, hb ▸ hv⟩
    | true =>
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨tail, ht, hb ▸ hv⟩

def checkPremises (v : Valuation n) (ps : List (Expr n)) : Bool :=
  ps.all (eval v)

theorem checkPremises_correct (v : Valuation n) (ps : List (Expr n)) :
    checkPremises v ps = true ↔ Premises v ps := by
  simp [checkPremises, Premises, List.all_eq_true, eval_correct]

def checkWitness (v : Valuation n) (ps : List (Expr n)) : Question n → Bool
  | .satisfiable => checkPremises v ps
  | .entails goal => checkPremises v ps && !eval v goal

theorem witness_correct (v : Valuation n) (ps : List (Expr n)) (q : Question n) :
    checkWitness v ps q = true ↔ Candidate v ps q := by
  cases q <;> simp [checkWitness, Candidate, checkPremises_correct, ← eval_correct]

inductive Scan where
  | found | excluded | incomplete

def scan (budget : Nat) (ps : List (Expr n)) (q : Question n) : Scan :=
  if 2 ^ n > budget then .incomplete
  else if (valuations n).any (fun v => checkWitness v ps q) then .found
  else .excluded

theorem cut_off (ps : List (Expr n)) (q : Question n)
    (budget : Nat) (short : budget < 2 ^ n) :
    scan budget ps q = .incomplete := by
  simp [scan, short]

theorem exclusion_correct (ps : List (Expr n)) (q : Question n)
    (budget : Nat) (h : scan budget ps q = .excluded) :
    2 ^ n ≤ budget ∧ (∀ v, ¬ Candidate v ps q) := by
  unfold scan at h
  split at h
  · contradiction
  rename_i enough
  refine ⟨Nat.le_of_not_gt enough, fun v hc => ?_⟩
  have existsWitness : (valuations n).any (fun u => checkWitness u ps q) = true :=
    List.any_eq_true.mpr ⟨v, valuations_complete v, (witness_correct v ps q).mpr hc⟩
  simp [existsWitness] at h

theorem unsat_sound (ps : List (Expr n)) (budget : Nat)
    (h : scan budget ps .satisfiable = .excluded) : ¬ ∃ v, Premises v ps := by
  intro ⟨v, hv⟩
  exact (exclusion_correct ps .satisfiable budget h).2 v hv

theorem entails_sound (ps : List (Expr n)) (goal : Expr n) (budget : Nat)
    (h : scan budget ps (.entails goal) = .excluded) :
    ∀ v, Premises v ps → Truth v goal := by
  intro v hp
  cases he : eval v goal
  · exact False.elim ((exclusion_correct ps (.entails goal) budget h).2 v
      ⟨hp, by simp [← eval_correct, he]⟩)
  · exact (eval_correct v goal).mp he

/-- info: 'Trion.Propositional.eval_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms eval_correct
/-- info: 'Trion.Propositional.expand_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms expand_correct
/-- info: 'Trion.Propositional.query_condition_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms query_condition_exact
/-- info: 'Trion.Propositional.translate_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms translate_exact
/-- info: 'Trion.Propositional.target_query_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms target_query_exact
/-- info: 'Trion.Propositional.mmt_formula_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mmt_formula_exact
/-- info: 'Trion.Propositional.mmt_question_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mmt_question_exact
/-- info: 'Trion.Propositional.witness_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms witness_correct
/-- info: 'Trion.Propositional.empty_valuation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms empty_valuation
/-- info: 'Trion.Propositional.valuation_count' depends on axioms: [propext] -/
#guard_msgs in
#print axioms valuation_count
/-- info: 'Trion.Propositional.valuations_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms valuations_complete
/-- info: 'Trion.Propositional.cut_off' depends on axioms: [propext] -/
#guard_msgs in
#print axioms cut_off
/-- info: 'Trion.Propositional.exclusion_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exclusion_correct
/-- info: 'Trion.Propositional.unsat_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unsat_sound
/-- info: 'Trion.Propositional.entails_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entails_sound

end Trion.Propositional
