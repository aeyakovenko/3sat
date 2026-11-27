import Std

/-! Logical consequences of a sound, complete-up-to-budget trace search.
This file does not implement a distance algorithm or a dynamic index. -/
namespace CappedTraceVerdicts

/-- A successful search exposes the actual new verdict. Every edge within
budget produces a success. Searches may also succeed beyond that budget. -/
def CappedCorrect (result : Option Bool) (actual : Bool) (distance budget : Nat) : Prop :=
  (∀ v, result = some v → v = actual) ∧ (distance ≤ budget → result = some actual)

theorem infer_missing_verdict {result : Option Bool} {actual designated : Bool}
    {d r : Nat} (search : CappedCorrect result actual d r)
    (covered : actual = designated → d ≤ r) :
    result.getD (!designated) = actual := by
  cases h : result with
  | some v => exact search.1 _ h
  | none =>
    have hne : actual ≠ designated := by
      intro eq
      have hs := search.2 (covered eq)
      simp [h] at hs
    cases actual <;> cases designated <;> simp_all

/-- Only same-b to same-b edges are required to be short. The baseline
verdict must be b for this rule. -/
theorem same_baseline {result : Option Bool} {old actual b : Bool} {d r : Nat}
    (search : CappedCorrect result actual d r) (baseline : old = b)
    (short : old = b → actual = b → d ≤ r) :
    result.getD (!b) = actual :=
  infer_missing_verdict search (short baseline)

/-- If every opposite-verdict edge is short, failure preserves the old
verdict. Either orientation of a changing edge is covered. -/
theorem opposite_baseline {result : Option Bool} {old actual : Bool} {d r : Nat}
    (search : CappedCorrect result actual d r) (short : old ≠ actual → d ≤ r) :
    result.getD old = actual := by
  have covered (h : actual = !old) : d ≤ r := by
    apply short
    rw [h]
    cases old <;> decide
  simpa using infer_missing_verdict search covered

inductive Edit {α : Type} : List α → List α → Nat → Prop where
  | empty : Edit [] [] 0
  | keep (a : α) : Edit xs ys d → Edit (a :: xs) (a :: ys) d
  | drop (a : α) : Edit xs ys d → Edit (a :: xs) ys (d+1)
  | insert (a : α) : Edit xs ys d → Edit xs (a :: ys) (d+1)

theorem edit_length_gap {α : Type} {xs ys : List α} {d : Nat} (e : Edit xs ys d) :
    ys.length ≤ xs.length + d ∧ xs.length ≤ ys.length + d := by
  induction e <;> simp_all <;> omega

/-- Only successful patches belong to this chain. Queries discarded by the
caller consume no edge or length budget. -/
inductive Patches {α : Type} (r : Nat) (start : List α) : Nat → List α → Prop where
  | base : Patches r start 0 start
  | push (prior : Patches r start count xs) (step : Edit xs ys d) (cap : d ≤ r) :
      Patches r start (count+1) ys

theorem patched_length {α : Type} {r k : Nat} {start finish : List α}
    (path : Patches r start k finish) :
    finish.length ≤ start.length + k*r ∧ start.length ≤ finish.length + k*r := by
  induction path with
  | base => simp
  | push prior e cap ih =>
    obtain ⟨left, right⟩ := edit_length_gap e
    simp only [Nat.add_mul, Nat.one_mul]
    omega

end CappedTraceVerdicts
