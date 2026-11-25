import Std

namespace RecoveredListGadgets

/-- The three binary clauses of a bank triangle, in recovered polarities. -/
def triangle (p f c : Bool) : Prop :=
  (p = false ∨ f = false) ∧ (p = false ∨ c = true) ∧ (f = false ∨ c = true)

def bank (p : Bool) : List Bool → Prop
  | [] => True
  | f :: fs => ∃ c : Bool, triangle p f c ∧ bank c fs

/-- Existential choice of every cursor is exactly a bound of one on the
    initial true cursor and all succeeding true flags combined. -/
theorem bank_iff (p : Bool) (fs : List Bool) :
    bank p fs ↔ (if p then 1 else 0) + fs.count true ≤ 1 := by
  induction fs generalizing p with
  | nil => cases p <;> simp [bank]
  | cons f fs ih =>
    cases p <;> cases f <;>
      simp [bank, triangle, ih, Bool.exists_bool, List.count_cons] <;> omega

/-- The selected-row threshold updates the seen and two-seen registers
    with the original two disjunctions and one conjunction. -/
def threshold (seen two : Bool) : List Bool → Bool
  | [] => two
  | s :: ss => threshold (seen || s) (two || (seen && s)) ss

theorem threshold_seeded (ss : List Bool) (k : Nat) :
    threshold (decide (1 ≤ k)) (decide (2 ≤ k)) ss =
      decide (2 ≤ k + ss.count true) := by
  induction ss generalizing k with
  | nil => simp [threshold]
  | cons s ss ih =>
    cases s with
    | false => simpa [threshold, List.count_cons] using ih k
    | true =>
      have h : (decide (2 ≤ k) || decide (1 ≤ k)) = decide (2 ≤ k+1) := by
        by_cases a : 1 ≤ k
        · simp [a, show 2 ≤ k+1 by omega]
        · simp [a, show ¬ 2 ≤ k by omega, show ¬ 2 ≤ k+1 by omega]
      simpa [threshold, List.count_cons, h, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih (k+1)

theorem threshold_from_zero (ss : List Bool) :
    threshold false false ss = decide (2 ≤ ss.count true) := by
  simpa using threshold_seeded ss 0

end RecoveredListGadgets
