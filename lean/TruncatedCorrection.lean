import Std

namespace TruncatedCorrection

/-- Evaluate products of base factors and their additive corrections, keeping
at most k corrected positions. This recurrence is the subset expansion. -/
def truncated : Nat → List (Int × Int) → Int
  | _, [] => 1
  | 0, (a, _) :: xs => a * truncated 0 xs
  | k+1, (a, b) :: xs => a * truncated (k+1) xs + b * truncated k xs

def full : List (Int × Int) → Int
  | [] => 1
  | (a, b) :: xs => (a+b) * full xs

def active : List (Int × Int) → Nat
  | [] => 0
  | (_, b) :: xs => if b = 0 then active xs else active xs + 1

/-- The full product is recovered whenever at most k corrections are nonzero. -/
theorem truncated_eq (xs : List (Int × Int)) (k : Nat) (bound : active xs ≤ k) :
    truncated k xs = full xs := by
  induction xs generalizing k with
  | nil => simp [truncated, full]
  | cons head xs ih =>
    obtain ⟨a, b⟩ := head
    by_cases hb : b = 0
    · subst b
      simp only [active, if_pos rfl] at bound
      cases k <;> simp [truncated, full, ih _ bound]
    · simp only [active, if_neg hb] at bound
      cases k with
      | zero => omega
      | succ k =>
        have h₁ : active xs ≤ k := by omega
        have h₂ : active xs ≤ k+1 := by omega
        simp only [truncated, full, ih _ h₁, ih _ h₂, Int.add_mul]

/-- One monomial, given as (value of coordinate, exponent) pairs. -/
def linearPower (x : Int) : Nat → Int
  | 0 => 1
  | _+1 => x

def factors : List (Int × Nat) → List (Int × Int)
  | [] => []
  | (x, e) :: xs => (x^e, linearPower x e - x^e) :: factors xs

def repeats : List (Int × Nat) → Nat
  | [] => 0
  | (_, e) :: xs => if 2 ≤ e then repeats xs + 1 else repeats xs

def multilinearValue : List (Int × Nat) → Int
  | [] => 1
  | (x, e) :: xs => linearPower x e * multilinearValue xs

theorem active_le_repeats (xs : List (Int × Nat)) : active (factors xs) ≤ repeats xs := by
  induction xs with
  | nil => decide
  | cons head xs ih =>
    obtain ⟨x, e⟩ := head
    cases e with
    | zero => simpa [factors, active, repeats, linearPower] using ih
    | succ n =>
      cases n with
      | zero => simpa [factors, active, repeats, linearPower, Int.pow_succ] using ih
      | succ n =>
        simp only [factors, active, repeats]
        split <;> split <;> omega

theorem full_factors (xs : List (Int × Nat)) : full (factors xs) = multilinearValue xs := by
  induction xs with
  | nil => rfl
  | cons head xs ih =>
    obtain ⟨x, e⟩ := head
    simp only [factors, full, multilinearValue, ih]
    have simplify : x^e + (linearPower x e - x^e) = linearPower x e := by omega
    rw [simplify]

/-- Truncating by the number of repeated variables recovers the Boolean
multilinearization of a monomial at any integer point. -/
theorem correct_monomial (xs : List (Int × Nat)) (k : Nat) (hr : repeats xs ≤ k) :
    truncated k (factors xs) = multilinearValue xs :=
  (truncated_eq _ k (Nat.le_trans (active_le_repeats xs) hr)).trans (full_factors xs)

end TruncatedCorrection
