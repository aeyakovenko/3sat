import Std

namespace MultilinearClockSupport

/-- A one-coordinate weight for evaluation of a Boolean table. -/
def weight {R : Type} (zero one : R) (sub mul : R → R → R) :
    List (Bool × R) → R
  | [] => one
  | (bit, z) :: xs =>
      mul (if bit then z else sub one z) (weight zero one sub mul xs)

def ones {R : Type} (xs : List (Bool × R)) : Nat :=
  (xs.filter (fun v => v.1)).length

def supported {R : Type} [DecidableEq R] (zero : R) (xs : List (Bool × R)) : Nat :=
  (xs.filter (fun v => decide (v.2 ≠ zero))).length

/-- Only zero absorption is needed for the support implication, so it applies
    in particular to the field operations of every oracle gate. -/
theorem support_bound {R : Type} [DecidableEq R] (z o : R) (sub mul : R → R → R)
    (left : ∀ a, mul z a = z) (right : ∀ a, mul a z = z)
    (xs : List (Bool × R)) (nz : weight z o sub mul xs ≠ z) :
    ones xs ≤ supported z xs := by
  induction xs with
  | nil => simp [ones, supported]
  | cons v vs ih =>
    have nt : weight z o sub mul vs ≠ z := by
      intro e
      apply nz
      simp [weight, e, right]
    have tail := ih nt
    rcases v with ⟨b, x⟩
    cases b <;> by_cases eq : x = z <;>
      simp_all [weight, ones, supported, left] <;> omega

theorem long_wrapper_unavailable (support budget length queryLength : Nat)
    (spent : support ≤ budget) (padding : 2 * budget < length)
    (long : length ≤ queryLength) : ¬ queryLength < 2 * support := by omega

end MultilinearClockSupport
