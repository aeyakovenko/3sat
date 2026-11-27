import Std

namespace ProbeAllocation

/-- Sum over the first n indices. Natural numbers allow arbitrary common
    denominator scalings of the reciprocal row caps and layer budgets. -/
def segmentSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => segmentSum f n + f n

theorem prefix_mono (a b : Nat → Nat) (h : ∀ i, a i ≤ b i) (n : Nat) :
    segmentSum a n ≤ segmentSum b n := by
  induction n with
  | zero => simp [segmentSum]
  | succ i ih => exact Nat.add_le_add ih (h i)

/-- Drop any one row cap. Each layer can still use a distinct incident row. -/
theorem omit_one (a b : Nat → Nat)
    (left : ∀ i, a i ≤ b i) (right : ∀ i, a i ≤ b (i+1))
    (n t : Nat) (h : t ≤ n) : segmentSum a n + b t ≤ segmentSum b (n+1) := by
  induction n with
  | zero =>
    have : t = 0 := by omega
    simp [this, segmentSum]
  | succ n ih =>
    by_cases hr : t ≤ n
    · have rest := ih hr
      have last := right n
      change segmentSum a n + a n + b t ≤ segmentSum b (n+1) + b (n+1)
      omega
    · have eq : t = n+1 := by omega
      rw [eq]
      exact Nat.add_le_add_right (prefix_mono a b left (n+1)) _

theorem add_all (f : Nat → Nat) (a u n : Nat)
    (bound : ∀ t, t < n → a + f t ≤ u) : n*a + segmentSum f n ≤ n*u := by
  induction n with
  | zero => simp [segmentSum]
  | succ i ih =>
    have prev := ih (fun t ht => bound t (by omega))
    have last := bound i (by omega)
    simp only [Nat.succ_mul, segmentSum]
    omega

/-- Sharp incidence inequality for path layers. Apply it to scaled reciprocal
    masses and reciprocal row gains. It holds before the Cauchy-Schwarz step. -/
theorem path_incidence (a b : Nat → Nat)
    (left : ∀ i, a i ≤ b i) (right : ∀ i, a i ≤ b (i+1)) (n : Nat) :
    (n+1) * segmentSum a n ≤ n * segmentSum b (n+1) := by
  have allRows := add_all b (segmentSum a n) (segmentSum b (n+1)) (n+1)
    (fun t ht => omit_one a b left right n t (by omega))
  rw [Nat.succ_mul n (segmentSum b (n+1))] at allRows
  omega

end ProbeAllocation
