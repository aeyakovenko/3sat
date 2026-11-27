import Std

namespace LocalBagConsistency

/-- Integer-scaled probabilities of the common bit in successive path bags. -/
theorem endpoint_gap (p : Nat → Nat) (err : Nat) (first : p 0 = 0)
    (step : ∀ i, p (i + 1) ≤ p i + err) (last : Nat) :
    p last ≤ last * err := by
  induction last with
  | zero => simp [first]
  | succ i ih =>
    calc
      p (i+1) ≤ p i + err := step i
      _ ≤ i * err + err := Nat.add_le_add_right ih err
      _ = (i+1)*err := by rw [Nat.succ_mul]

/-- If A,C each forbid at most ell cuts out of h, their overlap gives
    the stated cross-multiplied total variation bound for uniform laws.
    `a + c ≤ h + both` is the union cardinality inequality. -/
theorem uniform_cut_overlap (h ell a c both : Nat)
    (missA : h ≤ a + ell) (missC : h ≤ c + ell)
    (union_bound : a + c ≤ h + both) :
    (max a c - both) * (h - ell) ≤ ell * max a c := by
  have numerator : max a c - both ≤ ell := by
    cases Nat.le_total a c with
    | inl less => rw [Nat.max_eq_right less]; omega
    | inr less => rw [Nat.max_eq_left less]; omega
  have denominator : h - ell ≤ max a c := by
    have := Nat.le_max_left a c
    omega
  exact Nat.mul_le_mul numerator denominator

end LocalBagConsistency
