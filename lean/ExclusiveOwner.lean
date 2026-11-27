import Std

namespace ExclusiveOwner

/-- A Bernoulli trial with `h` hit outcomes and `h+d` misses preserves the
    upper bound of one half on mass at a single success. -/
theorem half_preserved (noneCount one total h d : Nat)
    (mass : noneCount + one ≤ total) (half : 2 * one ≤ total) :
    2 * ((h+d)*one + h*noneCount) ≤ (d + 2*h)*total := by
  calc
    2 * ((h+d)*one + h*noneCount) = d*(2*one) + (2*h)*(noneCount+one) := by
      simp only [Nat.add_mul, Nat.mul_add]
      ac_rfl
    _ ≤ d*total + (2*h)*total :=
      Nat.add_le_add (Nat.mul_le_mul_left d half) (Nat.mul_le_mul_left _ mass)
    _ = _ := (Nat.add_mul _ _ _).symm

/-- Count zero-success and one-success outcomes in a product of such trials. -/
def counts : List (Nat × Nat) → Nat × Nat × Nat
  | [] => (1, 0, 1)
  | (h,d)::rest =>
    let (z,o,t) := counts rest
    ((h+d)*z, (h+d)*o+h*z, (d+2*h)*t)

theorem singleton_at_most_half (trials : List (Nat × Nat)) :
    let (z,o,t) := counts trials
    z+o ≤ t ∧ 2*o ≤ t := by
  induction trials with
  | nil => decide
  | cons pair rest ih =>
    obtain ⟨h,d⟩ := pair
    cases e : counts rest with
    | mk z other =>
      obtain ⟨o,t⟩ := other
      simp only [counts, e] at ih ⊢
      constructor
      · calc
          (h+d)*z+((h+d)*o+h*z) ≤ (d+2*h)*(z+o) := by
            simp only [Nat.add_mul, Nat.mul_add, Nat.two_mul]
            omega
          _ ≤ _ := Nat.mul_le_mul_left _ ih.1
      · exact half_preserved z o t h d ih.1 ih.2

end ExclusiveOwner
