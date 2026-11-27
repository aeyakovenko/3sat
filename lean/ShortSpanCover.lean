import Std

namespace ShortSpanCover

/-- ceil(log₂(R+1)), including the empty random tape. -/
def generators (R : Nat) := if R = 0 then 0 else R.log2 + 1

theorem rounding (R : Nat) : R < 2^generators R ∧ 2^generators R ≤ 2*(R+1) := by
  by_cases h : R = 0
  · subst R; decide
  · have lower := Nat.log2_self_le h
    have upper := Nat.lt_log2_self (n := R)
    simp only [generators, if_neg h, Nat.pow_succ] at *
    omega

/-- Exact integer iteration of the existential one-shift bound in
    LexFactorResponse.uncovered_square. -/
theorem iterated {N : Nat} (pos : 0 < N) (u : Nat → Nat)
    (initial : 2*u 0 ≤ N) (step : ∀ i, N*u (i+1) ≤ (u i)^2) :
    ∀ i, 2^(2^i) * u i ≤ N := by
  intro i
  induction i with
  | zero => simpa using initial
  | succ i ih =>
    let c := 2^(2^i)
    have recurrence := Nat.mul_le_mul_left (c*c) (step i)
    have square := Nat.mul_le_mul ih ih
    have bound : N*((c*c)*u (i+1)) ≤ N*N := calc
      _ = (c*c)*(N*u (i+1)) := by ac_rfl
      _ ≤ (c*c)*(u i)^2 := recurrence
      _ = (c*u i)*(c*u i) := by rw [Nat.pow_two]; ac_rfl
      _ ≤ N*N := square
    have cancel := Nat.le_of_mul_le_mul_left bound pos
    simpa only [Nat.pow_succ, Nat.mul_two, Nat.pow_add, c] using cancel

theorem no_uncovered {R : Nat} (u : Nat → Nat) (initial : 2*u 0 ≤ 2^R)
    (step : ∀ i, 2^R*u (i+1) ≤ (u i)^2) : u (generators R) = 0 := by
  have high := iterated (Nat.pow_pos (by decide)) u initial step (generators R)
  have strict : 2^R < 2^(2^generators R) := Nat.pow_lt_pow_of_lt (by decide) (rounding R).1
  by_cases h : u (generators R) = 0
  · exact h
  · have large := Nat.mul_le_mul_left (2^(2^generators R)) (Nat.pos_of_ne_zero h)
    simp only [Nat.mul_one] at large
    omega

/-- Even if every one of the 2^g translations contributed all its points,
    a small accepting set could not cover the whole cube. -/
theorem low_cannot_cover (R hits covered : Nat) (sparse : 2*(R+1)*hits < 2^R)
    (unionBound : covered ≤ 2^generators R * hits) : covered < 2^R :=
  Nat.lt_of_le_of_lt (Nat.le_trans unionBound (Nat.mul_le_mul_right hits (rounding R).2)) sparse

end ShortSpanCover
