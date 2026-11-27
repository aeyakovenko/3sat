import Std

namespace MarginalGrowth

/-- Clear the denominators of a lower bound A/B on successive ratios.
    Multiplying it through all stages cancels the intermediate marginals. -/
theorem telescope (u : Nat → Nat) (A B r : Nat)
    (step : ∀ i < r, A * u i ≤ B * u (i+1)) :
    A^r * u 0 ≤ B^r * u r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have previous := ih (fun i hi => step i (by omega))
    calc
      A^(r+1) * u 0 = A * (A^r * u 0) := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ A * (B^r * u r) := Nat.mul_le_mul_left _ previous
      _ = B^r * (A * u r) := by ac_rfl
      _ ≤ B^r * (B * u (r+1)) := Nat.mul_le_mul_left _ (step r (by omega))
      _ = B^(r+1) * u (r+1) := by rw [Nat.pow_succ]; ac_rfl

/-- Compare adjacent marginal ratios at two indices without division. -/
def ratioLE (u : Nat → Nat) (i j : Nat) : Prop :=
  u (i+1) * u j ≤ u (j+1) * u i

private theorem ratioTrans (u : Nat → Nat) (i j k : Nat) (positive : 0 < u j)
    (first : ratioLE u i j) (second : ratioLE u j k) : ratioLE u i k := by
  apply Nat.le_of_mul_le_mul_right (c := u j) _ positive
  calc
    (u (i+1) * u k) * u j = (u (i+1) * u j) * u k := by ac_rfl
    _ ≤ (u (j+1) * u i) * u k := Nat.mul_le_mul_right _ first
    _ = (u (j+1) * u k) * u i := by ac_rfl
    _ ≤ (u (k+1) * u j) * u i := Nat.mul_le_mul_right _ second
    _ = (u (k+1) * u i) * u j := by ac_rfl

/-- Select the first minimum ratio among stages zero through k inclusive. -/
def selected (u : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k+1 =>
    let prev := selected u k
    if u (k+2) * u prev < u (prev+1) * u (k+1) then k+1 else prev

theorem selected_bound (u : Nat → Nat) (k : Nat) : selected u k ≤ k := by
  induction k with
  | zero => simp [selected]
  | succ k ih => simp only [selected]; split <;> omega

theorem selected_min (u : Nat → Nat) (k : Nat) (positive : ∀ i ≤ k, 0 < u i) :
    ∀ i ≤ k, ratioLE u (selected u k) i := by
  induction k with
  | zero =>
    intro i hi
    have eq : i = 0 := by omega
    simp [selected, eq, ratioLE]
  | succ k ih =>
    have prev := ih (fun i hi => positive i (by omega))
    intro i hi
    simp only [selected]
    split
    next h =>
      have better : ratioLE u (k+1) (selected u k) := Nat.le_of_lt h
      by_cases he : i = k+1
      · simp [ratioLE, he]
      · exact ratioTrans u _ _ _ (positive _ (by have := selected_bound u k; omega))
          better (prev _ (by omega))
    next h =>
      by_cases he : i = k+1
      · subst i
        exact Nat.le_of_not_gt h
      · exact prev i (by omega)

/-- The selected marginal growth raised to the number of steps is at most
    the total growth. All stages refer to one common integer mass scale. -/
theorem selected_growth (u : Nat → Nat) (k : Nat) (positive : ∀ i ≤ k, 0 < u i) :
    (u (selected u k + 1))^(k+1) * u 0 ≤
      (u (selected u k))^(k+1) * u (k+1) := by
  apply telescope
  intro i hi
  simpa [ratioLE, Nat.mul_comm] using selected_min u k positive i (by omega)

/-- If the next joint atom has at least A/B times the old marginal, then
    its normalized mass to the r-th power is at least
    (A/B)^r times the initial-to-last marginal ratio. This is its
    division-free form and also covers zero atom mass. -/
theorem normalizedMass (u joint : Nat → Nat) (A B k : Nat)
    (positive : ∀ i ≤ k, 0 < u i)
    (atom : ∀ i ≤ k, A * u i ≤ B * joint (i+1)) :
    A^(k+1) * ((u (selected u k+1))^(k+1) * u 0) ≤
      (B * joint (selected u k+1))^(k+1) * u (k+1) := by
  let i := selected u k
  have hg := selected_growth u k positive
  have ha := Nat.pow_le_pow_left (atom i (selected_bound u k)) (k+1)
  change A^(k+1) * ((u (i+1))^(k+1) * u 0) ≤ (B * joint (i+1))^(k+1) * u (k+1)
  calc
    _ ≤ A^(k+1) * ((u i)^(k+1) * u (k+1)) := Nat.mul_le_mul_left _ hg
    _ = (A * u i)^(k+1) * u (k+1) := by rw [Nat.mul_pow]; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ ha

end MarginalGrowth
