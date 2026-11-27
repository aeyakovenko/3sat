import Std

namespace SoftRecovery

/-- All signed Fourier coefficients have a common positive denominator.
    This rounds the scaled positive part of one coefficient down. -/
def multiplicity (scale denom : Nat) (score : Int) : Nat :=
  scale * score.toNat / denom

/-- The number of Taylor coefficients of total degree less than h. -/
def constraints (h : Nat) : Nat := h * (h + 1) / 2

theorem constraints_le_square (h : Nat) : constraints h ≤ h ^ 2 := by
  apply Nat.div_le_of_le_mul
  cases h with
  | zero => decide
  | succ n =>
    calc
      (n+1) * ((n+1)+1) ≤ (n+1) * (2*(n+1)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (n+1)^2 := by simp only [Nat.pow_two]; ac_rfl

private theorem scaledConstraint (scale denom : Nat) (a : Int) :
    denom^2 * constraints (multiplicity scale denom a) ≤ scale^2 * a.natAbs^2 := by
  let h := multiplicity scale denom a
  have clip : a.toNat ≤ a.natAbs := by cases a <;> simp
  have rounded : denom * h ≤ scale * a.natAbs :=
    Nat.le_trans (Nat.mul_div_le (scale * a.toNat) denom) (Nat.mul_le_mul_left scale clip)
  calc
    denom^2 * constraints h ≤ denom^2 * h^2 := Nat.mul_le_mul_left _ (constraints_le_square h)
    _ = (denom * h) * (denom * h) := by simp only [Nat.pow_two]; ac_rfl
    _ ≤ (scale * a.natAbs) * (scale * a.natAbs) := Nat.mul_le_mul rounded rounded
    _ = scale^2 * a.natAbs^2 := by simp only [Nat.pow_two]; ac_rfl

private theorem totalScaledConstraints (scores : List Int) (scale denom : Nat) :
    denom^2 * (scores.map (fun a => constraints (multiplicity scale denom a))).sum ≤
      scale^2 * (scores.map (fun a => a.natAbs^2)).sum := by
  induction scores with
  | nil => simp
  | cons a rest ih =>
    simpa only [List.map_cons, List.sum_cons, Nat.mul_add] using
      Nat.add_le_add (scaledConstraint scale denom a) ih

/-- An integer Parseval budget bounds the total number of homogeneous
    interpolation constraints after clipping and rounding every signed score. -/
theorem constraintBudget (scores : List Int) (scale denom fieldSize : Nat)
    (positive : 0 < denom)
    (energy : (scores.map (fun a => a.natAbs^2)).sum ≤ denom^2 * fieldSize) :
    (scores.map (fun a => constraints (multiplicity scale denom a))).sum ≤
      scale^2 * fieldSize := by
  apply Nat.le_of_mul_le_mul_left (c := denom^2) _ (Nat.pow_pos positive)
  calc
    _ ≤ scale^2 * (scores.map (fun a => a.natAbs^2)).sum := totalScaledConstraints ..
    _ ≤ scale^2 * (denom^2 * fieldSize) := Nat.mul_le_mul_left _ energy
    _ = denom^2 * (scale^2 * fieldSize) := by ac_rfl

private theorem clippedSum (scores : List Int) :
    scores.sum ≤ ((scores.map Int.toNat).sum : Int) := by
  induction scores with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, Int.natCast_add]
    omega

private theorem graphRoundoff (scores : List Int) (scale denom : Nat) (positive : 0 < denom) :
    scale * (scores.map Int.toNat).sum ≤
      denom * ((scores.map (multiplicity scale denom)).sum + scores.length) := by
  induction scores with
  | nil => simp
  | cons a rest ih =>
    have rem := Nat.mod_lt (scale * a.toNat) positive
    have split := Nat.div_add_mod (scale * a.toNat) denom
    have one : scale * a.toNat ≤ denom * multiplicity scale denom a + denom := by
      unfold multiplicity
      omega
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one] at *
    omega

/-- Along one graph, rounding loses at most one unit of multiplicity per
    coordinate. A signed sum with this much clearance forces more roots than
    the specified degree, including multiplicities. -/
theorem graphScore (scores : List Int) (scale denom degree : Nat) (positive : 0 < denom)
    (margin : denom * (degree + scores.length) < scale * scores.sum.toNat) :
    degree < (scores.map (multiplicity scale denom)).sum := by
  have clipped := clippedSum scores
  have h : scores.sum.toNat ≤ (scores.map Int.toNat).sum := by omega
  have strong := Nat.lt_of_lt_of_le margin (Nat.le_trans (Nat.mul_le_mul_left scale h)
    (graphRoundoff scores scale denom positive))
  by_cases contrary : (scores.map (multiplicity scale denom)).sum ≤ degree
  · have bound := Nat.mul_le_mul_left denom (Nat.add_le_add_right contrary scores.length)
    omega
  · omega

end SoftRecovery
