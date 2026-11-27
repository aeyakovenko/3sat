import Std

namespace DilatedMass

/-- At a rank larger than the envelope height, the discounted term must
be the active one. All rates use the same integer denominator. -/
theorem lateRank (rank height unit stretch rate : Nat) (unitPos : 0 < unit)
    (late : height < rank)
    (bound : rank * min unit (stretch * rate) ≤ height * unit) :
    rank * (stretch * rate) ≤ height * unit := by
  have below : stretch * rate < unit := by
    by_cases hup : unit ≤ stretch * rate
    · rw [Nat.min_eq_left hup] at bound
      have := Nat.mul_lt_mul_of_pos_right late unitPos
      omega
    · omega
  simpa [Nat.min_eq_right (Nat.le_of_lt below)] using bound

private theorem sumBounds (values : List Nat) (factor cap : Nat)
    (bound : ∀ x ∈ values, factor * x ≤ cap) :
    factor * values.sum ≤ values.length * cap := by
  induction values with
  | nil => simp
  | cons x xs ih =>
    have first := bound x (by simp)
    have rest := ih (fun y hy => bound y (by simp [hy]))
    simp only [List.sum_cons, List.length_cons, Nat.mul_add, Nat.succ_mul]
    omega

/-- In a late dyadic rank block, the total discounted probability
times the stretch costs at most one copy of the envelope. -/
theorem lateRankBlock (rates : List Nat) (base stretch cap : Nat)
    (positive : 0 < base) (sizeBound : rates.length ≤ base)
    (rankBound : ∀ r ∈ rates, base * (stretch * r) ≤ cap) :
    stretch * rates.sum ≤ cap := by
  have total := sumBounds rates (base * stretch) cap (by
    intro r hr
    simpa [Nat.mul_assoc] using rankBound r hr)
  have products : base * (stretch * rates.sum) ≤ base * cap := by
    simpa [Nat.mul_assoc] using
      Nat.le_trans total (Nat.mul_le_mul_right cap sizeBound)
  by_cases h : cap < stretch * rates.sum
  · have := Nat.mul_lt_mul_of_pos_left h positive
    omega
  · omega

/-- Combine the initial ranks with all later blocks. At least as much
clock stretch as the number of blocks gives a factor-two comparison. -/
theorem doubledEnvelope (early cap stretch : Nat) (blocks : List Nat)
    (earlyBound : early ≤ cap) (positive : 0 < stretch)
    (enough : blocks.length ≤ stretch)
    (blockBound : ∀ x ∈ blocks, stretch * x ≤ cap) :
    early + blocks.sum ≤ 2 * cap := by
  have late := sumBounds blocks stretch cap blockBound
  have budget := Nat.le_trans late (Nat.mul_le_mul_right cap enough)
  have h : blocks.sum ≤ cap := by
    by_cases contrary : cap < blocks.sum
    · have := Nat.mul_lt_mul_of_pos_left contrary positive
      omega
    · omega
  omega

/-- A length threshold for the best soft description is a length-specific
finite running-time test on every name. -/
theorem cutoffTest (length logTime baseline budget : Nat) :
    length + (logTime - baseline) ≤ budget ↔
      length ≤ budget ∧ logTime ≤ baseline + (budget - length) := by omega

end DilatedMass
