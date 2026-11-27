import Std

namespace DiscountedMass

/-- For scores scaled to a common denominator, the same estimate bounds both
the number of exceptional lengths and the rank at a specified score. -/
theorem thresholdMass (threshold : Nat) (scores : List Nat) :
    threshold * (scores.filter (fun x => decide (threshold ≤ x))).length ≤ scores.sum := by
  induction scores with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : threshold ≤ x
    · simp [List.filter_cons, hx, Nat.mul_add, Nat.mul_succ]
      omega
    · simp [List.filter_cons, hx]
      omega

/-- Removing a tail of at most half the total and then approximating the
remaining terms from below by a factor four retains at least an eighth. -/
theorem truncationAndRounding (score retained tail : Nat)
    (rounding : retained ≤ 4 * score) (smallTail : tail ≤ retained) :
    retained + tail ≤ 8 * score := by omega

/-- At least one dyadic bin attains the averaging bound when the truncated
bins retain at least half of a positive total. -/
theorem hasLargeBin (bins : List Nat) (total : Nat) (positive : 0 < total)
    (retention : total ≤ 2 * bins.sum) :
    ∃ w ∈ bins, total ≤ 2 * bins.length * w := by
  have sumCap (xs : List Nat) (cap : Nat) (bound : ∀ x ∈ xs, x ≤ cap) :
      xs.sum ≤ xs.length * cap := by
    induction xs with
    | nil => simp
    | cons y ys ih =>
      have byHead := bound y (by simp)
      have byTail := ih (fun x h => bound x (by simp [h]))
      simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  cases bins with
  | nil => simp at retention; omega
  | cons x xs =>
    have peak (y : Nat) (ys : List Nat) :
        ∃ z ∈ y :: ys, ∀ w ∈ y :: ys, w ≤ z := by
      induction ys generalizing y with
      | nil => exact ⟨y, by simp, by simp⟩
      | cons a as ih =>
        obtain ⟨z, hz, bound⟩ := ih a
        by_cases yz : y ≤ z
        · exact ⟨z, by simp [hz], fun w hw => by
              rcases List.mem_cons.mp hw with h | h
              · simpa [h] using yz
              · exact bound w h⟩
        · exact ⟨y, by simp, fun w hw => by
              rcases List.mem_cons.mp hw with h | h
              · simp [h]
              · exact Nat.le_trans (bound w h) (by omega)⟩
    obtain ⟨z, hz, cap⟩ := peak x xs
    refine ⟨z, hz, ?_⟩
    calc
      total ≤ 2 * (x :: xs).sum := retention
      _ ≤ 2 * ((x :: xs).length * z) := Nat.mul_le_mul_left 2 (sumCap _ _ cap)
      _ = 2 * (x :: xs).length * z := (Nat.mul_assoc _ _ _).symm

end DiscountedMass
