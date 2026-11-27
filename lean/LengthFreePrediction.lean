import Std

namespace LengthFreePrediction

/-- Exact halts and further input requests are disjoint. Two strict majorities
cannot prescribe different operations on the program stream. -/
theorem majorityParse (total halted more : Nat) (disjoint : halted + more ≤ total)
    (read : total < 2*more) : ¬ total < 2*halted := by omega

/-- A common finite completion can change only unresolved challenge answers. -/
theorem corrFromMatches (total hits pos neg K : Nat)
    (partition : pos + neg = total) (kept : hits ≤ pos)
    (advantage : total * K + 2 * total < 2 * (hits * K)) :
    2 * total + neg*K < pos*K := by
  have enlarged := Nat.mul_le_mul_right K kept
  have split := congrArg (fun v => v * K) partition
  simp only [Nat.add_mul] at split
  omega

/-- The scaled first/second moment comparison for binary rows of coherence
at most 1/K² bounds the number having correlation at least 2/K. -/
theorem listBudget (L K : Nat) (pos : 0 < L)
    (moments : (4*L)*L ≤ K^2*L + (L-1)*L) : L ≤ K^2 := by
  rw [← Nat.add_mul] at moments
  have bound : 4*L ≤ K^2 + (L-1) := by
    by_cases h : K^2 + (L-1) < 4*L
    · have strict := Nat.mul_lt_mul_of_pos_right h pos
      omega
    · omega
  omega

/-- Opposite signs on the fresh final bit cancel at every fixed prefix,
with no requirement on how another row depends on the preceding bits. -/
theorem markerCancels (earlier mask : Int) :
    earlier * mask + earlier * (-mask) = 0 := by
  rw [Int.mul_neg]; omega

end LengthFreePrediction
