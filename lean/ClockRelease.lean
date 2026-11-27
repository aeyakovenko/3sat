import Std

namespace ClockRelease

/-- Number of raw indices in a contiguous prefix allocation after thinning by m. -/
def allot (before seeds divisor : Nat) : Nat :=
  (before + seeds) / divisor - before / divisor

theorem quotientMonotone (before seeds divisor : Nat) :
    before / divisor ≤ (before + seeds) / divisor := by
  cases divisor with
  | zero => simp
  | succ d =>
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos d)).2
    rw [Nat.mul_comm]
    exact Nat.le_trans (Nat.mul_div_le before d.succ) (by omega)

theorem adjacentAllocations (before left right divisor : Nat) :
    allot before left divisor + allot (before + left) right divisor =
      allot before (left + right) divisor := by
  have h₁ := quotientMonotone before left divisor
  have h₂ := quotientMonotone (before + left) right divisor
  simp only [allot, ← Nat.add_assoc]
  omega

theorem roundingLoss (before seeds divisor : Nat) (positive : 0 < divisor) :
    seeds < divisor * (allot before seeds divisor + 1) := by
  have h₀ := quotientMonotone before seeds divisor
  have h₁ := Nat.div_add_mod before divisor
  have h₂ := Nat.div_add_mod (before + seeds) divisor
  have h₃ := Nat.mod_lt (before + seeds) positive
  have decomp : (before + seeds) / divisor = before / divisor + allot before seeds divisor := by
    unfold allot
    omega
  rw [decomp, Nat.mul_add] at h₂
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- If at least one currently missing word stays missing in this cell,
    the allocation is paid in full, with no saturation. -/
theorem survivingCell (holes born assigned : Nat)
    (progress : min holes assigned ≤ born) (survives : born < holes) :
    assigned ≤ born ∧ assigned < holes := by omega

end ClockRelease
