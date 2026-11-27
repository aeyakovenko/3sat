import Std

namespace ProducerProofExtension

theorem nameLength (header parameter phase cell d g b j m : Nat)
    (cellLength : cell + phase + d + g = b)
    (block : b ≤ j) (output : j ≤ m) (savings : header + parameter < d) :
    header + parameter + phase + cell + (j-b+g) + (m-j) < m := by omega

/-- The successful window can spend at most one window of new certificates. -/
theorem failedMass (pool successWindow newFailure newSuccess : Nat)
    (full : newFailure + newSuccess = pool)
    (oneWindow : newSuccess ≤ successWindow) :
    pool - successWindow ≤ newFailure := by omega

/-- Every late length here is known to be fully covered by the shared generator,
    and fails to be fully covered in the original early test. -/
theorem lateLengths (earlyBound earlyCovered lateCovered factor : Nat)
    (declined : earlyCovered ≤ earlyBound)
    (generated : factor*earlyBound ≤ earlyCovered+lateCovered) :
    (factor-1)*earlyBound ≤ lateCovered := by
  cases factor with
  | zero => simp
  | succ f =>
    simp only [Nat.succ_mul] at generated
    simp only [Nat.succ_sub_one]
    omega

end ProducerProofExtension
