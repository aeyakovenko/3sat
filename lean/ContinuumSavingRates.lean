import Std

namespace ContinuumSavingRates

/-- Splitting rate and rank digits over a streaming input still gives a
    strictly eligible name, even with a separately encoded length cutoff. -/
theorem interleavedName (header savingCode dCode p c d b m : Nat)
    (fits : d + c + dCode + p + b ≤ m) (cheap : header + savingCode < c) :
    header + savingCode + dCode + p + b + (m - (d + c + dCode + p + b)) < m - d := by
  omega

/-- Refining the rate prefix by at most the change in output length
    leaves the previous rank grid aligned on the new grid. -/
theorem rankDepthMonotone (overhead m n b b' : Nat)
    (growth : m + b' ≤ n + b) :
    m - (overhead + b) ≤ n - (overhead + b') := by
  omega

/-- Counting on a common fine dyadic grid cancels the per-path charge
    for the b rate digits of an individual allocated word. -/
theorem integratedCell (fine b wordUnits : Nat) (fits : b ≤ fine) :
    2^(fine-b) * (2^b * wordUnits) = 2^fine * wordUnits := by
  rw [←Nat.mul_assoc, ←Nat.pow_add, Nat.sub_add_cancel fits]

/-- A common first completion time can pay for a word in only one
    member of a collection of nonoverlapping, ordered time windows. -/
theorem uniqueCell (early late : Nat → Nat)
    (ordered : ∀ i j, i < j → late i ≤ early j)
    (t i j : Nat) (one : early i < t ∧ t ≤ late i)
    (two : early j < t ∧ t ≤ late j) : i = j := by
  apply Classical.byContradiction
  intro ne
  by_cases lt : i < j
  · have := ordered i j lt
    omega
  · have gt : j < i := by omega
    have := ordered j i gt
    omega

end ContinuumSavingRates
