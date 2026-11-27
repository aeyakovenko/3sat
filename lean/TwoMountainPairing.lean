import Std

namespace TwoMountainPairing

/-- Positions are zero based. Reflect within the first or second mountain. -/
def mate (n k t : Nat) : Nat :=
  if t < 2 * k then 2 * k - 1 - t else 2 * n + 2 * k - 1 - t

def oddSlot (n k i : Nat) : Nat :=
  if i < k then k - 1 - i else n + k - 1 - i

theorem even_pairs_odd {n k i : Nat} (hk : k ≤ n) (hi : i < n) :
    mate n k (2*i) = 2 * oddSlot n k i + 1 ∧ oddSlot n k i < n := by
  unfold mate oddSlot
  by_cases h : i < k <;> split <;> omega

/-- The offset below n that connects input i to the odd output j. -/
def offset (n i j : Nat) : Nat :=
  if i + j + 1 < n then i + j + 1 else i + j + 1 - n

theorem unique_offset {n i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) :
    oddSlot n k i = j ↔ k = offset n i j := by
  unfold oddSlot offset
  split <;> split <;> omega

theorem offset_in_range {n i j : Nat} (hi : i < n) (hj : j < n) :
    offset n i j < n := by
  unfold offset
  split <;> omega

end TwoMountainPairing
