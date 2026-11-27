import Std

namespace DominoHistory

/-- The four corners of a product interval contribute the product of the
    two low-bit domino boundary indicators. -/
theorem rectangle_block (row0 row1 col0 col1 : Bool) :
    ((row0 && col0) ^^ (row0 && col1) ^^ (row1 && col0) ^^ (row1 && col1)) =
      ((row0 ^^ row1) && (col0 ^^ col1)) := by
  cases row0 <;> cases row1 <;> cases col0 <;> cases col1 <;> decide

/-- Values of x XOR y on the four corners have low bits in checkerboard
    order. This formula includes both diagonal choices and the empty case. -/
theorem track_block (row0 row1 evenOffset oddOffset : Bool) :
    ((row0 && evenOffset) ^^ (row0 && oddOffset) ^^
        (row1 && oddOffset) ^^ (row1 && evenOffset)) =
      ((row0 ^^ row1) && (evenOffset ^^ oddOffset)) := by
  cases row0 <;> cases row1 <;> cases evenOffset <;> cases oddOffset <;> decide

/-- A half-open interval that splits an adjacent even/odd pair has an
    endpoint at their common internal boundary. -/
theorem interval_splits {lo hi i : Nat}
    (split : ¬ ((lo ≤ 2*i ∧ 2*i < hi) ↔ (lo ≤ 2*i+1 ∧ 2*i+1 < hi))) :
    lo = 2*i+1 ∨ hi = 2*i+1 := by
  omega

theorem not_three_splits (lo hi i j k : Nat)
    (different : i ≠ j ∧ j ≠ k ∧ i ≠ k)
    (cut : ∀ t, t = i ∨ t = j ∨ t = k →
      ¬ ((lo ≤ 2*t ∧ 2*t < hi) ↔ (lo ≤ 2*t+1 ∧ 2*t+1 < hi))) : False := by
  have a := interval_splits (cut i (by simp))
  have b := interval_splits (cut j (by simp))
  have c := interval_splits (cut k (by simp))
  omega

/-- A hit in a fixed row pair forces at most one column pair for this
    offset, regardless of which of the four points was hit. -/
theorem unique_track_column (x y d : Nat) (onTrack : x ^^^ y = d) :
    y / 2 = (x / 2) ^^^ (d / 2) := by
  have h : (x >>> 1) ^^^ (y >>> 1) = d >>> 1 := by
    rw [← Nat.shiftRight_xor_distrib, onTrack]
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one] at h
  rw [← h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

end DominoHistory
