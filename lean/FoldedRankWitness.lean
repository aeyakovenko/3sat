import Std

/-! The `rank E ≥ h` step of the folded binary matrix-product check. If h selected
positions are on the earliest nonzero antidiagonal, increasing their row coordinates
makes a triangular minor. Every nonempty sorted selection of its columns has a
nonzero xor in the row of its first member. This file does not model tensor rank,
rectangular algorithms, or the Vandermonde hitting set. -/
namespace FoldedRankWitness

/-- At one physical row, sum some physical columns modulo two. -/
def rowParity (entry : Nat → Nat → Bool) (row : Nat) : List Nat → Bool
  | [] => false
  | col :: rest => Bool.xor (entry row col) (rowParity entry row rest)

private theorem zeroParity (entry : Nat → Nat → Bool) (row : Nat) (cols : List Nat)
    (zeros : ∀ col ∈ cols, entry row col = false) : rowParity entry row cols = false := by
  induction cols with
  | nil => rfl
  | cons h t ih =>
    have head := zeros h (by simp)
    have tail := ih (fun col hc => zeros col (by simp [hc]))
    simp [rowParity, head, tail]

/-- Every chosen column list with smallest row index `p` contributes exactly
one to the row `rows p` in its xor. This applies to every nonempty sorted subset. -/
theorem earliestAntidiagonalIndependent
    (entry : Nat → Nat → Bool) (rows cols : Nat → Nat) (weight : Nat)
    (earlier : ∀ x y, x + y < weight → entry x y = false)
    (p : Nat) (rest : List Nat)
    (diagonal : entry (rows p) (cols p) = true)
    (sameWeight : ∀ q ∈ rest, rows q + cols q = weight)
    (increasing : ∀ q ∈ rest, rows p < rows q) :
    rowParity entry (rows p) ((p :: rest).map cols) = true := by
  have vanishes : rowParity entry (rows p) (rest.map cols) = false := by
    apply zeroParity
    intro col hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
    apply earlier
    have := sameWeight q hq
    have := increasing q hq
    omega
  simp [rowParity, diagonal, vanishes]

/-- Every pair across the indicated consecutive half-blocks lies on a sampled
band diagonal if the two halves together have length at most `r`. -/
theorem halfBlocksAreSampled {start b r i j : Nat}
    (width : 2 * b ≤ r) (rowLo : start ≤ i) (rowHi : i < start + b)
    (colLo : start + b ≤ j) (colHi : j < start + 2*b) :
    i < j ∧ j - i < r := by omega

end FoldedRankWitness
