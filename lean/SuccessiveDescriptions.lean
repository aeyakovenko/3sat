import Std

namespace SuccessiveDescriptions

/-- Each batch is large enough to pass its surviving quota to the next stage. -/
theorem quotasPersist (size quota lost : Nat → Nat) (initial : quota 0 ≤ size 0)
    (selected : ∀ i, quota i ≤ size i → quota i ≤ size (i+1) + lost i)
    (budget : ∀ i, quota (i+1) + lost i ≤ quota i) : ∀ i, quota i ≤ size i := by
  intro i
  induction i with
  | zero => exact initial
  | succ i ih =>
    have next := selected i ih
    have cap := budget i
    omega

/-- Independently observable, strictly separated length bands certify a
    strict decrease even though the particular witnessing names can vary. -/
theorem adjacentDecrease (previous current lower upper : Nat)
    (earlier : lower ≤ previous) (later : current < upper)
    (separate : upper ≤ lower) : current < previous := by omega

/-- A measurement falling in either of the adjoining bands recovers its bit. -/
theorem bitRecovered (v boundary upper : Nat) (bit : Bool)
    (measurement : if bit then v < boundary else boundary ≤ v ∧ v < upper) :
    decide (v < boundary) = bit := by
  cases bit <;> simp_all

/-- Disjoint prefix groups that each lose at least one common quota pay that
    many distinct bad words into the global count. -/
theorem losingPrefixes (losses : List Nat) (quota : Nat)
    (large : ∀ n ∈ losses, quota ≤ n) : losses.length * quota ≤ losses.sum := by
  induction losses with
  | nil => simp
  | cons x xs ih =>
    have first := large x (by simp)
    have rest := ih (fun n hn => large n (by simp [hn]))
    simp only [List.length_cons, List.sum_cons, Nat.succ_mul]
    omega

/-- After deducting the header, a transition spends one rank bit plus the
    excess measured by its failed threshold test. -/
theorem rankCharge (cutoff nextCut header nextHeader excess : Int)
    (transition : nextCut = cutoff - 1 - header + nextHeader - excess) :
    nextCut - nextHeader = (cutoff - header) - 1 - excess := by omega

/-- A uniform bound on the charged excess keeps rank bits available over
    a linear number of transitions, even when header lengths change. -/
theorem rankRemaining (rank : Nat → Int) (allowance : Int)
    (step : ∀ j, rank j - allowance ≤ rank (j+1)) (j : Nat) :
    rank 0 - (j : Int) * allowance ≤ rank j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have next := step j
    rw [Int.natCast_succ, Int.add_mul, Int.one_mul]
    omega

end SuccessiveDescriptions
