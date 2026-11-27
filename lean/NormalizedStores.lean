import Std

namespace NormalizedStores

private theorem coarsePaid (stores : List Nat) (block : Nat) :
    (stores.map (fun s => s / block)).sum * block ≤ stores.sum := by
  induction stores with
  | nil => simp
  | cons s rest ih =>
    simpa [Nat.add_mul] using Nat.add_le_add (Nat.div_mul_le_self s block) ih

/-- Every high-counter change pays for one disjoint block of stores to its
    own logical key. Different logical keys may have different remainders. -/
theorem coarseBudget (stores : List Nat) (block : Nat) (positive : 0 < block) :
    (stores.map (fun s => s / block)).sum ≤ stores.sum / block :=
  (Nat.le_div_iff_mul_le positive).mpr (coarsePaid stores block)

/-- If each high increment introduces one 1-bit, the total number of drops
    is the increments minus the final total Hamming weight (initially zero). -/
theorem dropsFromBalance (increments drops finalWeight : Nat)
    (balance : increments = drops + finalWeight) :
    drops = increments - finalWeight ∧ drops ≤ increments := by omega

/-- The tree represents the intervals on which successive adaptive reads
    see a constant reply. There are at most b+1 pieces on any one probe. -/
inductive ProbePartitions (b : Nat) : Nat → Nat → Prop where
  | leaf : ProbePartitions b 0 1
  | node {depth : Nat} (pieces : List Nat) (fanout : pieces.length ≤ b+1)
      (children : ∀ p ∈ pieces, ProbePartitions b depth p) :
      ProbePartitions b (depth+1) pieces.sum

private theorem sumAtMost (pieces : List Nat) (bound : Nat)
    (each : ∀ p ∈ pieces, p ≤ bound) : pieces.sum ≤ pieces.length * bound := by
  induction pieces with
  | nil => simp
  | cons p rest ih =>
    have first := each p (by simp)
    have tail := ih (fun v hv => each v (by simp [hv]))
    simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add first tail

/-- This counts chronological pieces, including two disjoint periods that
    happen to return the same value. The actual decoder can have fewer runs. -/
theorem snapshotProbeBound {b depth pieces : Nat}
    (history : ProbePartitions b depth pieces) : pieces ≤ (b+1)^depth := by
  induction depth generalizing pieces with
  | zero => cases history; simp
  | succ d ih =>
    cases history with
    | node sizes fanout children =>
      have counted := sumAtMost sizes ((b+1)^d) (fun p hp => ih (children p hp))
      have scaled := Nat.mul_le_mul_right ((b+1)^d) fanout
      simpa [Nat.pow_succ, Nat.mul_comm] using Nat.le_trans counted scaled

end NormalizedStores
