import Std

namespace SuffixBlockExponents

/-- A low block contributes at most threshold accepted entries, and a
    high block at most size additional entries. -/
theorem totalByBlocks (counts : List Nat) (size threshold : Nat)
    (capacity : ∀ x ∈ counts, x ≤ size) :
    counts.sum ≤ counts.length * threshold +
      counts.countP (fun x => decide (threshold ≤ x)) * size := by
  induction counts with
  | nil => simp
  | cons x xs ih =>
    have hx := capacity x (by simp)
    have ht := ih (fun y hy => capacity y (by simp [hy]))
    by_cases h : threshold ≤ x <;>
      simp [List.countP_cons, h, Nat.succ_mul, Nat.add_mul] <;> omega

/-- If globally twice the local threshold is met on average, the high
    prefixes together carry at least one threshold times the prefix count
    when measured at the full block capacity. -/
theorem manyHighBlocks (counts : List Nat) (size threshold : Nat)
    (capacity : ∀ x ∈ counts, x ≤ size)
    (dense : 2*(counts.length*threshold) ≤ counts.sum) :
    counts.length*threshold ≤ counts.countP (fun x => decide (threshold ≤ x)) * size := by
  have h := totalByBlocks counts size threshold capacity
  omega

/-- Hits in all qualifying prefix blocks add, regardless of dependencies
    among their restricted circuits. -/
theorem hitsAdd {I : Type} (blocks : List I) (high : I → Bool) (hits : I → Nat)
    (quota : Nat) (good : ∀ z ∈ blocks, high z = true → quota ≤ hits z) :
    blocks.countP high * quota ≤ (blocks.map hits).sum := by
  induction blocks with
  | nil => simp
  | cons z zs ih =>
    have ht := ih (fun t hm => good t (by simp [hm]))
    cases hz : high z with
    | false => simp [List.countP_cons, hz]; omega
    | true =>
      have hh := good z (by simp) hz
      simpa [List.countP_cons, hz, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hh ht

end SuffixBlockExponents
