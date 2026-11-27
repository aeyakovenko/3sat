import Std

namespace PositiveOutputWatchdog

/-- A completed assignment must fail the chosen clause.
The directory index is the candidate number, independent of its contents. -/
def survives (k : Nat) (valid : Nat → Nat → Prop) (clauses : Nat)
    (challenge : Nat → Nat) : Prop :=
  ∀ i, i < k → challenge i < clauses ∧ ¬ valid i (challenge i)

theorem existsDirectory_iff (k clauses : Nat) (valid : Nat → Nat → Prop) :
    (∃ d, survives k valid clauses d) ↔
      ¬ ∃ i, i < k ∧ ∀ j, j < clauses → valid i j := by
  classical
  constructor
  · rintro ⟨d, hd⟩ ⟨i, hi, all⟩
    exact (hd i hi).2 (all _ (hd i hi).1)
  · intro noneValid
    have h : ∀ i, i < k → ∃ j, j < clauses ∧ ¬ valid i j := by
      intro i hi
      apply Classical.byContradiction
      intro noneBad
      apply noneValid
      refine ⟨i, hi, ?_⟩
      intro j hj
      exact Classical.byContradiction (fun hbad => noneBad ⟨j, hj, hbad⟩)
    let d := fun i => if hi : i < k then Classical.choose (h i hi) else 0
    refine ⟨d, ?_⟩
    intro i hi
    simpa [d, hi] using Classical.choose_spec (h i hi)

/-- The charge is for all *complete* candidates, including one whose
last bit falls exactly on the budget boundary. -/
theorem candidateVolume {bits variables horizon stepWidth : Nat}
    (covers : horizon ≤ variables) (written : bits ≤ stepWidth) :
    (bits / variables) * horizon ≤ stepWidth :=
  Nat.le_trans (Nat.mul_le_mul_left (bits / variables) covers)
    (Nat.le_trans (Nat.div_mul_le_self bits variables) written)

/-- Integer budget accounting before the next instruction. -/
def prefixCost (cost : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t+1 => prefixCost cost t + cost t

theorem prefixAffordable (cost : Nat → Nat) (i e budget : Nat)
    (early : i ≤ e) (cap : prefixCost cost e ≤ budget) :
    prefixCost cost i ≤ budget := by
  induction e with
  | zero => simpa [Nat.le_zero.mp early] using cap
  | succ e ih =>
    by_cases h : i = e+1
    · simpa [h] using cap
    · exact ih (by omega) (by simp only [prefixCost] at cap; omega)

/-- The chain clauses are numbered from zero to v. -/
def chainOK (v k j : Nat) : Prop :=
  if j = 0 then 0 < k
  else if j = v then k < v
  else j - 1 ≥ k ∨ j < k

theorem uniqueBadClause (v k j : Nat) (hk : k ≤ v) (hj : j ≤ v) :
    ¬ chainOK v k j ↔ j = k := by
  unfold chainOK
  split <;> rename_i h
  · omega
  · split <;> omega

end PositiveOutputWatchdog
