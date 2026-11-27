import Std

namespace PrefixPrediction

/-- After eliminating dependent parity queries, each new answer splits an
    affine fiber of dimension n+1 into two fibers of dimension n. -/
inductive QueryTree (Label : Type) : Nat → Type where
  | stop {n : Nat} (label : Option Label) : QueryTree Label n
  | split {n : Nat} (left right : QueryTree Label n) : QueryTree Label (n + 1)

def votes {Label : Type} {n : Nat} (tree : QueryTree Label n) : List (Label × Nat) :=
  match tree with
  | @QueryTree.stop _ n (some label) => [(label, 2 ^ n)]
  | .stop none => []
  | .split left right => votes left ++ votes right

private theorem append_sum (xs ys : List Nat) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

theorem voteMass {Label : Type} {n : Nat} (tree : QueryTree Label n) :
    ((votes tree).map Prod.snd).sum ≤ 2 ^ n := by
  induction tree with
  | stop label => cases label <;> simp [votes]
  | @split n left right ihl ihr =>
    simp only [votes, List.map_append, append_sum, Nat.pow_succ]
    omega

theorem sum_ge_floor (bins : List Nat) (budget : Nat)
    (large : ∀ v ∈ bins, budget ≤ v) : bins.length * budget ≤ bins.sum := by
  induction bins with
  | nil => simp
  | cons v rest ih =>
    have head := large v (by simp)
    have tail := ih (fun u hu => large u (by simp [hu]))
    simp only [List.length_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem lightBin (bins : List Nat) (budget : Nat)
    (smallTotal : bins.sum < bins.length * budget) :
    ∃ v ∈ bins, v < budget := by
  apply Classical.byContradiction
  intro none
  have large : ∀ v ∈ bins, budget ≤ v := by
    intro v hv
    exact Nat.le_of_not_gt (fun h => none ⟨v, hv, h⟩)
  have bound := sum_ge_floor bins budget large
  omega

/-- With both probabilities scaled by 2^denom, the price of enforcing
    consistency of parity replies is 2^(tests-rank). -/
theorem consistencyRatio (denom tests rank : Nat)
    (rankBound : rank ≤ tests) (testBound : tests ≤ denom) :
    2 ^ (denom - rank) = 2 ^ (tests - rank) * 2 ^ (denom - tests) := by
  rw [← Nat.pow_add]
  congr 1
  omega

end PrefixPrediction
