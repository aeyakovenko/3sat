import Std

namespace SparseEventOrder

variable {α : Type} [DecidableEq α]

/-- At a mismatching position keep both complete rows, including their payloads. -/
def different (rows : List (α × α)) : List (α × α) :=
  rows.filter fun p => decide (p.1 ≠ p.2)

private theorem balanced_counts (rows : List (α × α)) (a : α) :
    (rows.map Prod.fst).count a + ((different rows).map Prod.snd).count a =
    (rows.map Prod.snd).count a + ((different rows).map Prod.fst).count a := by
  induction rows with
  | nil => simp [different]
  | cons p tail ih =>
    obtain ⟨x,y⟩ := p
    by_cases h : x = y
    · subst y
      simp only [different, List.filter_cons, ne_self_iff_false, decide_false,
        Bool.false_eq_true, ite_false, List.map_cons, List.count_cons] at *
      omega
    · have keep : decide (x ≠ y) = true := decide_eq_true h
      simp only [different, List.filter_cons, keep, ite_true, List.map_cons,
        List.count_cons] at *
      omega

/-- Cancelling all position-wise equal rows preserves the exact multiset test. -/
theorem perm_iff_different_perm (rows : List (α × α)) :
    (rows.map Prod.fst).Perm (rows.map Prod.snd) ↔
    ((different rows).map Prod.fst).Perm ((different rows).map Prod.snd) := by
  simp only [List.perm_iff_count]
  constructor <;> intro h a <;> have := balanced_counts rows a <;> specialize h a <;> omega

end SparseEventOrder
