import Std

namespace MinorityInstanceComplexity

/-- If fewer than cap earlier hits precede a new hit, that hit occurs among
    the first cap hits even after an arbitrary later suffix is appended. -/
theorem hit_in_first {α : Type} (earlier later : List α) (x : α) (cap : Nat)
    (h : earlier.length < cap) :
    x ∈ (earlier ++ x :: later).take cap := by
  induction earlier generalizing cap with
  | nil =>
    cases cap with
    | zero => simp at h
    | succ n => simp
  | cons a xs ih =>
    cases cap with
    | zero => simp at h
    | succ n =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      exact List.mem_cons_of_mem _ (ih n h)

/-- Even overlapping lists of the first cap predictions by each tester
    have total length at most the product of family size and cap. -/
theorem bounded_hits {α : Type} (histories : List (List α)) (cap : Nat) :
    ((histories.map (fun xs => xs.take cap)).flatten).length ≤ histories.length * cap := by
  induction histories with
  | nil => simp
  | cons xs rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_take,
      List.length_cons, Nat.succ_mul]
    have h := Nat.min_le_left cap xs.length
    omega

private theorem distinct_subset_length {α : Type} [DecidableEq α] (block hits : List α)
    (distinct : block.Nodup) (subset : block ⊆ hits) : block.length ≤ hits.length := by
  induction block generalizing hits with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, nodup⟩ := List.nodup_cons.mp distinct
    have inHits := subset (List.mem_cons_self (a := x) (l := xs))
    have tail : xs ⊆ hits.erase x := by
      intro y hy
      have ne : y ≠ x := fun eq => fresh (eq ▸ hy)
      exact (List.mem_erase_of_ne ne).mpr (subset (List.mem_cons_of_mem x hy))
    have bound := ih (hits.erase x) nodup tail
    have positive := List.length_pos_of_mem inHits
    rw [List.length_erase_of_mem inHits] at bound
    simp only [List.length_cons]
    omega

/-- If every block point is covered and block points are distinct, the
    arithmetic bound follows without requiring distinct hits across testers. -/
theorem cover_bound {α : Type} [DecidableEq α] (block : List α)
    (distinct : block.Nodup) (histories : List (List α)) (cap : Nat)
    (cover : ∀ x ∈ block, x ∈ (histories.map (fun xs => xs.take cap)).flatten) :
    block.length ≤ histories.length * cap := by
  exact Nat.le_trans (distinct_subset_length block _ distinct cover) (bounded_hits histories cap)

end MinorityInstanceComplexity
