import Std

namespace ResetEpisodePacking

private theorem capacity {α : Type} [DecidableEq α] {xs pool : List α}
    (distinct : xs.Nodup) (inside : ∀ a ∈ xs, a ∈ pool) : xs.length ≤ pool.length := by
  induction xs generalizing pool with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    have hit := inside x (by simp)
    have pos := List.length_pos_of_mem hit
    have rest := ih (pool := pool.erase x) tail (by
      intro a ha
      have ne : a ≠ x := fun eq => fresh (eq ▸ ha)
      exact (List.mem_erase_of_ne ne).mpr (inside a (by simp [ha])))
    rw [List.length_erase_of_mem hit] at rest
    simp
    omega

/-- All short opportunities over a list of reset seeds. The opportunity
    number is zero-based. Paths may revisit addresses or one another. -/
def prefixPool {S A : Type} (path : S → Nat → A) (d : Nat) : List S → List A
  | [] => []
  | s :: ss => (List.range d).map (path s) ++ prefixPool path d ss

private theorem poolLength {S A : Type} (path : S → Nat → A) (d : Nat) (ss : List S) :
    (prefixPool path d ss).length = ss.length*d := by
  induction ss with
  | nil => simp [prefixPool]
  | cons s ss ih => simp [prefixPool, ih, Nat.succ_mul, Nat.add_comm]

private theorem inPool {S A : Type} (path : S → Nat → A) {d i : Nat} (hi : i < d)
    {ss : List S} {s : S} (hs : s ∈ ss) : path s i ∈ prefixPool path d ss := by
  induction ss with
  | nil => simp at hs
  | cons t ts ih =>
    rcases List.mem_cons.mp hs with rfl | ht
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    · exact List.mem_append_right _ (ih ht)

/-- If each required endpoint is reached at the end of a disjoint episode,
    assign it that episode's zero-based last load index. All but at most
    |seeds|*d distinct endpoints pay at least d opportunities each. -/
theorem resetPacking {S A : Type} [DecidableEq A] (seeds : List S) (path : S → Nat → A)
    (targets : List A) (index : A → Nat) (d : Nat) (distinct : targets.Nodup)
    (reach : ∀ a ∈ targets, ∃ s ∈ seeds, path s (index a) = a) :
    (targets.length - seeds.length*d) * d ≤ (targets.map (fun a => index a + 1)).sum := by
  let short := fun a => decide (index a < d)
  have sub : ∀ a ∈ targets.filter short, a ∈ prefixPool path d seeds := by
    intro a ha
    obtain ⟨ht, hlt⟩ := List.mem_filter.mp ha
    obtain ⟨s, hs, eq⟩ := reach a ht
    exact eq ▸ inPool path (of_decide_eq_true hlt) hs
  have small := capacity (distinct.filter short) sub
  rw [poolLength] at small
  have cost : (targets.length - (targets.filter short).length)*d ≤
      (targets.map (fun a => index a+1)).sum := by
    clear sub small distinct reach
    induction targets with
    | nil => simp
    | cons a xs ih =>
      have len := List.length_filter_le short xs
      by_cases ha : index a < d
      · simp [List.filter_cons, short, ha] at ih ⊢
        omega
      · have hd : d ≤ index a+1 := by omega
        have step : xs.length+1-(xs.filter short).length = xs.length-(xs.filter short).length+1 := by omega
        simp only [List.length_cons, List.filter_cons, List.map_cons, List.sum_cons]
        have no : short a = false := by simp [short, ha]
        rw [no]
        simp only [Bool.false_eq_true, ↓reduceIte, step, Nat.succ_mul]
        omega
  exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le_sub_left small _)) cost

end ResetEpisodePacking
