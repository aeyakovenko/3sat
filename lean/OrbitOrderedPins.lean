import Std

namespace OrbitOrderedPins

/-- Cutting an orbit prefix immediately after its kth marked word realizes
    every marked count through the total count. -/
theorem cut_before_remainder (marked : α → Bool) (orbit : List α) (k : Nat)
    (enough : k ≤ (orbit.filter marked).length) :
    ∃ left right, orbit = left ++ right ∧ (left.filter marked).length = k := by
  induction orbit generalizing k with
  | nil =>
    have : k = 0 := by simpa using enough
    exact ⟨[], [], rfl, this.symm⟩
  | cons a rest ih =>
    cases k with
    | zero => exact ⟨[], a :: rest, rfl, rfl⟩
    | succ k =>
      cases value : marked a with
      | false =>
        have rem : k+1 ≤ (rest.filter marked).length := by simpa [value] using enough
        obtain ⟨left, right, split, card⟩ := ih (k+1) rem
        exact ⟨a :: left, right, by simp [split], by simp [value, card]⟩
      | true =>
        have rem : k ≤ (rest.filter marked).length := by simpa [value] using enough
        obtain ⟨left, right, split, card⟩ := ih k rem
        exact ⟨a :: left, right, by simp [split], by simp [value, card]⟩

/-- A cut in orbit order yields a physical partition with disjoint owners.
    The public list of variable-name pairs covers exactly the marked slots
    on each side, in that side's order. -/
theorem balanced_pairing (marked : α → Bool) (orbit : List α) (k : Nat)
    (unique : orbit.Nodup) (total : (orbit.filter marked).length = 2*k) :
    ∃ (left right : List α) (pairs : List (α × α)),
      orbit = left ++ right ∧ (∀ a ∈ left, a ∉ right) ∧ pairs.length = k ∧
      pairs.map Prod.fst = left.filter marked ∧ pairs.map Prod.snd = right.filter marked := by
  obtain ⟨left, right, split, lcard⟩ := cut_before_remainder marked orbit k (by omega)
  rw [split, List.filter_append, List.length_append] at total
  have rcard : (right.filter marked).length = k := by omega
  have disjoint : ∀ a ∈ left, a ∉ right := by
    rw [split] at unique
    have sep := (List.pairwise_append.mp unique).2.2
    exact fun a ha hb => sep a ha a hb rfl
  refine ⟨left, right, (left.filter marked).zip (right.filter marked), split, disjoint,
    ?_, List.map_fst_zip (by omega), List.map_snd_zip (by omega)⟩
  simp [lcard, rcard]

/-- With two public dummy literals pinned false, each private 3-clause pins
    one variable. The paired clauses are jointly satisfiable exactly on the diagonal. -/
theorem paired_clauses (u v : Fin k → Bool) :
    (∃ assignment : Fin k → Bool, ∀ i,
      ((assignment i = u i ∨ False ∨ False) ∧ (assignment i = v i ∨ False ∨ False))) ↔
    u = v := by
  simp only [or_false]
  constructor
  · rintro ⟨assignment, h⟩
    exact funext fun i => (h i).1.symm.trans (h i).2
  · rintro rfl
    exact ⟨u, fun _ => ⟨rfl, rfl⟩⟩

end OrbitOrderedPins
