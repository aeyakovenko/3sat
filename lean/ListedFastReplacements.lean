import Std

namespace ListedFastReplacements

private theorem coverLength (palette cover : List Nat) (unique : palette.Nodup)
    (covered : ∀ x ∈ palette, x ∈ cover) : palette.length ≤ cover.length := by
  induction palette generalizing cover with
  | nil => simp
  | cons x xs ih =>
    have h := List.nodup_cons.mp unique
    have hx : x ∈ cover := covered _ (by simp)
    have rest : ∀ y ∈ xs, y ∈ cover.erase x := by
      intro y hy
      have ne : y ≠ x := by
        intro eq
        exact h.1 (eq ▸ hy)
      exact (List.mem_erase_of_ne ne).mpr (covered _ (by simp [hy]))
    have shorter := ih _ h.2 rest
    rw [List.length_erase_of_mem hx] at shorter
    have pos : cover.length > 0 := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

/-- An arbitrary row blacklist and the preceding distinct assignments
    cannot cover a palette of size two times the number of rows. -/
theorem availableTag (palette forbidden used : List Nat) (rows : Nat)
    (unique : palette.Nodup) (capacity : palette.length = 2*rows)
    (rowLimit : forbidden.length ≤ rows) (unfinished : used.length < rows) :
    ∃ tag ∈ palette, tag ∉ forbidden ∧ tag ∉ used := by
  apply Classical.byContradiction
  intro fail
  have covered : ∀ tag ∈ palette, tag ∈ forbidden ++ used := by
    intro tag member
    by_cases first : tag ∈ forbidden
    · exact List.mem_append_left _ first
    · by_cases prior : tag ∈ used
      · exact List.mem_append_right _ prior
      · exact False.elim (fail ⟨tag, member, first, prior⟩)
  have size := coverLength _ _ unique covered
  rw [List.length_append, capacity] at size
  omega

/-- The extra literal tag digit is paid by a shorter header. -/
theorem pairedLength (context high low : Nat) :
    1 + context + high + (low+1) = 2 + context + high + low := by omega

end ListedFastReplacements
