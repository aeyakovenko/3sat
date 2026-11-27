import Std

namespace SparseWindowLists

/-- A mask R already has 'inside' entries in the center and requires
'added' new ones. To stay light, only center entries outside R may be removed. -/
theorem minimum_edit (inside added outside cap : Nat)
    (fits : inside + added ≤ cap) :
    let removed := inside + outside + added - cap
    removed ≤ outside ∧
      inside + (outside - removed) + added ≤ cap ∧
      ∀ extra drop : Nat, drop ≤ outside →
        inside + (outside - drop) + added + extra ≤ cap →
        added + removed ≤ added + extra + drop := by
  dsimp
  refine ⟨by omega, by omega, ?_⟩
  intro extra drop hd hc
  omega

theorem radius_test (weight added cap radius : Nat) :
    added + (weight + added - cap) ≤ radius ↔
      added ≤ radius ∧ weight + 2 * added ≤ cap + radius := by
  omega

/-- Incidence counting for arbitrary, possibly overlapping candidate balls. -/
def covered {α β : Type} (rows : List α) (cols : List β)
    (hit : α → β → Bool) : Nat :=
  (rows.map (fun row => cols.countP (hit row))).sum

private theorem count_any {α β : Type} (rows : List α) (cols : List β)
    (hit : α → β → Bool) :
    cols.countP (fun col => rows.any (fun row => hit row col)) ≤ covered rows cols hit := by
  induction rows with
  | nil => simp [covered]
  | cons row rows ih =>
    have add : ∀ xs : List β,
        xs.countP (fun col => hit row col || rows.any (fun x => hit x col)) ≤
        xs.countP (hit row) + xs.countP (fun col => rows.any (fun x => hit x col)) := by
      intro xs
      induction xs with
      | nil => simp
      | cons col cs prev =>
        cases h : hit row col <;> cases k : rows.any (fun x => hit x col) <;>
          simp [List.countP_cons, h, k] at * <;> omega
    simp only [List.any_cons, covered, List.map_cons, List.sum_cons] at *
    exact Nat.le_trans (add cols) (Nat.add_le_add_left ih _)

theorem covered_length {α β : Type} (rows : List α) (cols : List β)
    (hit : α → β → Bool) (allHit : ∀ col ∈ cols, ∃ row ∈ rows, hit row col = true) :
    cols.length ≤ covered rows cols hit := by
  have eq : cols.countP (fun col => rows.any (fun row => hit row col)) = cols.length := by
    induction cols with
    | nil => simp
    | cons col cs ih =>
      obtain ⟨row, hr, h⟩ := allHit col (by simp)
      have here : rows.any (fun x => hit x col) = true := List.any_eq_true.mpr ⟨row, hr, h⟩
      have tail := ih (fun v hv => allHit v (by simp [hv]))
      simp [List.countP_cons, here, tail]
  rw [← eq]
  exact count_any rows cols hit

end SparseWindowLists
