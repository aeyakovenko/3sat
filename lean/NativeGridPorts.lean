import Std

/-! Finite connectivity ingredients for the native grid separator example.
The edge expansion of the core and the surface embedding are used in the manuscript. -/

namespace NativeGridPorts

/-- All intact rows and columns connect to the same chosen grid intersection.
    Reach is the ambient surviving-graph connectivity relation. -/
theorem connectedCross
    {R C : Type} (row : R → Prop) (col : C → Prop)
    (reach : R × C → R × C → Prop)
    (trans : ∀ {a b c}, reach a b → reach b c → reach a c)
    (alongRow : ∀ r, row r → ∀ i j, reach (r,i) (r,j))
    (alongCol : ∀ c, col c → ∀ i j, reach (i,c) (j,c))
    {r₀ : R} {c₀ : C} (hr : row r₀) (hc : col c₀)
    {r : R} {c : C} (onCross : row r ∨ col c) : reach (r,c) (r₀,c₀) := by
  rcases onCross with h | h
  · exact trans (alongRow r h c c₀) (alongCol c₀ hc r r₀)
  · exact trans (alongCol c h r r₀) (alongRow r₀ hr c c₀)

/-- A strand can fail at either port. Count the two excluded sets by a
    union bound, with no independence or ordering assumption. -/
theorem survivingStrand {α : Type} (ports : List α) (left right : α → Bool)
    (few : (ports.filter (fun x => !left x)).length +
      (ports.filter (fun x => !right x)).length < ports.length) :
    ∃ x ∈ ports, left x = true ∧ right x = true := by
  induction ports with
  | nil => simp at few
  | cons x xs ih =>
    cases hl : left x <;> cases hr : right x
    · have small : (xs.filter (fun a => !left a)).length +
          (xs.filter (fun a => !right a)).length < xs.length := by
        simp [List.filter, hl, hr] at few
        omega
      obtain ⟨y, hy, good⟩ := ih small
      exact ⟨y, List.mem_cons_of_mem _ hy, good⟩
    · have small : (xs.filter (fun a => !left a)).length +
          (xs.filter (fun a => !right a)).length < xs.length := by
        simpa [List.filter, hl, hr, Nat.succ_add] using few
      obtain ⟨y, hy, good⟩ := ih small
      exact ⟨y, List.mem_cons_of_mem _ hy, good⟩
    · have small : (xs.filter (fun a => !left a)).length +
          (xs.filter (fun a => !right a)).length < xs.length := by
        simp [List.filter, hl, hr] at few
        omega
      obtain ⟨y, hy, good⟩ := ih small
      exact ⟨y, List.mem_cons_of_mem _ hy, good⟩
    · exact ⟨x, List.mem_cons_self, hl, hr⟩

end NativeGridPorts
