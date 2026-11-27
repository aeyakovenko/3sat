import Std

namespace MemoryLayout

/-- A graph walk from the anchor connects the public vertex labels. -/
inductive Reach (edge : Nat → Nat → Prop) (anchor : Nat) : Nat → Prop
  | start : Reach edge anchor anchor
  | step {x y} : Reach edge anchor x → edge x y → Reach edge anchor y

private theorem permOfCover (vertices labels : List Nat) (unique : vertices.Nodup)
    (covered : ∀ x ∈ vertices, x ∈ labels)
    (budget : labels.length ≤ vertices.length) : vertices.Perm labels := by
  induction vertices generalizing labels with
  | nil =>
    cases labels with
    | nil => exact .nil
    | cons _ _ => simp at budget
  | cons x xs ih =>
    have hu := List.nodup_cons.mp unique
    have hx : x ∈ labels := covered x (by simp)
    have tail : ∀ y ∈ xs, y ∈ labels.erase x := by
      intro y hy
      have ne : y ≠ x := fun eq => hu.1 (eq ▸ hy)
      exact (List.mem_erase_of_ne ne).mpr (covered y (by simp [hy]))
    have shorter : (labels.erase x).length ≤ xs.length := by
      rw [List.length_erase_of_mem hx]
      simp only [List.length_cons] at budget
      omega
    exact ((ih _ hu.2 tail shorter).cons x).trans (List.perm_cons_erase hx).symm

/-- If every occurrence accounts for all of its neighbors, a connected
    component and its introduction log of bounded length coincide exactly. -/
theorem portCoverage (edge : Nat → Nat → Prop) (vertices labels : List Nat)
    (anchor : Nat) (unique : vertices.Nodup)
    (connected : ∀ x ∈ vertices, Reach edge anchor x) (started : anchor ∈ labels)
    (closed : ∀ x ∈ labels, ∀ y, edge x y → y ∈ labels)
    (budget : labels.length ≤ vertices.length) : vertices.Perm labels := by
  apply permOfCover _ _ unique _ budget
  intro x hx
  have walk := connected x hx
  clear hx
  induction walk with
  | start => exact started
  | step _ edgeXY ih => exact closed _ ih _ edgeXY

/-- Index all visits to a single address in chronological order. At the
    (j+1)-st index, the reciprocal predecessor must be the j-th index. -/
theorem consecutiveVisit (k : Nat) (pred : Nat → Nat)
    (earlier : ∀ i < k, pred i ≤ i)
    (noFork : ∀ i < k, ∀ j < k, pred i = pred j → i = j) :
    ∀ i < k, pred i = i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro bound
    have low := earlier i bound
    apply Classical.byContradiction
    intro different
    have lt : pred i < i := by omega
    have pk : pred i < k := by omega
    have fixed := ih (pred i) lt pk
    have eq := noFork (pred i) pk i bound fixed
    exact different eq

/-- An identity matching and two shift matchings represent both local
    grid constraints. The equivalence works for arbitrary index maps. -/
theorem grid {I W : Type} (horizontal vertical : I → I)
    (sameSite : I → W → Prop) (h v : I → W → W → Prop) :
    (∃ l r : I → W, (∀ i, l i = r i ∧ sameSite i (l i)) ∧
      (∀ i, h i (l i) (r (horizontal i))) ∧ (∀ i, v i (l i) (r (vertical i)))) ↔
    ∃ t : I → W, (∀ i, sameSite i (t i)) ∧
      (∀ i, h i (t i) (t (horizontal i))) ∧ (∀ i, v i (t i) (t (vertical i))) := by
  constructor
  · rintro ⟨l, r, agree, H, V⟩
    exact ⟨l, fun i => (agree i).2,
      fun i => (agree (horizontal i)).1 ▸ H i,
      fun i => (agree (vertical i)).1 ▸ V i⟩
  · rintro ⟨t, localOK, H, V⟩
    exact ⟨t, t, fun i => ⟨rfl, localOK i⟩, H, V⟩

end MemoryLayout
