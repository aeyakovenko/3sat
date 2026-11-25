import Std

namespace UnshiftedFunctionalScan

variable {α : Type} [DecidableEq α]

/-- A completed scan step reads M[p] and writes p at that address. -/
def step (M : α → α) (p a : α) : α :=
  if a = M p then p else M a

def run (M : α → α) : List α → (α → α)
  | [] => M
  | p :: rest => run (step M p) rest

/-- An edge of the underlying undirected support, including self-loops. -/
def Edge (M : α → α) (a b : α) : Prop := M a = b ∨ M b = a

def InImage (M : α → α) (a : α) : Prop := ∃ x, M x = a

omit [DecidableEq α] in
theorem edge_symm {M : α → α} {a b : α} (h : Edge M a b) : Edge M b a :=
  h.symm

/-- Even when the new arrow differs from the old value at its source, it
    reverses the edge just followed by the LOAD. -/
theorem step_arrow_in_old_support (M : α → α) (p a : α) :
    Edge M a (step M p a) := by
  by_cases h : a = M p
  · exact Or.inr (by simpa only [step, if_pos h] using h.symm)
  · exact Or.inl (by simp [step, h])

theorem step_support_subset (M : α → α) (p : α) {a b : α}
    (h : Edge (step M p) a b) : Edge M a b := by
  rcases h with hab | hba
  · simpa only [hab] using step_arrow_in_old_support M p a
  · exact edge_symm (by simpa only [hba] using step_arrow_in_old_support M p b)

theorem run_support_subset (M : α → α) (ps : List α) {a b : α}
    (h : Edge (run M ps) a b) : Edge M a b := by
  induction ps generalizing M with
  | nil => exact h
  | cons p rest ih => exact step_support_subset M p (ih (step M p) h)

theorem run_append (M : α → α) (ps qs : List α) :
    run M (ps ++ qs) = run (run M ps) qs := by
  induction ps generalizing M with
  | nil => rfl
  | cons p rest ih => exact ih (step M p)

theorem later_support_subset (M : α → α) (ps qs : List α) {a b : α}
    (h : Edge (run M (ps ++ qs)) a b) : Edge (run M ps) a b := by
  rw [run_append] at h
  exact run_support_subset _ qs h

omit [DecidableEq α] in
theorem only_initial_neighbor {M : α → α} {a b : α}
    (outside : ¬ InImage M a) (h : Edge M a b) : M a = b := by
  rcases h with hab | hba
  · exact hab
  · exact False.elim (outside ⟨b, hba⟩)

/-- Regardless of the scan schedule or its duration, an address outside the
    original value image always contains its original word. -/
theorem value_outside_initial_image (M : α → α) (ps : List α) {a : α}
    (outside : ¬ InImage M a) : run M ps a = M a := by
  have e : Edge (run M ps) a (run M ps a) := Or.inl rfl
  exact (only_initial_neighbor outside (run_support_subset M ps e)).symm

theorem support_at_outside (M : α → α) (ps : List α) {a b : α}
    (outside : ¬ InImage M a) : Edge (run M ps) a b ↔ Edge M a b := by
  refine ⟨run_support_subset M ps, ?_⟩
  intro h
  exact Or.inl ((value_outside_initial_image M ps outside).trans
    (only_initial_neighbor outside h))

/-- An edge observed at one prefix and absent at a later prefix must have
    both endpoints in the value image of the original memory. -/
theorem erased_endpoints (M : α → α) (ps qs : List α) {a b : α}
    (present : Edge (run M ps) a b) (absent : ¬ Edge (run M (ps ++ qs)) a b) :
    InImage M a ∧ InImage M b := by
  classical
  have old := run_support_subset M ps present
  constructor
  · apply Classical.byContradiction
    intro outside
    exact absent ((support_at_outside M (ps ++ qs) outside).mpr old)
  · apply Classical.byContradiction
    intro outside
    exact absent (edge_symm ((support_at_outside M (ps ++ qs) outside).mpr
      (edge_symm old)))

end UnshiftedFunctionalScan
