import Std

namespace SparseEditTestSuites

/-- The selected block is compared internally. All other values are
    compared individually against center, with a fixed address schedule. -/
def oneBlock (s : ι → Prop) (v : ι → α) (center : α) : Prop :=
  (∃ t, ∀ i, s i → v i = t) ∧ (∀ i, ¬ s i → v i = center)

theorem one_block_errors (s : ι → Prop) [DecidablePred s] (v : ι → α) (center : α)
    (used : ∃ i, s i) :
    (oneBlock s v center ∧ ¬ (∀ i, v i = center)) ↔
    ∃ t, t ≠ center ∧ ∀ i, v i = if s i then t else center := by
  constructor
  · rintro ⟨⟨⟨t, inside⟩, outside⟩, error⟩
    refine ⟨t, ?_, ?_⟩
    · intro eq
      apply error
      intro i
      by_cases si : s i
      · exact (inside i si).trans eq
      · exact outside i si
    · intro i
      by_cases si : s i
      · simpa [si] using inside i si
      · simpa [si] using outside i si
  · rintro ⟨t, ne, rows⟩
    refine ⟨⟨⟨t, ?_⟩, ?_⟩, ?_⟩
    · intro i si
      simpa [si] using rows i
    · intro i si
      simpa [si] using rows i
    · intro all
      obtain ⟨i, si⟩ := used
      have atI : v i = t := by simpa [si] using rows i
      exact ne (atI.symm.trans (all i))

theorem clock (m q : Nat) (h : q ≤ m) :
    m + (m - q) = 2*m - q := by omega

/-- A disjoint-block machine only needs a center entry in every long block.
    On a sparse input every block larger than the promise cap has one. -/
theorem long_blocks_are_central {β : Type} (blocks : β → ι → Prop)
    (v : ι → α) (center : α)
    (homogeneous : ∀ b, ∃ val, ∀ i, blocks b i → v i = val)
    (oneCenter : ∀ b, ∃ i, blocks b i ∧ v i = center) :
    ∀ b i, blocks b i → v i = center := by
  intro b i member
  obtain ⟨val, equal⟩ := homogeneous b
  obtain ⟨j, part, pinned⟩ := oneCenter b
  exact (equal i member).trans ((equal j part).symm.trans pinned)

def counts : List (Nat × Nat) → Nat × Nat
  | [] => (0, 0)
  | p :: rest => (p.1 + (counts rest).1, p.2 + (counts rest).2)

private theorem all_blocked (vs : List (Nat × Nat))
    (bad : ∀ p ∈ vs, 0 < p.1 ∨ 2 ≤ p.2) :
    2 * vs.length ≤ 2 * (counts vs).1 + (counts vs).2 := by
  induction vs with
  | nil => decide
  | cons p tail ih =>
    have hp := bad p (by simp)
    have ht := ih (fun q h => bad q (by simp [h]))
    simp only [counts, List.length_cons]
    omega

/-- The first entry counts directed prohibitions, the second incidence to
    edges which prescribe a deviation. Some component can carry a single
    freely signed magnitude. -/
theorem eligible_component (vs : List (Nat × Nat)) (d h : Nat)
    (vertices : d + h + 1 ≤ vs.length)
    (directed : (counts vs).1 ≤ d) (constrained : (counts vs).2 ≤ 2*h) :
    ∃ p ∈ vs, p.1 = 0 ∧ p.2 ≤ 1 := by
  apply Classical.byContradiction
  intro no
  have all : ∀ p ∈ vs, 0 < p.1 ∨ 2 ≤ p.2 := by
    intro p hp
    by_cases h1 : p.1 = 0
    · right
      apply Classical.byContradiction
      intro h2
      exact no ⟨p, hp, h1, by omega⟩
    · left
      omega
  have bound := all_blocked vs all
  omega

end SparseEditTestSuites
