import Std

namespace PinnedClauseRepairs

/-- A physical clause is split into its port and auxiliary literal occurrences. -/
structure Row (P A : Type) where
  ports : List (P × Bool)
  aux : List (A × Bool)

def litTrue {V : Type} (x : V → Bool) (lit : V × Bool) : Prop :=
  x lit.1 = lit.2

def hits {V : Type} (x : V → Bool) (lits : List (V × Bool)) : Prop :=
  ∃ l ∈ lits, litTrue x l

def accepts {I P A : Type} (H : I → Row P A) (x : P → Bool) : Prop :=
  ∃ z : A → Bool, ∀ i, hits x (H i).ports ∨ hits z (H i).aux

def repairs {I P A : Type} (H : I → Row P A) (u : P → Bool) : Prop :=
  ∀ i, ∃ z : A → Bool, ∀ j, j ≠ i → hits u (H j).ports ∨ hits z (H j).aux

/-- Eliminating any number of existential variables preserves only the
    disjunction of the port literals if all clauses admit a repair at one pin. -/
theorem projection {I P A : Type} (H : I → Row P A) (u : P → Bool)
    (bad : ¬ accepts H u) (rep : repairs H u) (v : P → Bool) :
    accepts H v ↔ ∃ i, hits v (H i).ports := by
  classical
  have dark : ∀ i, ¬ hits u (H i).ports := by
    intro i lit
    obtain ⟨z, rest⟩ := rep i
    apply bad
    refine ⟨z, fun j => ?_⟩
    by_cases same : j = i
    · exact Or.inl (same ▸ lit)
    · exact rest j same
  constructor
  · rintro ⟨z, works⟩
    apply Classical.byContradiction
    intro none
    apply bad
    refine ⟨z, fun j => Or.inr ?_⟩
    exact (works j).resolve_left (fun lit => none ⟨j, lit⟩)
  · rintro ⟨i, lit⟩
    obtain ⟨z, rest⟩ := rep i
    refine ⟨z, fun j => ?_⟩
    by_cases same : j = i
    · exact Or.inl (same ▸ lit)
    · exact Or.inr ((rest j same).resolve_left (dark j))

/-- No row can use the sign of a port that stays true at every proposed
    deletion witness if every one of those boundary tuples is rejected. -/
theorem frozen_polarity {I P A : Type} (H : I → Row P A)
    (centers : (P → Bool) → Prop) (port : P) (b : Bool)
    (fixedAt : ∀ x, centers x → x port = b)
    (reject : ∀ x, centers x → ¬ accepts H x)
    (covered : ∀ i, ∃ x, centers x ∧ ∃ z : A → Bool, ∀ j, j ≠ i →
      hits x (H j).ports ∨ hits z (H j).aux) :
    ∀ i, (port, b) ∉ (H i).ports := by
  intro i occurs
  obtain ⟨x, xc, z, rest⟩ := covered i
  apply reject x xc
  refine ⟨z, fun j => ?_⟩
  by_cases same : j = i
  · subst j
    exact Or.inl ⟨(port, b), occurs, fixedAt x xc⟩
  · exact rest j same

end PinnedClauseRepairs
