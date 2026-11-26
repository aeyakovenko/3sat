import Std

/-! The two-literal implication chain comparing independently named records. -/

namespace TransposeEqualityTwoCNF

variable {α : Type}

/-- `p i` and `x i v` are distinct propositional variables. -/
def Clauses (m : Nat) (a b : Nat → α)
    (p : Nat → Prop) (x : Nat → α → Prop) : Prop :=
  p 0 ∧ ¬p m ∧ ∀ i < m,
    (¬p i ∨ x i (a i)) ∧ (¬x i (b i) ∨ p (i + 1))

theorem path_of_agreement {m : Nat} {a b : Nat → α}
    {p : Nat → Prop} {x : Nat → α → Prop} (h : Clauses m a b p x)
    (agree : ∀ i < m, a i = b i) : ∀ j ≤ m, p j := by
  intro j
  induction j with
  | zero => exact fun _ => h.1
  | succ j ih =>
    intro bound
    have before : j < m := by omega
    have step := h.2.2 j before
    have atLeft : x j (a j) := step.1.resolve_left (fun dead => dead (ih (by omega)))
    rw [agree j before] at atLeft
    exact step.2.resolve_left (fun dead => dead atLeft)

theorem satisfying_cut {m j : Nat} {a b : Nat → α} (hj : j < m) (different : a j ≠ b j) :
    Clauses m a b (fun i => i ≤ j) (fun i v => i ≤ j ∧ v = a i) := by
  refine ⟨Nat.zero_le _, by omega, ?_⟩
  intro i _
  constructor
  · by_cases before : i ≤ j
    · exact Or.inr ⟨before, rfl⟩
    · exact Or.inl before
  · by_cases before : i < j
    · exact Or.inr (by omega)
    · left
      rintro ⟨ile, equal⟩
      have atCut : i = j := by omega
      subst i
      exact different equal.symm

theorem satisfiable_iff_mismatch (m : Nat) (a b : Nat → α) :
    (∃ p x, Clauses m a b p x) ↔ ∃ j < m, a j ≠ b j := by
  constructor
  · rintro ⟨p, x, h⟩
    classical
    apply Classical.byContradiction
    intro none
    have agree : ∀ i < m, a i = b i := by
      intro i hi
      apply Classical.byContradiction
      intro diff
      exact none ⟨i, hi, diff⟩
    exact h.2.1 (path_of_agreement h agree m (Nat.le_refl m))
  · rintro ⟨j, hj, different⟩
    exact ⟨_, _, satisfying_cut hj different⟩

theorem unsatisfiable_iff_equal (m : Nat) (a b : Nat → α) :
    (¬∃ p x, Clauses m a b p x) ↔ ∀ j < m, a j = b j := by
  rw [satisfiable_iff_mismatch]
  classical
  constructor
  · intro none j hj
    apply Classical.byContradiction
    intro diff
    exact none ⟨j, hj, diff⟩
  · rintro agree ⟨j, hj, diff⟩
    exact diff (agree j hj)

/-- A pair of proper binary clauses fixes its first literal for every anchor setting. -/
theorem split_pin (literal anchor : Prop) :
    ((literal ∨ anchor) ∧ (literal ∨ ¬anchor)) ↔ literal := by
  constructor
  · rintro ⟨leftClause, rightClause⟩
    rcases leftClause with yes | active
    · exact yes
    · exact rightClause.resolve_right (fun inactive => inactive active)
  · exact fun yes => ⟨Or.inl yes, Or.inl yes⟩

/-- For a sum of translates of the punctured cube, a missing shift
forces any constant output to be zero. The weight of each shift is its
aggregate coefficient in the finite sum. Clearing a common denominator covers
rational weights as well. -/
theorem punctured_cube_missing_shift {ι : Type} (indices : List ι)
    (weight : ι → Int) (out : Int) (miss : ι) (hmiss : weight miss = 0)
    (constant : ∀ a, (indices.map weight).sum - weight a = out) : out = 0 := by
  have total : (indices.map weight).sum = out := by simpa [hmiss] using constant miss
  have vanish (a : ι) : weight a = 0 := by
    have eq := constant a
    rw [total] at eq
    omega
  have zero_sum (l : List ι) : (l.map weight).sum = 0 := by
    induction l with
    | nil => rfl
    | cons a tl ih => simp [vanish a, ih]
  exact total.symm.trans (zero_sum indices)

end TransposeEqualityTwoCNF
