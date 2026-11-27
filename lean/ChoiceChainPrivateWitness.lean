import Std

namespace ChoiceChainPrivateWitness

inductive LocalCoordinate
  | atom (choice : Nat)
  | threshold (cut : Nat)

def holds : LocalCoordinate → Nat → Prop
  | .atom i, a => a = i
  | .threshold r, a => r < a

def missingPair (f g : Nat → Prop) : Prop :=
  (∀ a, ¬ (f a ∧ g a)) ∨ (∀ a, f a → g a) ∨ (∀ a, g a → f a)

theorem local_omission (a b : LocalCoordinate) : missingPair (holds a) (holds b) := by
  cases a with
  | atom i =>
    cases b with
    | atom j =>
      by_cases h : i = j
      · subst j; exact Or.inr (Or.inl fun _ h => h)
      · exact Or.inl (by simp only [holds]; omega)
    | threshold s =>
      by_cases h : s < i
      · exact Or.inr (Or.inl (by simp only [holds]; omega))
      · exact Or.inl (by simp only [holds]; omega)
  | threshold r =>
    cases b with
    | atom j =>
      by_cases h : r < j
      · exact Or.inr (Or.inr (by simp only [holds]; omega))
      · exact Or.inl (by simp only [holds]; omega)
    | threshold s =>
      by_cases h : s ≤ r
      · exact Or.inr (Or.inl (by simp only [holds]; omega))
      · exact Or.inr (Or.inr (by simp only [holds]; omega))

inductive Variable
  | anchor
  | left (c : LocalCoordinate)
  | right (c : LocalCoordinate)

def witness (i j : Nat) : Variable → Prop
  | .anchor => False
  | .left c => holds c i
  | .right c => holds c j

def missesTriple (a b c : Variable) : Prop :=
  ∃ u v w : Prop, ∀ i j, ¬ ((witness i j a ↔ u) ∧
    (witness i j b ↔ v) ∧ (witness i j c ↔ w))

private theorem pair_pattern (a b : LocalCoordinate) :
    ∃ u v : Prop, ∀ i, ¬ ((holds a i ↔ u) ∧ (holds b i ↔ v)) := by
  rcases local_omission a b with h | h | h
  · exact ⟨True, True, fun i q => h i ⟨q.1.mpr trivial, q.2.mpr trivial⟩⟩
  · exact ⟨True, False, fun i q => q.2.mp (h i (q.1.mpr trivial))⟩
  · exact ⟨False, True, fun i q => q.1.mp (h i (q.2.mpr trivial))⟩

private theorem swap12 {a b c : Variable} (h : missesTriple a b c) : missesTriple b a c := by
  obtain ⟨u,v,w,h⟩ := h
  exact ⟨v,u,w,fun i j q => h i j ⟨q.2.1,q.1,q.2.2⟩⟩

private theorem swap23 {a b c : Variable} (h : missesTriple a b c) : missesTriple a c b := by
  obtain ⟨u,v,w,h⟩ := h
  exact ⟨u,w,v,fun i j q => h i j ⟨q.1,q.2.2,q.2.1⟩⟩

private theorem anchored (b c : Variable) : missesTriple .anchor b c :=
  ⟨True,True,True,fun _ _ q => q.1.mpr trivial⟩

private theorem left_pair (a b : LocalCoordinate) (c : Variable) :
    missesTriple (.left a) (.left b) c := by
  obtain ⟨u,v,h⟩ := pair_pattern a b
  exact ⟨u,v,True,fun i _ q => h i ⟨q.1,q.2.1⟩⟩

private theorem right_pair (a b : LocalCoordinate) (c : Variable) :
    missesTriple (.right a) (.right b) c := by
  obtain ⟨u,v,h⟩ := pair_pattern a b
  exact ⟨u,v,True,fun _ j q => h j ⟨q.1,q.2.1⟩⟩

theorem fill_every_triple (a b c : Variable) : missesTriple a b c := by
  cases a <;> cases b <;> cases c <;>
    first | apply anchored | apply left_pair | apply right_pair
          | exact swap12 (anchored _ _)
          | exact swap23 (swap12 (anchored _ _))
          | exact swap23 (left_pair _ _ _)
          | exact swap23 (right_pair _ _ _)
          | exact swap12 (swap23 (left_pair _ _ _))
          | exact swap12 (swap23 (right_pair _ _ _))

theorem chain_forces (p : Nat) (s a : Nat → Prop) (start : s 0) (stop : ¬s p)
    (step : ∀ i < p, s i → a i ∨ s (i+1)) : ∃ i < p, a i := by
  apply Classical.byContradiction
  intro h
  have pathHolds : ∀ i ≤ p, s i := by
    intro i hi
    induction i with
    | zero => exact start
    | succ i ih =>
      rcases step i (by omega) (ih (by omega)) with ha | hs
      · exact False.elim (h ⟨i, by omega, ha⟩)
      · exact hs
  exact stop (pathHolds p (by omega))

theorem threshold_path (chosen : Nat) (i : Nat) :
    i ≤ chosen → i = chosen ∨ i + 1 ≤ chosen := by omega

theorem only_selected_target (i j u v : Nat) :
    (witness i j (.left (.atom u)) ∧ witness i j (.right (.atom v)) ∧
      ¬witness i j .anchor) ↔ (u = i ∧ v = j) := by
  simp only [witness, holds, not_false_eq_true, and_true]
  omega

end ChoiceChainPrivateWitness
