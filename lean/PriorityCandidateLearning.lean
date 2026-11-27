import Std

namespace PriorityCandidateLearning

/-- The stage searches its active initial segment in increasing index order. -/
def choice (refuted : Nat → Nat → Bool) (active : Nat → Nat) (stage : Nat) : Option Nat :=
  (List.range (active stage)).find? (fun candidate => !refuted stage candidate)

/-- A finite initial segment of eventually permanent refutations is
    simultaneously refuted from some common stage onward. -/
theorem finite_cutoff (refuted : Nat → Nat → Bool) (g : Nat)
    (persistent : ∀ s t i, s ≤ t → refuted s i = true → refuted t i = true)
    (caught : ∀ i, i < g → ∃ s, refuted s i = true) :
    ∃ cutoff, ∀ t, cutoff ≤ t → ∀ i, i < g → refuted t i = true := by
  induction g with
  | zero => exact ⟨0, fun _ _ _ h => False.elim (Nat.not_lt_zero _ h)⟩
  | succ g ih =>
    obtain ⟨a, ha⟩ := ih (fun i hi => caught i (by omega))
    obtain ⟨b, hb⟩ := caught g (by omega)
    refine ⟨max a b, ?_⟩
    intro t h i hi
    by_cases eq : i = g
    · subst i; exact persistent b t g (by omega) hb
    · exact ha t (by omega) i (by omega)

/-- Once g is active forever, permanent soundness at g and eventual
    detection of every lower index force convergence to g. -/
theorem choice_stabilizes (refuted : Nat → Nat → Bool) (active : Nat → Nat) (g : Nat)
    (persistent : ∀ s t i, s ≤ t → refuted s i = true → refuted t i = true)
    (safe : ∀ t, refuted t g = false)
    (caught : ∀ i, i < g → ∃ s, refuted s i = true)
    (visible : ∃ a, ∀ t, a ≤ t → g < active t) :
    ∃ cutoff, ∀ t, cutoff ≤ t → choice refuted active t = some g := by
  obtain ⟨a, ha⟩ := visible
  obtain ⟨b, hb⟩ := finite_cutoff refuted g persistent caught
  refine ⟨max a b, ?_⟩
  intro t ht
  apply List.find?_range_eq_some.mpr
  refine ⟨by simp [safe], List.mem_range.mpr (ha t (by omega)), ?_⟩
  intro i hi
  simp [hb t (by omega) i hi]

/-- Each award may spoil one pair or none. The complete set of spoiled
    pairs admits a duplicate-free enumeration no longer than the award log.
    Multiple awards charging the same pair are allowed. -/
theorem spoiled_pairs {Award PairId : Type} [DecidableEq PairId]
    (charge : Award → Option PairId) (awards : List Award) :
    ∃ ids : List PairId, ids.Nodup ∧ ids.length ≤ awards.length ∧
      ∀ p, p ∈ ids ↔ ∃ a ∈ awards, charge a = some p := by
  induction awards with
  | nil => exact ⟨[], by simp, by simp, by simp⟩
  | cons a rest ih =>
    obtain ⟨ids, distinct, bound, member⟩ := ih
    cases eq : charge a with
    | none =>
      refine ⟨ids, distinct, by simp; omega, ?_⟩
      intro p
      simp [eq, member]
    | some x =>
      by_cases old : x ∈ ids
      · refine ⟨ids, distinct, by simp; omega, ?_⟩
        intro p
        simp only [List.mem_cons, exists_eq_or_imp, eq, Option.some.injEq, ← member]
        constructor
        · exact Or.inr
        · rintro (rfl | h)
          · exact old
          · exact h
      · refine ⟨x :: ids, List.nodup_cons.mpr ⟨old, distinct⟩, by simp; omega, ?_⟩
        intro p
        simp only [List.mem_cons, exists_eq_or_imp, eq, Option.some.injEq, ← member]
        rw [eq_comm (a := p) (b := x)]

end PriorityCandidateLearning
