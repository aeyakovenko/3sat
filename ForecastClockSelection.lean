import Std

/-! Finite stabilization of the least unrefuted clocked solver and the
    Boolean logic at a forecast observation. The resource estimates and
    native simulation are separate manuscript arguments. -/
namespace ForecastClockSelection

/-- Every incorrect member of a finite initial segment has been exposed
at every sufficiently late stage. No effective stabilization time is given. -/
theorem finite_refutation_tail (Good : Nat → Prop) (seen : Nat → Nat → Prop)
    (complete : ∀ i, ¬Good i → ∃ t, ∀ n ≥ t, seen n i) (j : Nat) :
    ∃ t, ∀ n ≥ t, ∀ i < j, ¬Good i → seen n i := by
  classical
  induction j with
  | zero => exact ⟨0, by omega⟩
  | succ j ih =>
    obtain ⟨t, ht⟩ := ih
    by_cases good : Good j
    · refine ⟨t, ?_⟩
      intro n hn i hi bad
      by_cases same : i = j
      · subst i
        exact False.elim (bad good)
      · exact ht n hn i (by omega) bad
    · obtain ⟨u, hu⟩ := complete j good
      refine ⟨max t u, ?_⟩
      intro n hn i hi bad
      by_cases less : i < j
      · exact ht n (by omega) i less bad
      · have same : i = j := by omega
        subst i
        exact hu n (by omega)

/-- The unrefuted total program first in enumeration order eventually
equals the first actually correct one, on every later input length. -/
theorem selection_stabilizes (Good : Nat → Prop) (seen : Nat → Nat → Prop)
    (sound : ∀ n i, seen n i → ¬Good i)
    (complete : ∀ i, ¬Good i → ∃ t, ∀ n ≥ t, seen n i)
    (first : Nat) (honest : Good first) (prior : ∀ i < first, ¬Good i)
    (pick : Nat → Nat) (unseen : ∀ n, ¬seen n (pick n))
    (least : ∀ n i, ¬seen n i → pick n ≤ i) :
    ∃ t, ∀ n ≥ t, pick n = first := by
  obtain ⟨t, cleared⟩ := finite_refutation_tail Good seen complete first
  refine ⟨t, ?_⟩
  intro n hn
  have le := least n first (fun h => sound n first h honest)
  by_cases same : pick n = first
  · exact same
  · have lt : pick n < first := by omega
    exact False.elim (unseen n (cleared n hn (pick n) lt (prior (pick n) lt)))

/-- If bounded acceptance of a guessed description is answered exactly
within the latch budget, soundness rules out every timely witness, even
when no deterministic generator for the description is supplied. -/
theorem no_short_acceptance {α : Type} (forecast : Bool)
    (early : Bool) (valid timely : α → Prop)
    (latch : forecast = early)
    (accurate : early = true ↔ ∃ p, valid p ∧ timely p)
    (certifies : ∀ p, valid p → forecast = false) :
    forecast = false ∧ ∀ p, valid p → ¬ timely p := by
  have absent : ¬ ∃ p, valid p ∧ timely p := by
    rintro ⟨p, hp, fast⟩
    have yes := accurate.mpr ⟨p, hp, fast⟩
    have no := certifies p hp
    rw [latch, yes] at no
    cases no
  constructor
  · cases early with
    | false => exact latch
    | true => exact False.elim (absent (accurate.mp rfl))
  · exact fun p hv ht => absent ⟨p, hv, ht⟩

end ForecastClockSelection
