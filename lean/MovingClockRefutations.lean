import Std

/-! A refutation reported later can eliminate the clock selected at a good
length. The good lengths may be arbitrarily far apart. -/

namespace MovingClockRefutations

abbrev Cofinal (good : Nat → Prop) : Prop :=
  ∀ lower, ∃ h, lower ≤ h ∧ good h

/-- At stage h, choose the first index whose refutation has not been reported. -/
structure Selector (refuted : Nat → Nat → Prop) (pick : Nat → Nat) : Prop where
  persists : ∀ h s i, h ≤ s → refuted h i → refuted s i
  openAt : ∀ h, ¬refuted h (pick h)
  earlier : ∀ h i, i < pick h → refuted h i

/-- Reporting the old choice permanently moves the selection beyond it. -/
theorem past_refuted_choice {refuted : Nat → Nat → Prop} {pick : Nat → Nat}
    (sel : Selector refuted pick) {h s : Nat} (later : h ≤ s)
    (report : refuted s (pick h)) : pick h < pick s := by
  by_cases below : pick s < pick h
  · exact False.elim (sel.openAt s
      (sel.persists h s (pick s) later (sel.earlier h (pick s) below)))
  · by_cases same : pick s = pick h
    · exact False.elim (sel.openAt s (same ▸ report))
    · omega

/-- Only sufficiently large good lengths must eventually refute their
current choice. Every finite initial segment then stays refuted at all
sufficiently late stages, including stages outside the good lengths. -/
theorem finite_segments_eventually_refuted {refuted : Nat → Nat → Prop}
    {pick : Nat → Nat} {good : Nat → Prop} (sel : Selector refuted pick)
    (unbounded : Cofinal good) (cutoff : Nat)
    (defeat : ∀ h, cutoff ≤ h → good h → ∃ s, h ≤ s ∧ refuted s (pick h)) :
    ∀ k, ∃ stage, ∀ t ≥ stage, ∀ i < k, refuted t i := by
  intro k
  induction k with
  | zero => exact ⟨0, by omega⟩
  | succ k ih =>
    obtain ⟨old, done⟩ := ih
    obtain ⟨h, hh, hg⟩ := unbounded (max old cutoff)
    obtain ⟨s, hs, report⟩ := defeat h (by omega) hg
    have reached : k ≤ pick h := by
      apply Nat.le_of_not_gt
      intro gap
      exact sel.openAt h (done h (by omega) (pick h) gap)
    have inc := past_refuted_choice sel hs report
    refine ⟨s, ?_⟩
    intro t ht i hi
    exact sel.persists s t i ht (sel.earlier s i (by omega))

theorem selections_eventually_escape {refuted : Nat → Nat → Prop}
    {pick : Nat → Nat} (sel : Selector refuted pick)
    (cleared : ∀ k, ∃ stage, ∀ t ≥ stage, ∀ i < k, refuted t i) :
    ∀ k, ∃ stage, ∀ t ≥ stage, k ≤ pick t := by
  intro k
  obtain ⟨s, hs⟩ := cleared k
  refine ⟨s, ?_⟩
  intro t ht
  apply Nat.le_of_not_gt
  intro below
  exact sel.openAt t (hs t ht (pick t) below)

/-- In particular, one arithmetic progression with a positive step suffices. -/
theorem cofinal_progression {good : Nat → Prop} (offset step : Nat) (positive : 0 < step)
    (onProgression : ∀ j, good (offset + step * j)) : Cofinal good := by
  intro lower
  refine ⟨offset + step * lower, ?_, onProgression lower⟩
  have enough : lower ≤ step * lower := by
    calc
      lower = 1 * lower := (Nat.one_mul lower).symm
      _ ≤ step * lower := Nat.mul_le_mul_right lower positive
  omega

/-- An actual reported discrepancy for every refutation gives an input
disagreeing with each individual clock. -/
theorem every_clock_fails {Input Answer : Type} {refuted : Nat → Nat → Prop}
    (verdict : Input → Answer) (clock : Nat → Input → Answer)
    (sound : ∀ s i, refuted s i → ∃ x, clock i x ≠ verdict x)
    (cleared : ∀ k, ∃ stage, ∀ t ≥ stage, ∀ i < k, refuted t i) :
    ∀ i, ∃ x, clock i x ≠ verdict x := by
  intro i
  obtain ⟨stage, hs⟩ := cleared (i + 1)
  exact sound stage i (hs stage (by omega) i (by omega))

end MovingClockRefutations
