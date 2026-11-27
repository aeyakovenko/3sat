import Std

namespace NegativeWinnerRectangles

/-- The only possible right responder to a first win was selected by an
    accepted exclusion. Soundness rules out every right win in its wake. -/
theorem excludeRectangle {L R : Type} (firstWon : L → Prop) (nextWon : R → Prop)
    (chosen accepted : L → R → Prop)
    (firstRule : ∀ f, firstWon f → ∃ g, chosen f g ∧ accepted f g)
    (responseRule : ∀ f g r, firstWon f → chosen f g → nextWon r → r = g)
    (sound : ∀ f g, accepted f g → ¬(firstWon f ∧ nextWon g)) :
    ∀ f r, ¬(firstWon f ∧ nextWon r) := by
  intro f r ⟨hf, hr⟩
  obtain ⟨g, hg, ha⟩ := firstRule f hf
  have eq := responseRule f g r hf hg hr
  exact sound f g ha ⟨hf, eq ▸ hr⟩

private theorem countInside {xs pool : List Nat} (h : xs.Nodup)
    (mem : ∀ x ∈ xs, x ∈ pool) : xs.length ≤ pool.length := by
  induction xs generalizing pool with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp h
    have found := mem a (by simp)
    have pos := List.length_pos_of_mem found
    have bound := ih rest (pool := pool.erase a) (by
      intro x hx
      have ne : x ≠ a := fun eq => fresh (eq ▸ hx)
      exact (List.mem_erase_of_ne ne).mpr (mem x (by simp [hx])))
    rw [List.length_erase_of_mem found] at bound
    simp
    omega

/-- Count preemptors together with the right ranks, including their maximum.
    Survivor count uses the number of remaining first ranks at the positive win. -/
theorem survivingRows (q : Nat) (right blockers leftLive : List Nat)
    (unique : (right ++ blockers).Nodup)
    (bounded : ∀ x ∈ right ++ blockers, x ≤ q)
    (retirements : q + 1 ≤ leftLive.length + blockers.length) :
    right.length ≤ leftLive.length := by
  have cap := countInside (pool := List.range (q+1)) unique
    (fun x hx => List.mem_range.mpr (Nat.lt_succ_of_le (bounded x hx)))
  simp only [List.length_append, List.length_range] at cap
  omega

/-- At the true positive win a common search that reacts to any certified
    live edge by making an earlier offer cannot have certified even one edge. -/
theorem allPairsMissed {L R : Type} (liveL : L → Prop) (liveR : R → Prop)
    (certificate : L → R → Prop) (earlierOffer : Prop)
    (selection : (∃ f g, liveL f ∧ liveR g ∧ certificate f g) → earlierOffer)
    (winner : ¬ earlierOffer) : ∀ f g, liveL f → liveR g → ¬ certificate f g := by
  intro f g hf hg hc
  exact winner (selection ⟨f, g, hf, hg, hc⟩)

/-- If b+1 first winners all get their distinct successor awards at ranks ≤ b,
    the repeatedly available responder b must win at least one successor. -/
theorem genuineNegativePair (b : Nat) (successors : List Nat)
    (unique : successors.Nodup) (many : b < successors.length)
    (bounded : ∀ r ∈ successors, r ≤ b) : b ∈ successors := by
  apply Classical.byContradiction
  intro absent
  have cap := countInside (pool := List.range b) unique (by
    intro r hr
    have le := bounded r hr
    have ne : r ≠ b := fun eq => absent (eq ▸ hr)
    exact List.mem_range.mpr (by omega))
  simp at cap
  omega

end NegativeWinnerRectangles
