import Std

namespace ClockSpectrum

/-- If a log release is close to its own grid line, and is observed in a
    narrow window before another grid line, the two rates coincide. -/
theorem uniqueRate (m i j released ownSlack window : Nat)
    (beforeOwn : released ≤ j * m) (nearOwn : j * m ≤ released + ownSlack)
    (beforeEnd : released ≤ i * m) (inWindow : i * m ≤ released + window)
    (ownSmall : ownSlack < m) (windowSmall : window < m) : i = j := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · have gap := Nat.mul_le_mul_right m (show i + 1 ≤ j by omega)
    rw [Nat.add_mul, Nat.one_mul] at gap
    omega
  · exact h
  · have gap := Nat.mul_le_mul_right m (show j + 1 ≤ i by omega)
    rw [Nat.add_mul, Nat.one_mul] at gap
    omega

/-- Each spoiled word uses a disjoint generic name of at least the unit cost. -/
theorem halfUnspoiled (spoiled total unitCost budget : Nat) (positive : 0 < unitCost)
    (charged : spoiled * unitCost ≤ budget) (small : budget + budget ≤ total * unitCost) :
    spoiled + spoiled ≤ total := by
  refine Nat.le_of_mul_le_mul_right ?_ positive
  rw [Nat.add_mul]
  omega

/-- A false column can belong to only finitely many header windows. Their
    separate eventual exclusions therefore have a common starting stage. -/
theorem commonStage {α : Type} (wins : α → Nat → Prop) (windows : List α)
    (excluded : ∀ w ∈ windows, ∃ n, ∀ s ≥ n, ¬ wins w s) :
    ∃ n, ∀ s ≥ n, ∀ w ∈ windows, ¬ wins w s := by
  induction windows with
  | nil => exact ⟨0, by simp⟩
  | cons w ws ih =>
    obtain ⟨n, atHead⟩ := excluded w (by simp)
    obtain ⟨m, inTail⟩ := ih (fun v hv => excluded v (by simp [hv]))
    refine ⟨max n m, ?_⟩
    intro s hs v hv
    rcases List.mem_cons.mp hv with h | h
    · subst v
      exact atHead s (Nat.le_trans (Nat.le_max_left n m) hs)
    · exact inTail s (Nat.le_trans (Nat.le_max_right n m) hs) v h

end ClockSpectrum
