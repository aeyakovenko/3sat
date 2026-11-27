import Std

namespace TapeTravel

/-- Explicit time and travel accounting. -/
inductive Runs (step : σ → Nat → σ → Prop) : σ → σ → Nat → Nat → Prop where
  | nil (s) : Runs step s s 0 0
  | cons {s v w c t d} : step s c v → Runs step v w t d →
      Runs step s w (t + 1) (d + c)

theorem append_run (p : Runs step u v t d) (q : Runs step v w t' d') :
    Runs step u w (t+t') (d+d') := by
  induction p with
  | nil => simpa using q
  | cons edge _ ih =>
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Runs.cons edge (ih q)

theorem no_stationary_return_in_minimum
    (prefixRun : Runs step start s t d) (_loop : Runs step s s k 0)
    (suffixRun : Runs step s stop t' d')
    (minimum : ∀ j, Runs step start stop j (d+d') → t + k + t' ≤ j) :
    k = 0 := by
  have shorter := minimum (t+t') (append_run prefixRun suffixRun)
  omega

private theorem length_mul_le_sum (m : Nat) (xs : List Nat)
    (h : ∀ x ∈ xs, m ≤ x) : xs.length * m ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    have hx := h x (by simp)
    have hr := ih (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Apply when each unit move contributes to one translated grid's count. -/
theorem grid_has_light_offset (crossings : List Nat) (limit D : Nat)
    (total : crossings.sum ≤ D) (capacity : D < crossings.length * (limit+1)) :
    ∃ x ∈ crossings, x ≤ limit := by
  apply Classical.byContradiction
  intro nope
  have h : ∀ x ∈ crossings, limit+1 ≤ x := by
    intro x mem
    have cannot : ¬ x ≤ limit := fun le => nope ⟨x, mem, le⟩
    omega
  have large := length_mul_le_sum (limit+1) crossings h
  omega

end TapeTravel
