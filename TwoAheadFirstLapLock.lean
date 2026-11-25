import Std

namespace TwoAheadFirstLapLock

variable {α : Type} [DecidableEq α]

/-- Memory immediately before stage t. Stage t reads at p t, then uses
    that reply as the destination of the compulsory write of p (t+2). -/
def memory (initial : α → α) (p : Nat → α) : Nat → α → α
  | 0 => initial
  | t + 1 => fun a =>
      if a = memory initial p t (p t) then p (t + 2) else memory initial p t a

theorem origin (initial : α → α) (p : Nat → α) (t : Nat) (a : α) :
    memory initial p t a = initial a ∨
      ∃ j < t, memory initial p j (p j) = a ∧
        memory initial p t a = p (j + 2) := by
  induction t with
  | zero => exact Or.inl rfl
  | succ t ih =>
    by_cases hit : a = memory initial p t (p t)
    · exact Or.inr ⟨t, by omega, hit.symm, by simp [memory, hit]⟩
    · have unchanged : memory initial p (t+1) a = memory initial p t a := by
        simp [memory, hit]
      rcases ih with h | ⟨j, hj, dest, val⟩
      · exact Or.inl (unchanged.trans h)
      · exact Or.inr ⟨j, by omega, dest, unchanged.trans val⟩

theorem lock_step (initial : α → α) (p : Nat → α) (t : Nat)
    (h : memory initial p t (p t) = p (t+1)) :
    memory initial p (t+1) (p (t+1)) = p ((t+1)+1) := by
  simp [memory, h]

theorem lock_persists (initial : α → α) (p : Nat → α) (t : Nat)
    (h : memory initial p t (p t) = p (t+1)) (k : Nat) :
    memory initial p (t+k) (p (t+k)) = p ((t+k)+1) := by
  induction k with
  | zero => exact h
  | succ k ih => exact lock_step initial p (t+k) ih

/-- During distinct first visits, a cell whose address is absent from the
    initial image keeps its original contents until read, unless the scan
    has already started returning each next cursor. -/
theorem untouched_until_lock (initial : α → α) (p : Nat → α) (i : Nat)
    (distinct : ∀ u v, u ≤ i → v ≤ i → p u = p v → u = v)
    (absent : ∀ a, initial a ≠ p i)
    (unlocked : ∀ u < i, memory initial p u (p u) ≠ p (u+1)) :
    memory initial p i (p i) = initial (p i) := by
  rcases origin initial p i (p i) with h | ⟨j, hj, target, _⟩
  · exact h
  · rcases origin initial p j (p j) with orig | ⟨u, hu, dest, val⟩
    · exact False.elim (absent (p j) (orig.symm.trans target))
    · have eqidx : u+2 = i :=
        distinct (u+2) i (by omega) (by omega) (val.symm.trans target)
      have adj : j = u+1 := by omega
      exact False.elim (unlocked u (by omega) (adj ▸ dest))

theorem first_lap_trigger (initial : α → α) (p : Nat → α) (i : Nat)
    (distinct : ∀ u v, u ≤ i → v ≤ i → p u = p v → u = v)
    (absent : ∀ a, initial a ≠ p i)
    (seed : initial (p i) = p (i+1)) :
    memory initial p i (p i) = p (i+1) := by
  by_cases earlier : ∃ u < i, memory initial p u (p u) = p (u+1)
  · obtain ⟨u, hu, lock⟩ := earlier
    have lasts := lock_persists initial p u lock (i-u)
    simpa [show u+(i-u) = i by omega] using lasts
  · exact (untouched_until_lock initial p i distinct absent
      (fun u hu h => earlier ⟨u, hu, h⟩)).trans seed

end TwoAheadFirstLapLock
