import Std

namespace WinnerInformedStages

/-- The existence search either supplies a falsifying word or reports the
    prescribed fallback. Soundness is needed only on a genuine win. -/
theorem genuineFallback {Word : Type} (fails : Word → Prop) (w : Word)
    (choice : Option Word) (won : Prop)
    (searchSome : ∀ x, choice = some x → fails x)
    (searchNone : choice = none → ∀ x, ¬fails x)
    (conditionalSound : won → ¬fails (choice.getD w))
    (genuine : won) : choice.getD w = w ∧ ∀ x, ¬fails x := by
  cases hc : choice with
  | none => exact ⟨rfl, searchNone hc⟩
  | some x =>
    have bad := searchSome x hc
    have good := conditionalSound genuine
    simp [hc] at good
    exact False.elim (good bad)

private theorem distinctCount {xs pool : List Nat} (distinct : xs.Nodup)
    (inside : ∀ x ∈ xs, x ∈ pool) : xs.length ≤ pool.length := by
  induction xs generalizing pool with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    have found := inside x (by simp)
    have pos := List.length_pos_of_mem found
    have lower := ih tail (pool := pool.erase x) (by
      intro y hy
      have diff : y ≠ x := fun eq => fresh (eq ▸ hy)
      exact (List.mem_erase_of_ne diff).mpr (inside y (by simp [hy])))
    rw [List.length_erase_of_mem found] at lower
    simp
    omega

/-- Failure throughout a window of e+1 eligible dates would supply an
    impossibly long list of different preempting ranks below e. -/
theorem windowContainsWin (e : Nat) (hasWin : Prop) (blockers : List Nat)
    (unique : blockers.Nodup) (smaller : ∀ x ∈ blockers, x < e)
    (missed : ¬hasWin → blockers.length = e+1) : hasWin := by
  apply Classical.byContradiction
  intro noWin
  have room := distinctCount (pool := List.range e) unique
    (fun x hx => List.mem_range.mpr (smaller x hx))
  simp at room
  have full := missed noWin
  omega

/-- Distinct preemptors from disjoint windows count against the same prefix
    of ranks as the designated winners. -/
theorem totalDelayCharge (E : Nat) (winners delays : List Nat)
    (unique : (winners ++ delays).Nodup)
    (inPrefix : ∀ r ∈ winners ++ delays, r ≤ E) :
    delays.length ≤ E+1-winners.length := by
  have room := distinctCount (pool := List.range (E+1)) unique
    (fun r hr => List.mem_range.mpr (Nat.lt_succ_of_le (inPrefix r hr)))
  simp at room
  omega

/-- In an increasing list, `after` comprises exactly the dates later than the
    win. Deleting at most that many final entries keeps the true date. -/
theorem peelList {α : Type} (before after : List α) (win : α) (s : Nat)
    (safe : s ≤ after.length) :
    (before ++ [win] ++ after).take ((before ++ [win] ++ after).length - s) =
      before ++ [win] ++ after.take (after.length - s) := by
  let earlierDates := before ++ [win]
  change (earlierDates ++ after).take ((earlierDates ++ after).length - s) = _
  have size : (earlierDates ++ after).length - s =
      earlierDates.length + (after.length - s) := by
    simp only [List.length_append]
    omega
  rw [size, List.take_append]

theorem tightPeelEndsAtWin {α : Type} (before after : List α) (win : α) :
    ((before ++ [win] ++ after).take
      ((before ++ [win] ++ after).length - after.length)).getLast? = some win := by
  rw [peelList before after win after.length (Nat.le_refl _)]
  simp [List.getLast?_append]

end WinnerInformedStages
