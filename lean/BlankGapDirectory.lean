import Std

/-! Amortization of interval reassignment. For a particular surviving key,
an update can shrink its existing interval without reassigning its ID, or
move it to the smaller interval remaining after deletion of a key. Updates
to other intervals need not be recorded. -/
namespace BlankGapDirectory

theorem smaller_half (left right : Nat) :
    2 * (min left right + 1) ≤ (left + 1 + right) + 1 := by
  cases Nat.le_total left right with
  | inl h => rw [Nat.min_eq_left h]; omega
  | inr h => rw [Nat.min_eq_right h]; omega

/-- The indices are the initial capacity, present interval length, and
number of times this key's own stored interval ID has been changed. -/
inductive KeyHistory (capacity : Nat) : Nat → Nat → Prop where
  | start : KeyHistory capacity capacity 0
  | retained {old new moves} (past : KeyHistory capacity old moves) (shrinks : new ≤ old) :
      KeyHistory capacity new moves
  | reassigned {left right moves} (past : KeyHistory capacity (left + 1 + right) moves) :
      KeyHistory capacity (min left right) (moves + 1)

theorem remaining_budget {capacity current moves : Nat}
    (h : KeyHistory capacity current moves) :
    (current + 1) * 2 ^ moves ≤ capacity + 1 := by
  induction h with
  | start => simp
  | retained past shrinks ih =>
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.succ_le_succ shrinks)) ih
  | @reassigned left right moves past ih =>
    rw [Nat.pow_succ]
    calc
      (min left right + 1) * (2 ^ moves * 2) =
          (2 * (min left right + 1)) * 2 ^ moves := by ac_rfl
      _ ≤ ((left + 1 + right) + 1) * 2 ^ moves :=
          Nat.mul_le_mul_right _ (smaller_half left right)
      _ ≤ _ := ih

/-- Count each key until just before deletion, while its interval is
nonempty. This yields a slightly sharper integer bound on its moves. -/
theorem key_move_bound {capacity current moves : Nat}
    (h : KeyHistory capacity current moves) (live : current > 0) :
    moves + 1 ≤ (capacity + 1).log2 := by
  apply (Nat.le_log2 (by omega)).mpr
  have bound := remaining_budget h
  have smaller := Nat.mul_le_mul_right (2 ^ moves) (show 2 ≤ current + 1 by omega)
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ moves) 2]
  omega

/-- Summing the per-key costs bounds every stored ID reassignment in the
whole directory. Computing the constant number of endpoints at each
deletion is additional constant work per key. -/
theorem total_reassignments {capacity : Nat} (counts : List Nat)
    (survived : ∀ r ∈ counts, ∃ size > 0, KeyHistory capacity size r) :
    counts.sum ≤ counts.length * ((capacity + 1).log2 - 1) := by
  induction counts with
  | nil => simp
  | cons r rs ih =>
    obtain ⟨size, live, trace⟩ := survived r (by simp)
    have hr := key_move_bound trace live
    have tail := ih (fun s hs => survived s (List.mem_cons_of_mem _ hs))
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

end BlankGapDirectory
