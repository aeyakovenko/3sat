import Std

namespace LinkedQueryRollback

/-- The interval containing the sentinel complements the selected query bit. -/
def advance (feedback previous current salt : Bool) : Bool :=
  ((current.xor feedback).xor previous).xor salt

theorem telescope_step (previous current carried salt : Bool) :
    advance (previous.xor carried) previous current salt = current.xor (carried.xor salt) := by
  cases previous <;> cases current <;> cases carried <;> cases salt <;> decide

def finish : List (Bool × Bool) → Bool → Bool → Bool
  | [], _, feedback => feedback
  | (current, salt) :: xs, previous, feedback =>
    finish xs current (advance feedback previous current salt)

theorem intervention (xs : List (Bool × Bool)) (previous b : Bool) :
    finish xs previous (!b) = !(finish xs previous b) := by
  induction xs generalizing previous b with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨current, salt⟩ := pair
    have neg : advance (!b) previous current salt = !(advance b previous current salt) := by
      cases b <;> cases previous <;> cases current <;> cases salt <;> decide
    simp only [finish, neg, ih]

/-- Accounting invariant for a prefix-rollback online simulation. -/
theorem replay_balance (executed erased oldLength remove append : Nat)
    (inv : executed = oldLength + erased) (valid : remove ≤ oldLength) :
    executed + append = (oldLength - remove + append) + (erased + remove) := by omega

theorem total_step_cost (executed erased finalLength : Nat)
    (balance : executed = finalLength + erased) :
    executed + erased = finalLength + 2 * erased := by omega

/-- A differing record can introduce at most two work-address differences.
    An identical visited store removes one. A skipped interval changes none. -/
inductive Repair : Nat → Nat → Nat → Nat → Prop where
  | start : Repair 0 0 0 0
  | changed {diff clean live visited next : Nat} :
      Repair diff clean live visited → next ≤ live + 2 →
      Repair (diff + 1) clean next (visited + 1)
  | discharge {diff clean live visited : Nat} :
      Repair diff clean (live + 1) visited →
      Repair diff (clean + 1) live (visited + 1)

theorem repair_charge {diff clean live visited : Nat} (h : Repair diff clean live visited) :
    clean + live ≤ 2 * diff ∧ visited = diff + clean := by
  induction h with
  | start => omega
  | changed h bound ih => omega
  | discharge h ih => omega

theorem visited_slots {diff clean live visited : Nat} (h : Repair diff clean live visited) :
    visited ≤ 3 * diff := by
  obtain ⟨budget, count⟩ := repair_charge h
  omega

end LinkedQueryRollback
