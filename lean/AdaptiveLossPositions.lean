import Std

namespace AdaptiveLossPositions

/-- A finite generator after a given history. A flagged step lists only
    the next symbols causing a rank loss. An unflagged step lists all symbols. -/
def completions {A : Type} (next : Bool → List A → List A) :
    List Bool → List A → Nat
  | [], _ => 1
  | flag :: flags, history =>
    ((next flag history).map fun v => completions next flags (v :: history)).sum

private theorem sum_map_cap {A : Type} (xs : List A) (f : A → Nat) (bound : Nat)
    (h : ∀ v, f v ≤ bound) : (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (h x) ih

/-- At the prescribed loss positions at most one possible symbol may survive,
    even when its identity depends on the entire previous history. -/
theorem prescribed_loss_bound {A : Type} (q : Nat) (next : Bool → List A → List A)
    (all : ∀ h, (next false h).length ≤ q) (one : ∀ h, (next true h).length ≤ 1)
    (flags : List Bool) (history : List A) :
    completions next flags history ≤ q ^ (flags.count false) := by
  induction flags generalizing history with
  | nil => simp [completions]
  | cons flag flags ih =>
    have bounded := sum_map_cap (next flag history) _ (q ^ flags.count false)
      (fun v => ih (v :: history))
    cases flag with
    | false =>
      have prod := Nat.mul_le_mul_right (q ^ flags.count false) (all history)
      exact (by simpa [completions, List.count_cons, Nat.pow_succ, Nat.mul_comm] using
        Nat.le_trans bounded prod)
    | true =>
      have prod := Nat.mul_le_mul_right (q ^ flags.count false) (one history)
      exact (by simpa [completions, List.count_cons] using Nat.le_trans bounded prod)

end AdaptiveLossPositions
