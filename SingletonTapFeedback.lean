import Std

namespace SingletonTapFeedback

/-- A zero persists along the residue chain of a singleton AND factor. -/
theorem chain_of_zeros (x : Nat → Bool) (a t : Nat)
    (back : ∀ i, x (i+a) = true → x i = true) (zero : x t = false) :
    ∀ j, x (t+j*a) = false := by
  intro j
  induction j with
  | zero => simpa using zero
  | succ j ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc]
    cases h : x (t+j*a+a) with
    | false => rfl
    | true => exact Bool.noConfusion (ih.symm.trans (back _ h))

/-- A shared length-D window is enough to continue a period forever
    for any deterministic D-memory recurrence. -/
theorem periodic_after_window (x : Nat → Bool) (d a start : Nat)
    (rule : (Fin d → Bool) → Bool)
    (recurrence : ∀ n, x (n+d) = rule (fun i => x (n+i)))
    (window : ∀ j < d, x (start+j) = x (start+a+j)) :
    ∀ j, x (start+j) = x (start+a+j) := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases early : j < d
    · exact window j early
    · let k := j-d
      have step : k+d=j := by dsimp [k]; omega
      have hl : start+j = (start+k)+d := by omega
      have hr : start+a+j = (start+a+k)+d := by omega
      rw [hl, hr, recurrence, recurrence]
      apply congrArg rule
      funext i
      have small : k+i.val < j := by have := i.isLt; omega
      simpa only [Nat.add_assoc] using ih (k+i.val) small

end SingletonTapFeedback
