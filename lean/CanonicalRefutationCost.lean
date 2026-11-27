import Std

namespace CanonicalRefutationCost

/-- `target` is the canonical bit, `accepts` the SAT verdict and `shortNo` the
    existence of a verified refutation meeting the length bound. -/
structure Pin where
  target : Bool
  accepts : Bool
  shortNo : Bool
  sound : shortNo = true → accepts = false

def correct (x : Pin) : Bool := x.target == x.accepts

def witnessed (x : Pin) : Bool :=
  (x.target && x.accepts) || (!x.target && x.shortNo)

def hardNegative (x : Pin) : Bool := !x.target && !x.accepts && !x.shortNo

def score (p : Pin → Bool) : List Pin → Nat
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + score p xs

theorem per_pin (x : Pin) :
    (if correct x then 1 else 0 : Nat) =
    (if witnessed x then 1 else 0) + (if hardNegative x then 1 else 0) := by
  rcases x with ⟨t, a, n, h⟩
  cases t <;> cases a <;> cases n <;> simp_all [correct, witnessed, hardNegative] <;> exact Bool.noConfusion (h rfl)

theorem correct_partition (xs : List Pin) :
    score correct xs = score witnessed xs + score hardNegative xs := by
  induction xs with
  | nil => simp [score]
  | cons x xs ih =>
    simp only [score]
    rw [per_pin, ih]
    omega

theorem excess_forces_hard_negatives (xs : List Pin) (threshold excess slack : Nat)
    (advantage : threshold + excess ≤ score correct xs)
    (witness_cap : score witnessed xs ≤ threshold + slack) :
    excess ≤ score hardNegative xs + slack := by
  have h := correct_partition xs
  omega

end CanonicalRefutationCost
