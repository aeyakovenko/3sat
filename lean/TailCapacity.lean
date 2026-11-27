import Std

namespace TailCapacity

/-- Outstanding work after processing the first n arrivals and capacities. -/
def backlog (arrivals capacity : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => backlog arrivals capacity n + arrivals n - capacity n

/-- A dominating capacity on every remaining suffix bounds the backlog.
    The statement uses a common integer grid for finite rational data. -/
theorem backlog_and_future (arrivals capacity workLeft roomLeft : Nat → Nat)
    (workStep : ∀ n, workLeft n = arrivals n + workLeft (n + 1))
    (roomStep : ∀ n, roomLeft n = capacity n + roomLeft (n + 1))
    (fits : ∀ n, workLeft n ≤ roomLeft n) (n : Nat) :
    backlog arrivals capacity n + workLeft n ≤ roomLeft n := by
  induction n with
  | zero => simpa [backlog] using fits 0
  | succ n ih =>
    have w := workStep n
    have c := roomStep n
    have f := fits (n + 1)
    simp only [backlog]
    omega

end TailCapacity
