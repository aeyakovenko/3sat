import Std

namespace FifoProducerCredits

/-- Use the credits in queue order on demand measured on a common grid. -/
def paid : List Nat → Nat → Nat
  | [], _ => 0
  | balance :: rest, demand => min balance demand + paid rest (demand - balance)

def outstanding : List Nat → Nat → Nat
  | [], _ => 0
  | balance :: rest, demand => (balance - demand) + outstanding rest (demand - balance)

theorem totalPaid (credits : List Nat) (demand : Nat) :
    paid credits demand = min demand credits.sum := by
  induction credits generalizing demand with
  | nil => simp [paid]
  | cons balance rest ih =>
    simp only [paid, ih, List.sum_cons]
    omega

theorem totalOutstanding (credits : List Nat) (demand : Nat) :
    outstanding credits demand = credits.sum - demand := by
  induction credits generalizing demand with
  | nil => simp [outstanding]
  | cons balance rest ih =>
    simp only [outstanding, ih, List.sum_cons]
    omega

theorem conserveCredits (credits : List Nat) (demand : Nat) :
    paid credits demand + outstanding credits demand = credits.sum := by
  rw [totalPaid, totalOutstanding]
  omega

end FifoProducerCredits
