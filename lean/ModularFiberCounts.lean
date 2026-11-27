import Std

namespace ModularFiberCounts

def invisible (modulus n : Nat) : Bool := decide (0 < n ∧ n % modulus = 0)

/-- An occupied fiber invisible to the unweighted modular readout costs
    at least one whole modulus of names. -/
theorem missingNameBudget (sizes : List Nat) (modulus : Nat) :
    sizes.countP (invisible modulus) * modulus ≤ sizes.sum := by
  induction sizes with
  | nil => simp
  | cons n sizes ih =>
    by_cases h : 0 < n ∧ n % modulus = 0
    · have ge : modulus ≤ n := Nat.le_of_dvd h.1 (Nat.dvd_of_mod_eq_zero h.2)
      simp only [List.countP_cons, invisible, decide_eq_true h, ↓reduceIte,
        List.sum_cons, Nat.succ_mul]
      change sizes.countP (invisible modulus) * modulus + modulus ≤ n + sizes.sum
      omega
    · simp only [List.countP_cons, invisible, decide_eq_false h, Bool.false_eq_true,
        ↓reduceIte, List.sum_cons]
      change sizes.countP (invisible modulus) * modulus ≤ n + sizes.sum
      omega

/-- Given the uniform bound on eligible names, the number of missed
    nonempty fibers is strictly below N/(2*modulus), before real division. -/
theorem missingCubeBudget (sizes : List Nat) (modulus N : Nat)
    (eligible : 2 * sizes.sum < N) :
    2 * (sizes.countP (invisible modulus) * modulus) < N :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 (missingNameBudget sizes modulus)) eligible

/-- A dense signed graph with small discrepancy against the all-ones vectors
    has many edges of each sign, even after rounding block by block. -/
theorem twoDenseGraphs (plus minus total loss imbalance : Nat)
    (density : total ≤ plus + minus + loss)
    (up : plus ≤ minus + imbalance) (down : minus ≤ plus + imbalance) :
    total ≤ 2 * plus + imbalance + loss ∧ total ≤ 2 * minus + imbalance + loss := by
  omega

end ModularFiberCounts
