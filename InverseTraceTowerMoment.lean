import Std

namespace InverseTraceTowerMoment

/-- One lower fiber has 2^r members. Count upper inputs by the behavior
    of the trace form on that fiber, with all denominators cleared. -/
theorem lift_mass {r q constantOne nonconstant : Nat}
    (constantCount : constantOne * 2^(r+1) = q)
    (functionalCount : nonconstant + 2 * constantOne = q) :
    constantOne * 2^(r+1) + nonconstant * 2^r = q * 2^r ∧
    constantOne * 2^(r+1) = q := by
  constructor
  · rw [← functionalCount, Nat.add_mul, Nat.pow_succ]
    rw [Nat.mul_assoc 2 constantOne, Nat.mul_comm 2 (constantOne * 2^r)]
    rw [← Nat.mul_assoc, Nat.add_comm]
  · exact constantCount

/-- If the chance of increasing dimension r is 2^(-r), the conditional
    expected value of 2^r increases by exactly one. -/
theorem morris_moment {r growing stable total : Nat}
    (mass : growing + stable = total)
    (fraction : growing * 2^r = total) :
    growing * 2^(r+1) + stable * 2^r = total * (2^r + 1) := by
  have weighted : growing * 2^r + stable * 2^r = total * 2^r := by
    rw [← Nat.add_mul, mass]
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_add, Nat.mul_one]
  omega

end InverseTraceTowerMoment
