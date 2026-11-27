import Std

namespace GateFaultSpectrum

def sign (b : Bool) : Int := if b then -1 else 1

def phase (a b l k r : Bool) : Bool :=
  (a && b) ^^ (a && l) ^^ (b && k) ^^ r

/-- Unnormalized sum over one pair of variables of a mixed quadratic term. -/
theorem eliminate_pair (l k r : Bool) :
    sign (phase false false l k r) + sign (phase false true l k r) +
    sign (phase true false l k r) + sign (phase true true l k r) =
      2 * sign (r ^^ (l && k)) := by
  cases l <;> cases k <;> cases r <;> decide

theorem isolated_coordinate (r : Bool) :
    sign r + sign (!r) = 0 := by cases r <;> decide

/-- Normalized Parseval weights, scaled by a common positive denominator. -/
theorem full_mass_has_no_omitted_weight (total kept omitted : Nat)
    (partition : total = kept + omitted) (full : kept = total) : omitted = 0 := by
  omega

theorem granularity (kept units : Nat) (small : kept < units) :
    1 ≤ units - kept := by omega

/-- Given its parents, a gate's output and its residual determine one another. -/
theorem triangular_coordinate (gate output : Bool) :
    (output ^^ gate) ^^ gate = output := by cases gate <;> cases output <;> rfl

end GateFaultSpectrum
