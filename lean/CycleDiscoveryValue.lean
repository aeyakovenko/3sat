import Std

namespace CycleDiscoveryValue

/-- When there are 2j+1 odd components, the expected fraction of components
    remaining at discovery has numerator 2·4···(2j) and denominator
    3·5···(2j+1). The empty products both equal one. -/
def numer : Nat → Nat
  | 0 => 1
  | j+1 => (2*(j+1))*numer j

def denom : Nat → Nat
  | 0 => 1
  | j+1 => (2*(j+1)+1)*denom j

theorem positive_numer (j : Nat) : 0 < numer j := by
  induction j with
  | zero => decide
  | succ j ih => exact Nat.mul_pos (by omega) ih

theorem positive_denom (j : Nat) : 0 < denom j := by
  induction j with
  | zero => decide
  | succ j ih => exact Nat.mul_pos (by omega) ih

/-- Successive fractions in a common denominator for one Bellman step.
    The first coefficient is for 2(j+1)+1 odd components, the second for
    two fewer. -/
theorem coefficient_step (j : Nat) :
    (2*(j+1)+1)*(numer (j+1)*denom j) =
      (2*(j+1))*(numer j*denom (j+1)) := by
  simp only [numer,denom]
  ac_rfl

/-- Querying an odd tail has o-1 possible next heads that remove two odd
    components. The other c-o heads preserve their number. Each possible
    head leaves c-1 components in total. Evaluation is multiplied by c-1
    and by the common denominator of a and prev. -/
def oddScore (c o a prev : Nat) : Nat :=
  (o-1)*((c-1)*prev) + (c-o)*((c-1)*a)

/-- For a query from an even tail, all c-1 possible heads preserve the
    number of odd components. This action is available only when c>o. -/
def evenScore (c a : Nat) : Nat := (c-1)*((c-1)*a)

theorem odd_action_value {c o a prev : Nat} (available : o ≤ c)
    (coefficient : o*a = (o-1)*prev) :
    oddScore c o a prev = (c-1)*(c*a) := by
  calc
    oddScore c o a prev = (c-1)*((o-1)*prev+(c-o)*a) := by
      unfold oddScore
      rw [Nat.mul_add]
      ac_rfl
    _ = (c-1)*(c*a) := by
      rw [← coefficient, ← Nat.add_mul]
      congr 2
      omega

theorem even_action_loss {c a : Nat} (positive : 0 < c) :
    evenScore c a + (c-1)*a = (c-1)*(c*a) := by
  calc
    evenScore c a + (c-1)*a = (c-1)*(((c-1)+1)*a) := by
      simp [evenScore, Nat.add_mul, Nat.mul_add]
    _ = (c-1)*(c*a) := by rw [show c-1+1=c by omega]

theorem odd_dominates {c o a prev : Nat} (active : 3 ≤ o) (available : o ≤ c)
    (coefficient : o*a = (o-1)*prev) :
    evenScore c a ≤ oddScore c o a prev := by
  rw [odd_action_value available coefficient, ← even_action_loss (by omega : 0 < c)]
  omega

/-- The proposed product value equals the larger of the two continuation
    values. At c=o the even action is infeasible, and including it in the
    maximum does not change the result. For j=0 the state with one odd
    component is already decided and has remaining value c. -/
theorem bellman_product (j c : Nat) (enough : 2*(j+1)+1 ≤ c) :
    let o := 2*(j+1)+1
    let a := numer (j+1)*denom j
    let prev := numer j*denom (j+1)
    max (oddScore c o a prev) (evenScore c a) = (c-1)*(c*a) := by
  dsimp only
  have h : (2*(j+1)+1)*(numer (j+1)*denom j) =
      ((2*(j+1)+1)-1)*(numer j*denom (j+1)) := by
    simpa using coefficient_step j
  rw [Nat.max_eq_left (odd_dominates (by omega) enough h), odd_action_value enough h]

end CycleDiscoveryValue
