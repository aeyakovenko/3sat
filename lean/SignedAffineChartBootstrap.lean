import Std

namespace SignedAffineChartBootstrap

/-- A lower estimate for (b/a)^n when the positive integer numerators differ
    by at least one. No powers of real numbers are required. -/
theorem ratio_bound {a b : Nat} (lt : a < b) (n : Nat) :
    (a+n)*a^n ≤ a*b^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have step : (a+(n+1))*a ≤ (a+n)*b := by
      calc
        (a+(n+1))*a = (a+n)*a+a := by rw [← Nat.add_assoc, Nat.add_mul]; simp
        _ ≤ (a+n)*a+(a+n) := by omega
        _ = (a+n)*(a+1) := by simp [Nat.mul_add]
        _ ≤ (a+n)*b := Nat.mul_le_mul_left _ lt
    calc
      (a+(n+1))*a^(n+1) = ((a+(n+1))*a)*a^n := by simp [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm (a^n) a]
      _ ≤ ((a+n)*b)*a^n := Nat.mul_le_mul_right _ step
      _ = ((a+n)*a^n)*b := by ac_rfl
      _ ≤ (a*b^n)*b := Nat.mul_le_mul_right _ ih
      _ = a*b^(n+1) := by simp [Nat.pow_succ,Nat.mul_assoc]

/-- Starting with the rational exponent dNumerator/dDenominator, finite
    iteration of multiplication by 0<a/b<1 yields an exponent below one. -/
theorem finite_contraction {a b dNumerator dDenominator : Nat}
    (positive : 0 < a) (lt : a < b) (denominator : 0 < dDenominator) :
    ∃ n, dNumerator*a^n < dDenominator*b^n := by
  let n := a*dNumerator + 1
  have h := ratio_bound lt n
  have gap : a*dNumerator < a+n := by dsimp [n]; omega
  have strict : a*(dNumerator*a^n) < a*b^n := by
    rw [← Nat.mul_assoc]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right gap (Nat.pow_pos positive)) h
  have final := Nat.lt_of_mul_lt_mul_left strict
  exact ⟨n, Nat.lt_of_lt_of_le final (by simpa using Nat.mul_le_mul_right (b^n) denominator)⟩

/-- After a local transition trace has been frozen, every required equality
    constrains a word at only its own address. -/
def AtAddress {Addr Word Row : Type} (key : Row → Addr)
    (allowed : Row → Word → Prop) (a : Addr) (v : Word) : Prop :=
  ∀ r, key r = a → allowed r v

theorem assemble_words {Addr Word Row : Type} (key : Row → Addr)
    (allowed : Row → Word → Prop) :
    (∃ M : Addr → Word, ∀ r, allowed r (M (key r))) ↔
      ∀ a, ∃ v, AtAddress key allowed a v := by
  constructor
  · rintro ⟨M,h⟩ a
    exact ⟨M a,fun r eq => eq ▸ h r⟩
  · intro h
    exact ⟨fun a => Classical.choose (h a), fun r =>
      Classical.choose_spec (h (key r)) r rfl⟩

/-- Given a one-word inconsistency witness bound, it transfers unchanged to
    all the cells of a frozen trace. It does not grow with the address count. -/
theorem global_conflict {Addr Word Row : Type} (key : Row → Addr)
    (allowed : Row → Word → Prop) (k : Nat)
    (localBound : ∀ a, (¬ ∃ v, AtAddress key allowed a v) →
      ∃ rs : List Row, rs.length ≤ k ∧ (∀ r ∈ rs, key r = a) ∧
        ¬ ∃ v, ∀ r ∈ rs, allowed r v)
    (impossible : ¬ ∃ M : Addr → Word, ∀ r, allowed r (M (key r))) :
    ∃ a, ∃ rs : List Row, rs.length ≤ k ∧ (∀ r ∈ rs, key r = a) ∧
      ¬ ∃ v, ∀ r ∈ rs, allowed r v := by
  classical
  have bad : ¬∀ a, ∃ v, AtAddress key allowed a v :=
    fun good => impossible ((assemble_words key allowed).mpr good)
  obtain ⟨a,h⟩ := Classical.not_forall.mp bad
  exact ⟨a,localBound a h⟩

end SignedAffineChartBootstrap
