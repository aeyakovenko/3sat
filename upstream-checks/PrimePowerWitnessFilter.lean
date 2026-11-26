import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Sum

open Finset Polynomial

namespace PrimePowerWitnessFilter

variable {p : ℕ} [Fact p.Prime]

/-- Below the prime-power cutoff the whole Pascal row is periodic in its row index. -/
theorem choose_period (s n i : ℕ) (hi : i < p ^ s) :
    ((n + p ^ s).choose i : ZMod p) = (n.choose i : ZMod p) := by
  let f : (ZMod p)[X] := 1 + X
  have periodic : f ^ (n + p ^ s) = f^n + f^n * X^(p^s) := by
    rw [pow_add]
    have frob : f^(p^s) = 1 + X^(p^s) := by
      simpa only [f, one_pow] using
        (add_pow_char_pow (1 : (ZMod p)[X]) X p s)
    rw [frob, mul_add, mul_one]
  have h := congrArg (fun g : (ZMod p)[X] => g.coeff i) periodic
  simpa [f, coeff_one_add_X_pow, coeff_mul_X_pow', Nat.not_le.mpr hi] using h

theorem choose_mod_period (s n i : ℕ) (hi : i < p ^ s) :
    (n.choose i : ZMod p) = ((n % (p^s)).choose i : ZMod p) := by
  have many (r k : ℕ) : ((r + k * p ^ s).choose i : ZMod p) = (r.choose i : ZMod p) := by
    induction k with
    | zero => simp
    | succ k ih => simpa [Nat.succ_mul, ← Nat.add_assoc] using
        (choose_period s (r + k * p^s) i hi).trans ih
  conv_lhs => rw [← Nat.mod_add_div n (p^s)]
  simpa [Nat.mul_comm (p^s)] using many (n % p^s) (n / p^s)

/-- The weight on all nonempty subsets of at most p^s-1 marked witnesses.
    The subtraction removes the empty subset and reverses all remaining signs. -/
def marker (p s witnesses : ℕ) : ZMod p :=
  1 - ∑ i ∈ range (p ^ s), (-1 : ZMod p)^i * (witnesses.choose i : ZMod p)

theorem marker_as_nonempty_subsets (s n : ℕ) :
    marker p s n =
      ∑ j ∈ range (p^s-1), (-1 : ZMod p)^j * (n.choose (j+1) : ZMod p) := by
  unfold marker
  have hq : 0 < p^s := pow_pos (Fact.out : p.Prime).pos _
  conv_lhs => rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt hq)]
  rw [sum_range_succ']
  simp [pow_succ, Finset.sum_neg_distrib]

theorem marker_eq (s n : ℕ) :
    marker p s n = if p^s ∣ n then 0 else 1 := by
  let q := p^s
  let r := n % q
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos _
  have hr : r < q := Nat.mod_lt n hq
  have hsum :
      (∑ i ∈ range q, (-1 : ZMod p)^i * (n.choose i : ZMod p)) =
        (∑ i ∈ range (r+1), (-1 : ZMod p)^i * (r.choose i : ZMod p)) := by
    calc
      _ = ∑ i ∈ range q, (-1 : ZMod p)^i * (r.choose i : ZMod p) := by
        apply sum_congr rfl
        intro i hi
        rw [choose_mod_period s n i (mem_range.mp hi)]
      _ = _ := by
        symm
        apply sum_subset (range_mono (Nat.succ_le_of_lt hr))
        intro i _ hnot
        have hlt : r < i := by simpa using hnot
        simp [Nat.choose_eq_zero_of_lt hlt]
  have hbin :
      (∑ i ∈ range (r+1), (-1 : ZMod p)^i * (r.choose i : ZMod p)) =
        ((-1 : ZMod p) + 1)^r := by
    simpa using (add_pow (-1 : ZMod p) 1 r).symm
  unfold marker
  change 1 - (∑ i ∈ range q, (-1 : ZMod p)^i * (n.choose i : ZMod p)) = _
  rw [hsum, hbin, neg_add_cancel]
  by_cases divides : p^s ∣ n
  · have hz : r = 0 := Nat.mod_eq_zero_of_dvd divides
    simp [divides, hz]
  · have hnz : r ≠ 0 := fun hz => divides (Nat.dvd_of_mod_eq_zero hz)
    simp [divides, zero_pow hnz]

end PrimePowerWitnessFilter
