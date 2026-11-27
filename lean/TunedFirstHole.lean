import Std

namespace TunedFirstHole

/-- Increasing order on the positive integers not divisible by the modulus. -/
def defaultValue (m i : Nat) : Nat :=
  m * (i / (m-1)) + (i % (m-1) + 1)

theorem default_nonmultiple (m i : Nat) (hm : 1 < m) :
    defaultValue m i % m ≠ 0 := by
  have small := Nat.mod_lt i (y := m-1) (by omega)
  unfold defaultValue
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Once the first missing quotient has been selected, all smaller
    ordinary addresses are either default outputs or earlier multiples. -/
theorem first_filtered (made : Nat → Prop) (m q : Nat) (hm : 0 < m)
    (missing : ¬ made (m*q))
    (earlier : ∀ r, r < q → made (m*r))
    (defaults : ∀ x, x < m*q → x % m ≠ 0 → made x) :
    (¬ made (m*q)) ∧ ∀ x, x < m*q → made x := by
  refine ⟨missing,?_⟩
  intro x small
  by_cases residue : x % m = 0
  · have hq : x / m < q :=
      (Nat.div_lt_iff_lt_mul hm).2 (by simpa [Nat.mul_comm] using small)
    have val := Nat.mod_add_div x m
    rw [residue, Nat.zero_add] at val
    exact val ▸ earlier (x/m) hq
  · exact defaults x small residue

/-- Count the exceptional residue class at positive offsets up to K. -/
def exceptional (m w : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => exceptional m w k + if m ∣ w-(k+1) then 1 else 0

theorem count_exceptional {m w K : Nat} (multiple : m ∣ w) (inside : K ≤ w) :
    exceptional m w K = K / m := by
  induction K with
  | zero => simp [exceptional]
  | succ k ih =>
    rw [exceptional,ih (by omega),Nat.succ_div]
    simp only [Nat.dvd_sub_iff_right inside multiple]

end TunedFirstHole
