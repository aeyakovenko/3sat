import Std

namespace OneBitProduction

/-- Total depth, including the branch bit, for a literal prefix. -/
theorem literal_length {j m : Nat} (le : j ≤ m) : j + (m-j) = m := by omega

def paddedLength (m D L : Nat) : Nat :=
  if m-D ≤ L ∧ L+2 ≤ m then m-1 else L

theorem pad_classifies_short {m D L : Nat} (short : paddedLength m D L < m) :
    paddedLength m D L = m-1 ∨ paddedLength m D L < m-D := by
  by_cases inGap : m-D ≤ L ∧ L+2 ≤ m
  · simp [paddedLength, inGap]
  · simp [paddedLength, inGap] at short ⊢
    omega

theorem pad_preserves_short {m D L : Nat} (short : L < m) :
    paddedLength m D L < m := by
  unfold paddedLength
  split <;> omega

theorem funded_length {header parameter p m D c : Nat}
    (room : D + p + c ≤ m) (saved : header + parameter < c) :
    header + parameter + p + (m-D-p-c) < m-D := by omega

/-- With masses in units of 1/32, the known mask budget fits the literal half,
    even after the factor two for the one extra length per block. -/
theorem literal_capacity {scale failed success requests : Nat}
    (f : failed ≤ 3*scale) (s : success ≤ scale)
    (h : requests ≤ 2*(failed+success)) : requests ≤ 16*scale := by omega

/-- Geometric cost of all allowed saving levels for one word. -/
def prefixPowers : Nat → Nat
  | 0 => 0
  | n+1 => prefixPowers n + 2^n

theorem prefixPowers_eq (n : Nat) : prefixPowers n + 1 = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prefixPowers, Nat.pow_succ]
    omega

/-- On the grid with denominator 2^m, charging all D with K + D < m
    costs at most the Kraft charge for a shortest name. -/
theorem all_savings_charge {m K : Nat} :
    prefixPowers (m-K) ≤ 2^(m-K) := by
  have := prefixPowers_eq (m-K)
  omega

/-- An extra gap of h bits discounts the geometric cost of that word. -/
theorem excess_saving {m K h : Nat} (fits : K + h ≤ m) :
    2^h * prefixPowers (m-K-h+1) ≤ 2 * 2^(m-K) := by
  have summ := all_savings_charge (m := m-K-h+1) (K := 0)
  simp only [Nat.sub_zero] at summ
  have exp : h+(m-K-h+1) = (m-K)+1 := by omega
  calc
    _ ≤ 2^h * 2^(m-K-h+1) := Nat.mul_le_mul_left _ summ
    _ = 2 * 2^(m-K) := by rw [← Nat.pow_add, exp, Nat.pow_succ, Nat.mul_comm]

/-- A band of attained saving indices telescopes to the difference of the
    two best-description weights, on a common integer grid. -/
theorem band_increment (depth late early : Nat) :
    prefixPowers (depth-late) - prefixPowers (depth-early) =
      2^(depth-late) - 2^(depth-early) := by
  have first := prefixPowers_eq (depth-late)
  have last := prefixPowers_eq (depth-early)
  omega

end OneBitProduction
