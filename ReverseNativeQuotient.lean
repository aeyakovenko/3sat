import Std

namespace ReverseNativeQuotient

theorem boundary {s i q : Nat} (hi : 0 < i) (hq : 0 < q) :
    q ≤ s / i ↔ i ≤ s / q := by
  rw [Nat.le_div_iff_mul_le hi, Nat.le_div_iff_mul_le hq, Nat.mul_comm]

theorem uniqueRegion {s i q : Nat} (hi : 0 < i) :
    s / i = q ↔ q * i ≤ s ∧ s < (q+1)*i := by
  constructor
  · intro h
    constructor
    · apply (Nat.le_div_iff_mul_le hi).1
      omega
    · apply (Nat.div_lt_iff_lt_mul hi).1
      omega
  · intro h
    exact Nat.div_eq_of_lt_le h.1 h.2

def deltaPrefix (x : Nat → Bool) : Nat → Bool
  | 0 => false
  | q+1 => deltaPrefix x q ^^ (x q ^^ x (q+1))

theorem telescope (x : Nat → Bool) (q : Nat) :
    (x 0 ^^ deltaPrefix x q) = x q := by
  induction q with
  | zero => simp [deltaPrefix]
  | succ q ih =>
    simp only [deltaPrefix]
    rw [← Bool.xor_assoc, ih]
    cases x q <;> cases x (q+1) <;> rfl

/-- The inverse subtraction shift embeds with a fixed two-bit prefix.
    The Euclidean remainder before wrapping is L+h-j. -/
theorem shiftWindow {L h j : Nat} (hh : h < L) (hj : j < L) :
    (3*L+h)/(2*L+j) = 1 ∧ (3*L+h) % (2*L+j) = L+h-j := by
  have hq : (3*L+h)/(2*L+j) = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  constructor
  · exact hq
  · rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_one]
    omega

/-- Swap a radix-q digit past one radix-D group, preserving the physical
    integer that the digit sequence denotes. -/
theorem radixSwap (q D h d e : Nat) :
    q*(D*h+d)+e = D*(q*h+(q*d+e)/D)+(q*d+e)%D := by
  have eq := congrArg (fun z => D*(q*h)+z) (Nat.div_add_mod (q*d+e) D).symm
  simpa only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
              Nat.add_assoc] using eq

theorem windowValue {s i q : Nat} (hi : 0 < i) (hq : 0 < q)
    (region : s / i = q) :
    s % i = q * (s/q - i) + s%q := by
  have ihit : i ≤ s/q := (boundary hi hq).1 (by omega)
  have prod := Nat.mul_le_mul_left q ihit
  have split := Nat.div_add_mod s q
  rw [Nat.mod_eq_sub_mul_div (x := s) (k := i), region, Nat.mul_comm i q, Nat.mul_sub]
  omega

end ReverseNativeQuotient
