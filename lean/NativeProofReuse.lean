import Std

/-! Finite accounting for passing ordinary proof lines to later widths.
The quantities can be any natural-valued length, cap, transfer and overhead.
The interpretation as Hilbert proofs and the limit estimates are external. -/

namespace NativeProofReuse

def total (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m+1 => total f m + f m

/-- Concatenation with shared earlier lines costs each transfer and its
final line once, for every finite number of widths. -/
theorem chain_bound (length transfer overhead : Nat → Nat)
    (append : ∀ i, length (i+1) ≤ length i + transfer i + overhead i)
    (m : Nat) : length m ≤ length 0 + total transfer m + total overhead m := by
  induction m with
  | zero => simp [total]
  | succ i ih =>
    have step := append i
    simp only [total]
    omega

/-- An exact cap violation forces the stated expenditure even when the
individual transfer lengths and output-line overheads vary at every step. -/
theorem expenditure (length cap transfer overhead : Nat → Nat)
    (append : ∀ i, length (i+1) ≤ length i + transfer i + overhead i) (m : Nat)
    (hard : cap m < length m) :
    cap m < length 0 + total transfer m + total overhead m :=
  Nat.lt_of_lt_of_le hard (chain_bound length transfer overhead append m)

/-- The cross-multiplied form avoids integer division of rational rates. -/
theorem rate_telescope (cap transfer : Nat → Nat) (p q m : Nat)
    (rate : ∀ i < m, q * transfer i + p * cap i ≤ p * cap (i+1)) :
    q * total transfer m + p * cap 0 ≤ p * cap m := by
  induction m with
  | zero => simp [total]
  | succ i ih =>
    have earlier := ih (fun j hj => rate j (Nat.lt_trans hj (Nat.lt_succ_self i)))
    have step := rate i (Nat.lt_succ_self i)
    simp only [total, Nat.mul_add]
    omega

/-- If the endpoints and overhead leave room for the proposed rational
rate, some actual transfer in the chain must exceed it. -/
theorem some_expensive_step (length cap transfer overhead : Nat → Nat)
    (append : ∀ i, length (i+1) ≤ length i + transfer i + overhead i)
    (p q m : Nat) (positive : 0 < q) (hard : cap m < length m)
    (room : p * cap m + q * (length 0 + total overhead m) ≤
      q * cap m + p * cap 0) :
    ∃ i < m, p * cap (i+1) < q * transfer i + p * cap i := by
  apply Classical.byContradiction
  intro none
  have rates : ∀ i < m, q * transfer i + p * cap i ≤ p * cap (i+1) := by
    intro i hi
    apply Nat.le_of_not_lt
    intro big
    exact none ⟨i, hi, big⟩
  have all := rate_telescope cap transfer p q m rates
  have notEnough := Nat.mul_lt_mul_of_pos_left
    (expenditure length cap transfer overhead append m hard) positive
  simp only [Nat.mul_add] at room notEnough
  omega

end NativeProofReuse
