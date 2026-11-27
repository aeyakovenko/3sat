import Std

namespace PrefixLengthMass

/-- A finite prefix code drawn within a complete binary tree of depth L.
    The weight at a selected leaf is measured in units of 2^(-L). -/
inductive CodeTree : Nat → Type where
  | unused (depth : Nat) : CodeTree depth
  | selected {depth : Nat} (charge : Nat) (bounded : 2 * charge ≤ 2^depth) :
      CodeTree depth
  | fork {depth : Nat} (left right : CodeTree depth) : CodeTree (depth+1)

def total {depth : Nat} : CodeTree depth → Nat
  | .unused _ => 0
  | .selected charge _ => charge
  | .fork left right => total left + total right

theorem finite_kraft_charge {depth : Nat} (code : CodeTree depth) :
    2 * total code ≤ 2^depth := by
  induction code with
  | unused d => simp [total]
  | selected charge bounded => exact bounded
  | @fork d left right ihLeft ihRight =>
    simp only [total, Nat.pow_succ]
    omega

/-- The program uses fewer bits than its output. Charge one depth-L
    cell per unit of normalized output mass. -/
theorem leaf_charge {p m L : Nat} (shorter : p < m) (depth : m ≤ L) :
    2 * 2^(L-m) ≤ 2^(L-p) := by
  rw [Nat.mul_comm 2, ← Nat.pow_succ]
  exact Nat.pow_le_pow_right (by decide) (by omega)

def blockWeight (L j : Nat) (data : List (Nat × Nat)) : Nat :=
  (data.map (fun entry => if 2^(entry.1-j) ≤ entry.2 then 2^(L-j) else 0)).sum

def outputWeight (L : Nat) (data : List (Nat × Nat)) : Nat :=
  (data.map (fun entry => entry.2 * 2^(L-entry.1))).sum

/-- Each entry is (output length m, first missing index). When m is heavy
    in its block, charge 2^(-j) against that length's mass. -/
theorem block_charge {L j : Nat} (data : List (Nat × Nat))
    (bounds : ∀ entry ∈ data, j ≤ entry.1 ∧ entry.1 ≤ L) :
    blockWeight L j data ≤ outputWeight L data := by
  induction data with
  | nil => simp [blockWeight,outputWeight]
  | cons entry tail ih =>
    have b := bounds entry (by simp)
    have htail := ih (fun item hi => bounds item (by simp [hi]))
    change (if 2^(entry.1-j) ≤ entry.2 then 2^(L-j) else 0) +
      blockWeight L j tail ≤ entry.2 * 2^(L-entry.1) + outputWeight L tail
    apply Nat.add_le_add _ htail
    split
    next h =>
      have hexp : L-j = (entry.1-j)+(L-entry.1) := by omega
      rw [hexp, Nat.pow_add]
      exact Nat.mul_le_mul_right _ h
    next _ => exact Nat.zero_le _

theorem decoder_is_short {tag lengthCode parameterCode rankBits j d m : Nat}
    (rankLength : rankBits + lengthCode + d = j)
    (room : j ≤ m) (saves : tag + parameterCode < d) :
    tag + lengthCode + parameterCode + rankBits + (m-j) < m := by omega

/-- k is encoded, the block index is recovered by search, and the offset
    uses an extra bit for the inclusive endpoint of the prefix. -/
theorem block_decoder_is_short {tag parameterCode j k m : Nat}
    (fits : k ≤ j) (room : j ≤ m) (saves : tag + parameterCode + 1 < k) :
    tag + parameterCode + (j-k+1) + (m-j) < m := by omega

end PrefixLengthMass
