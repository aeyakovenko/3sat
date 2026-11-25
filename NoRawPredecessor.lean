import Std

namespace NoRawPredecessor

/-- Counts for a base run. Producers are charged for their first distinct
    address. Each selected load has a used register definition. The two
    incidence inequalities are hypotheses about the concrete trace and ISA. -/
structure Counts (m G R T s d b H j : Nat) : Prop where
  time : m + G + R ≤ T
  stock : m ≤ G + s
  noRaw : d ≤ s + b + H * (s + R + 1)
  uses : m + b ≤ 2*R + G + j

/-- With b a count of zero-selected-input producers, this is the additive
    form of the consumer bound that refers to the other G-b producers. -/
theorem uses_from_sub (zeroPart : b ≤ G) (h : m ≤ 2*R + (G-b) + j) :
    m+b ≤ 2*R+G+j := by omega

def denom (H : Nat) : Nat := 16*(H+2)
def overhead (s H j : Nat) : Nat := 16*(2*(H+1)*s+j+H)

/-- Paying the stock deficit m-G only once in the producer budget saves a
    stock term. No assumption about word operations is embedded in the algebra. -/
theorem target_cost (h : Counts m G R T s d b H j) :
    (H+2)*(2*m) + d ≤ (H+2)*T + 2*(H+1)*s + j + H := by
  obtain ⟨time, stock, targets, uses⟩ := h
  have charged := Nat.mul_le_mul_left (H+2) time
  have missing := Nat.mul_le_mul_left (H+1) stock
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.one_mul, Nat.mul_one] at charged missing targets ⊢
  rw [show H*(2*m) = 2*(H*m) by ac_rfl]
  omega

/-- Integer form of a lower bound with leading coefficient 2+1/(16(H+2)). -/
theorem scaled_cost (h : Counts m G R T s d b H j) (fraction : m ≤ 16*d) :
    (2*denom H+1)*m ≤ denom H*T + overhead s H j := by
  have scaled := Nat.mul_le_mul_left 16 (target_cost h)
  calc
    (2*denom H+1)*m = 16*((H+2)*(2*m)) + m := by
      rw [Nat.add_mul, Nat.one_mul]
      unfold denom
      ac_rfl
    _ ≤ 16*((H+2)*(2*m)) + 16*d := Nat.add_le_add_left fraction _
    _ = 16*((H+2)*(2*m)+d) := (Nat.mul_add ..).symm
    _ ≤ _ := by
      unfold denom overhead
      rw [Nat.mul_assoc 16 (H+2) T]
      simpa only [Nat.mul_add, Nat.add_assoc] using scaled

/-- Keep half the excess coefficient to absorb the stock and input padding. -/
def cutoff (H s j padding : Nat) : Nat :=
  (4*denom H+1)*padding + 2*overhead s H j

theorem beyond_two (h : Counts m G R T s d b H j) (fraction : m ≤ 16*d)
    (layout : words ≤ m+padding) (margin : cutoff H s j padding < m) :
    (4*denom H+1)*words < (2*denom H)*T := by
  have doubled := Nat.mul_le_mul_left 2 (scaled_cost h fraction)
  have size := Nat.mul_le_mul_left (4*denom H+1) layout
  unfold cutoff at margin
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.one_mul] at doubled size margin ⊢
  omega

/-- Two more immediate operands can be paid for by a constant increment of
    marked words when the instruction set, double-input bound and layout stay fixed. -/
theorem cutoff_two_more (H s j padding : Nat) :
    cutoff H (s+2) j padding = cutoff H s j padding + 128*(H+1) := by
  simp only [cutoff, overhead, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  omega

theorem lift_one_slot (h : Counts m' G R T (s+2) d b H j) (fraction : m' ≤ 16*d)
    (layout : words ≤ m'+padding) (old : cutoff H s j padding < m)
    (additional : m+128*(H+1) ≤ m') : (4*denom H+1)*words < (2*denom H)*T := by
  apply beyond_two h fraction layout
  rw [cutoff_two_more]
  omega

end NoRawPredecessor
