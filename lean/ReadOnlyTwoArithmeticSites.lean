import Std

/- An arbitrary fixed Boolean gate applies the same truth table to both
   bit positions.  This is the low-pair obstruction in the read-only proof. -/
namespace ReadOnlyTwoArithmeticSites

abbrev LowPair := Bool × Bool

def equalBits (v : LowPair) : Prop := v.1 = v.2

def bitGate (f : Bool → Bool → Bool) (p q : LowPair) : LowPair :=
  (f p.1 q.1, f p.2 q.2)

theorem gate_preserves_equal_bits (f : Bool → Bool → Bool) (p q : LowPair)
    (hp : equalBits p) (hq : equalBits q) : equalBits (bitGate f p q) := by
  change f p.1 q.1 = f p.2 q.2
  rw [show p.1 = p.2 from hp, show q.1 = q.2 from hq]

theorem iterated_gates_preserve_equal_bits (step : Nat → Bool → Bool → Bool)
    (data : Nat → LowPair) (p : Nat → LowPair)
    (init : equalBits (p 0)) (hd : ∀ i, equalBits (data i))
    (hstep : ∀ i, p (i + 1) = bitGate (step i) (p i) (data i)) :
    ∀ i, equalBits (p i) := by
  intro i
  induction i with
  | zero => exact init
  | succ i ih =>
    rw [hstep i]
    exact gate_preserves_equal_bits _ _ _ ih (hd i)

theorem two_residues_unavailable (p : LowPair) (hp : equalBits p) :
    p ≠ (true, false) ∧ p ≠ (false, true) := by
  constructor <;> rintro rfl <;> cases hp

end ReadOnlyTwoArithmeticSites
