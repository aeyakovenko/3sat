import Std

namespace BalancedTripleSplit

def flips : List Bool := [false, true]

def agreePair (a b : Bool) : Nat := ((flips.flatMap fun i =>
    flips.map fun j => (i ^^ a) == (j ^^ b)).count true)

def agreeTriple (a b c : Bool) : Nat := ((flips.flatMap fun i =>
    flips.flatMap fun j => flips.map fun k =>
      ((i ^^ a) == (j ^^ b)) && ((j ^^ b) == (k ^^ c))).count true)

theorem pair_orientation_count (a b : Bool) : agreePair a b = 2 := by
  cases a <;> cases b <;> decide

theorem triple_orientation_count (a b c : Bool) : agreeTriple a b c = 2 := by
  cases a <;> cases b <;> cases c <;> decide

theorem forced_split (orientation : Bool) :
    orientation ^^ false ≠ orientation ^^ true := by cases orientation <;> decide

/-- With expectations scaled by four, the weighted pair/triple inequalities
halve the old potential even as the block count doubles. -/
theorem expected_potential (blocks triples pairs fourNextTriples fourNextPairs : Nat)
    (hTriples : fourNextTriples ≤ triples) (hPairs : fourNextPairs ≤ 2 * pairs) :
    2 * blocks * fourNextTriples + fourNextPairs ≤ 2 * (blocks * triples + pairs) := by
  calc
    _ ≤ (2 * blocks) * triples + 2 * pairs :=
      Nat.add_le_add (Nat.mul_le_mul_left (2*blocks) hTriples) hPairs
    _ = _ := by rw [Nat.mul_assoc, Nat.mul_add]

inductive Locations where
  | oneBlock
  | twoBlocks
  | threeBlocks

def exactScore (b : Nat) : Locations → Nat
  | .oneBlock => 2*b-1
  | .twoBlocks => 2
  | .threeBlocks => 0

def potential (b : Nat) : Locations → Nat
  | .oneBlock => b+3
  | .twoBlocks => 1
  | .threeBlocks => 0

theorem dominates (b : Nat) (loc : Locations) :
    exactScore b loc ≤ 2 * potential b loc := by
  cases loc <;> simp [exactScore, potential] <;> omega

def halves : List Nat → Prop
  | a::b::rest => 2*b ≤ a ∧ halves (b::rest)
  | _ => True

theorem geometric_total (a : Nat) (rest : List Nat) (h : halves (a::rest)) :
    (a::rest).sum ≤ 2*a := by
  induction rest generalizing a with
  | nil => simp; omega
  | cons b tail ih =>
    obtain ⟨first, later⟩ := h
    have bound := ih b later
    change a + (b :: tail).sum ≤ 2*a
    omega

#print axioms expected_potential
#print axioms geometric_total

end BalancedTripleSplit
