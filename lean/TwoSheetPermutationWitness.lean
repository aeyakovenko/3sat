import Std

namespace TwoSheetPermutationWitness
set_option synthInstance.maxSize 2048

abbrev Label := Fin 9

def P (i : Label) : Label := (#[1, 7, 0, 6, 2, 3, 8, 5, 4] : Array Label)[i.val]!
def Q (i : Label) : Label := (#[2, 0, 8, 1, 3, 7, 4, 6, 5] : Array Label)[i.val]!
def z (i : Label) : Nat := #[2, 0, 0, 1, 1, 1, 1, 0, 0][i.val]!

def inverseP (i : Label) : Label := (#[2, 0, 4, 5, 8, 7, 3, 1, 6] : Array Label)[i.val]!
def inverseQ (i : Label) : Label := (#[1, 3, 0, 4, 6, 8, 7, 5, 2] : Array Label)[i.val]!

theorem permutations : ∀ i : Label,
    P (inverseP i) = i ∧ inverseP (P i) = i ∧
    Q (inverseQ i) = i ∧ inverseQ (Q i) = i := by decide

theorem simple : ∀ i : Label, i ≠ P i ∧ i ≠ Q i ∧ P i ≠ Q i := by decide

theorem no_base_solution (x : Label → Nat) :
    ¬ (∀ i, x i + x (P i) + x (Q i) = 1) := by
  intro all
  have r0 : x 0 + x 1 + x 2 = 1 := all 0
  have r1 : x 1 + x 7 + x 0 = 1 := all 1
  have r2 : x 2 + x 0 + x 8 = 1 := all 2
  have r3 : x 3 + x 6 + x 1 = 1 := all 3
  have r4 : x 4 + x 2 + x 3 = 1 := all 4
  have r5 : x 5 + x 3 + x 7 = 1 := all 5
  have r6 : x 6 + x 8 + x 4 = 1 := all 6
  have r7 : x 7 + x 5 + x 6 = 1 := all 7
  have r8 : x 8 + x 4 + x 5 = 1 := all 8
  omega

theorem two_sheets : ∀ i : Label, z i ≤ 2 ∧ z i + z (P i) + z (Q i) = 2 := by decide

def signed (i : Label) : Int := 1 - (z i : Int)
theorem additive_solution : ∀ i, signed i + signed (P i) + signed (Q i) = 1 := by decide

def liftP (i : Label) (s : Bool) : Bool :=
  s ^^ #[false, false, false, true, false, true, false, false, false][i.val]!
def liftQ (i : Label) (s : Bool) : Bool :=
  s ^^ #[false, false, false, false, true, false, true, true, true][i.val]!
def chosen (i : Label) (s : Bool) : Nat := if s.toNat < z i then 1 else 0

/-- Each local sheet map is a bijection, witnessed by its own inverse. -/
theorem sheet_bijections : ∀ i s, liftP i (liftP i s) = s ∧ liftQ i (liftQ i s) = s := by decide

/-- All eighteen rows of the actual double cover are covered exactly once. -/
theorem explicit_cover : ∀ i s,
    chosen i s + chosen (P i) (liftP i s) + chosen (Q i) (liftQ i s) = 1 := by decide

end TwoSheetPermutationWitness
