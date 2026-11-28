import QuadraticFixedChain
import QuadraticDefs

namespace QuadraticOrSeparation
open QuadraticFixedChain

def middle : Array Nat :=
  #[57,29,60,23,33,41,21,0,13,27,2,0,45,0,0,0,61,57,44,0,21,0,0,0,44,0,0,0,0,0,0,0]
def sixRows : Array Nat := #[15,18,19,20,23,26,27,31,39,42,44,47,50,55,56,58]
def sevenRows : Array Nat := #[31,50,51,52,55,58,59,63,71,90,92,95,114,119,120,122]

/-- Insert the OR of x₃ and x₄ between them. Its degree-two monomial is x₃x₄. -/
def orGapThree (x : Nat) : Nat :=
  x%16 + 16*(x.testBit 3 || x.testBit 4).toNat + 32*(x/16)

def orCoefficients : Array Nat := (List.range 64).toArray.map fun m =>
  match m with
  | 1 => 1 | 2 => 2 | 4 => 4 | 8 => 24 | 16 => 48 | 24 => 16 | 32 => 64 | _ => 0

theorem globally_quadratic :
    exactQuadratic middle ∧ exactQuadratic orCoefficients ∧
    valid 5 (poly middle) ∧ valid 6 orGapThree ∧
    (∀ x : Fin 64, poly orCoefficients x = orGapThree x) := by native_decide

theorem inherited :
    ((List.range 16).map (fun x => poly middle (CycleImageQuadratic.polynomial x))).mergeSort =
      sixRows.toList ∧ (sixRows.toList.map orGapThree).mergeSort = sevenRows.toList := by
  native_decide

theorem six_excludes_five : boundedSearch 6 sixRows 5 = false := by native_decide
theorem seven_excludes_six : boundedSearch 7 sevenRows 6 = false := by native_decide

/-- The rotations and reflections of coordinate positions in a cycle. -/
def dihedral (n shift : Nat) (reflection : Bool) (x : Nat) : Nat :=
  (List.range n).foldl (fun a j =>
    if x.testBit j then a ||| (1 <<< ((shift + (if reflection then n-j else j)) % n))
    else a) 0

/-- The previous affine classification gives a rotation of a gap-zero insertion
following a dihedral source symmetry. The parameters are 12 source symmetries
and 7 output rotations. -/
def affine (index x : Nat) : Nat :=
  let s := index%12
  let v := dihedral 6 (s%6) (decide (s≥6)) x
  let y := v%2 + 2*(v.testBit 0 != v.testBit 1).toNat + 4*(v/2)
  dihedral 7 (index/12) false y

def allTables := (List.range 84).map (fun i => (List.range 64).map (affine i))

theorem distinct_global_maps : allTables.eraseDups.length = 84 ∧
    (List.range 84).all (fun i => valid 6 (affine i)) = true := by native_decide

/-- On these same sixteen source masks every globally affine successor has an
image with a native six-step tree. OR at gap three raises the clock to seven. -/
theorem all_affine_images_fit_six : (List.range 84).all (fun i =>
    boundedSearch 7 (sixRows.map (affine i)) 6) = true := by native_decide

end QuadraticOrSeparation
