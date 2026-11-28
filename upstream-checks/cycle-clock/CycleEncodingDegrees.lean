import QuadraticDefs

namespace CycleEncodingDegrees
open CycleImageClock CycleImageQuadratic

-- In clocks four and five an affine starter has the same image as its
-- quadratic precomposition; keeping the affine parametrization simplifies
-- the quartic tables.
def baseline (k v : Nat) : Nat :=
  if k == 2 then insertBit v 1 else if k == 3 then insertBit v 0
  else encoding k v

def swapTwo (v : Nat) : Nat := if v < 2 then v ^^^ 1 else v

def cubicMap (k v : Nat) : Nat := encoding k (swapTwo v)

def quarticMap (k v : Nat) : Nat :=
  if k == 4 then if v == 5 then 21 else imageWords[v]!
  else if v == 0 then #[17,2,2,1][k]! else baseline k v

def coeff (f : Nat → Nat) (s : Nat) : Nat := (List.range 16).foldl
  (fun val x => if (x &&& s) == x then val ^^^ f x else val) 0

def degreeExactly (f : Nat → Nat) (d : Nat) : Bool :=
  (List.range 16).all (fun s => degree s ≤ d || coeff f s == 0) &&
  (List.range 16).any (fun s => degree s == d && coeff f s != 0)

theorem swap_spec : ∀ x : Fin 16, swapTwo x < 16 ∧ swapTwo (swapTwo x) = x.val ∧
    cover 4 (swapTwo x) = cover 4 x := by decide +kernel

theorem degree_profiles : ∀ k : Fin 5,
    degreeExactly (cubicMap k) 3 = true ∧ degreeExactly (quarticMap k) 4 = true ∧
    (∀ x : Fin 16, quarticMap k x < 32 ∧ cover 5 (quarticMap k x) = cover 4 x) ∧
    (∀ x y : Fin 16, quarticMap k x = quarticMap k y → x = y) := by native_decide

def quarticUpper (k v : Nat) : Bool :=
  let x := v%8
  if k == 0 then decide (2 < x) else if k == 1 then decide (4 < x) || x == 3
  else if k == 2 then affineUpper 14 v else if k == 3 then affineUpper 7 v
  else sixUpper v

theorem quartic_uppers : ∀ k : Fin 5, ∀ x : Fin 16,
    quarticUpper k (quarticMap k x) = cover 4 x := by decide +kernel

def quarticImage (k : Nat) : Array Nat := (List.range 16).toArray.map (quarticMap k)

theorem quartic_lower_two : atDepth (quarticImage 0) 1 = false := by native_decide
theorem quartic_lower_three : atDepth (quarticImage 1) 2 = false := by native_decide
theorem quartic_lower_four : atDepth (quarticImage 2) 3 = false := by native_decide
theorem quartic_lower_five : atDepth (quarticImage 3) 4 = false := by native_decide
theorem quartic_lower_six : atDepth (quarticImage 4) 5 = false := by native_decide

end CycleEncodingDegrees
