import Std

/-! The finite algebra behind the selected triangle. The hypotheses name the
elementary scalar identities used, so this file uses only Lean's Std library.
An inverse for each selector mass is supplied explicitly. -/

namespace SelectedTriangle

structure BitWeights (F : Type) where
  selected : Bool
  zeroMass : F
  oneMass : F

/-- Summing an independent Boolean coordinate of an AND. A selected zero
branch contributes zero; the other branches retain the suffix verdict. -/
def expectation {F : Type} [Add F] [Mul F] [OfNat F 1] :
    List (BitWeights F) → F
  | [] => 1
  | w :: ws =>
      if w.selected then w.oneMass * expectation ws
      else w.zeroMass * expectation ws + w.oneMass * expectation ws

def selectedMeans {F : Type} [Mul F] [OfNat F 1] : List (BitWeights F) → F
  | [] => 1
  | w :: ws =>
      if w.selected then w.oneMass * selectedMeans ws else selectedMeans ws

theorem integrate_bits {F : Type} [Add F] [Mul F] [OfNat F 1]
    (addMul : ∀ x y z : F, (x+y)*z = x*z+y*z)
    (oneMul : ∀ x : F, 1*x = x) (ws : List (BitWeights F))
    (norm : ∀ w ∈ ws, w.zeroMass + w.oneMass = 1) :
    expectation ws = selectedMeans ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have htail := ih (fun u hu => norm u (by simp [hu]))
    have hw := norm w (by simp)
    cases choice : w.selected <;>
      simp [expectation, selectedMeans, choice, htail, ← addMul, hw, oneMul]

section Weights
variable {F : Type} [Mul F] [OfNat F 1]
variable [Std.Associative (fun x y : F => x*y)] [Std.Commutative (fun x y : F => x*y)]

theorem cancel_cell (oneMul : ∀ x : F, 1*x = x)
    (a b c ai bi ci x y z : F) (ha : a*ai = 1) (hb : b*bi = 1)
    (hc : c*ci = 1) :
    ((a*b)*c) * ((((ai*bi)*x)*(ci*y))*z) = (x*y)*z := by
  calc
    _ = (a*ai)*((b*bi)*((c*ci)*((x*y)*z))) := by ac_rfl
    _ = _ := by simp only [ha, hb, hc, oneMul]

def triangleSum {I K J : Type} [Add F] [OfNat F 0]
    (is : List I) (ks : List K) (js : List J) (f : I → K → J → F) : F :=
  (is.map fun i => (ks.map fun k => (js.map (f i k)).sum).sum).sum

/-- Over a field take ia, ib, ic to be the inverses of the nonzero masses.
The right side is the coefficient expansion of tr(XYZ). -/
theorem weighted_triangle {I K J : Type} [Add F] [OfNat F 0]
    (oneMul : ∀ x : F, 1*x = x) (is : List I) (ks : List K) (js : List J)
    (a ia : I → F) (b ib : K → F) (c ic : J → F)
    (ha : ∀ i, a i * ia i = 1) (hb : ∀ k, b k * ib k = 1)
    (hc : ∀ j, c j * ic j = 1)
    (x : I → K → F) (y : K → J → F) (z : J → I → F) :
    triangleSum is ks js (fun i k j =>
      ((a i * b k) * c j) *
      ((((ia i * ib k) * x i k) * (ic j * y k j)) * z j i)) =
    triangleSum is ks js (fun i k j => (x i k * y k j) * z j i) := by
  apply congrArg (triangleSum is ks js)
  funext i k j
  exact cancel_cell oneMul _ _ _ _ _ _ _ _ _ (ha i) (hb k) (hc j)

end Weights

/-- Coefficients through degree three in a single formal scaling variable t. -/
structure Jet3 (F : Type) where
  c0 : F
  c1 : F
  c2 : F
  c3 : F

namespace Jet3

def cubic {F : Type} [OfNat F 0] (u : F) : Jet3 F := ⟨0, 0, 0, u⟩

/-- Truncated multiplication by t*b and by 1+t*b, respectively. -/
def timesT {F : Type} [Mul F] [OfNat F 0] (q : Jet3 F) (b : F) : Jet3 F :=
  ⟨0, q.c0*b, q.c1*b, q.c2*b⟩

def timesOnePlusT {F : Type} [Mul F] [Add F] (q : Jet3 F) (b : F) : Jet3 F :=
  ⟨q.c0, q.c1+q.c0*b, q.c2+q.c1*b, q.c3+q.c2*b⟩

/-- One weight-three Boolean vertex contributes its three selected means
at degree three. Every unselected coordinate has weight 1-t*m and is fed
to this formula as b=-m. No division, interpolation or limit is involved. -/
theorem weight_three_vertex {F : Type} [Add F] [Mul F] [OfNat F 0] [OfNat F 1]
    (zeroMul : ∀ u : F, 0*u = 0) (oneMul : ∀ u : F, 1*u = u)
    (addZero : ∀ u : F, u+0 = u) (x y z : F) (unused : List F) :
    unused.foldl timesOnePlusT
      (((timesT (⟨1,0,0,0⟩ : Jet3 F) x).timesT y).timesT z) =
      cubic ((x*y)*z) := by
  have start : (((timesT (⟨1,0,0,0⟩ : Jet3 F) x).timesT y).timesT z) =
      cubic ((x*y)*z) := by simp [timesT, cubic, oneMul, zeroMul]
  rw [start]
  induction unused with
  | nil => rfl
  | cons u us ih =>
    simpa [List.foldl_cons, timesOnePlusT, cubic, zeroMul, addZero] using ih

/-- Coefficients of a sum of vertex weights add componentwise. -/
def plus {F : Type} [Add F] (p q : Jet3 F) : Jet3 F :=
  ⟨p.c0+q.c0, p.c1+q.c1, p.c2+q.c2, p.c3+q.c3⟩

theorem sum_cubic {F : Type} [Add F] [OfNat F 0]
    (zz : (0:F)+0 = 0) (values : List F) :
    ((values.map cubic).foldr plus (cubic 0)) = cubic values.sum := by
  induction values with
  | nil => rfl
  | cons u us ih =>
    simp only [List.map_cons, List.foldr_cons, List.sum_cons, ih]
    simp [plus, cubic, zz]

end Jet3
end SelectedTriangle
