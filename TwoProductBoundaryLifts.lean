import Std

namespace TwoProductBoundaryLifts

variable {ι : Type}

def dot : List ι → (ι → Bool) → (ι → Bool) → Bool
  | [], _, _ => false
  | k :: ks, a, b => (a k && b k) ^^ dot ks a b

def addVec (a b : ι → Bool) : ι → Bool := fun k => a k ^^ b k

def corners (a b c d : Bool) : Bool := (a ^^ b) ^^ (c ^^ d)

private theorem corners_xor : ∀ a b c d e f g h : Bool,
    corners (a ^^ e) (b ^^ f) (c ^^ g) (d ^^ h) =
      (corners a b c d ^^ corners e f g h) := by decide

private theorem one_column : ∀ a b x y z w : Bool,
    corners (a && b) ((a ^^ x) && (b ^^ y)) ((a ^^ z) && (b ^^ w))
      (((a ^^ x) ^^ z) && ((b ^^ y) ^^ w)) = ((x && w) ^^ (z && y)) := by decide

private theorem interchange : ∀ a b c d : Bool,
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by decide

private theorem equal_of_xor_zero : ∀ a b : Bool, (a ^^ b) = false → a = b := by decide

/-- The four products at the vertices of a translated affine square retain
    exactly the two mixed products, for any list of middle indices. -/
theorem dot_polarization (ks : List ι) (a b x y z w : ι → Bool) :
    corners (dot ks a b)
      (dot ks (addVec a x) (addVec b y))
      (dot ks (addVec a z) (addVec b w))
      (dot ks (addVec (addVec a x) z) (addVec (addVec b y) w)) =
      (dot ks x w ^^ dot ks z y) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [dot, corners_xor, ih, addVec, one_column]
    exact interchange _ _ _ _

abbrev Matrix (ι : Type) := ι → ι → Bool

def addMat (a b : Matrix ι) : Matrix ι := fun i j => a i j ^^ b i j

def mul (ks : List ι) (a b : Matrix ι) : Matrix ι :=
  fun i j => dot ks (a i) (fun k => b k j)

/-- When the four products close up in the output coordinates of a matrix
    product graph, the mixed products agree as matrices. -/
theorem mixed_products_equal (ks : List ι) (a b x y z w : Matrix ι)
    (square : ∀ i j, corners (mul ks a b i j)
      (mul ks (addMat a x) (addMat b y) i j)
      (mul ks (addMat a z) (addMat b w) i j)
      (mul ks (addMat (addMat a x) z) (addMat (addMat b y) w) i j) = false) :
    mul ks x w = mul ks z y := by
  funext i j
  have pol := dot_polarization ks (a i) (fun k => b k j)
    (x i) (fun k => y k j) (z i) (fun k => w k j)
  have h : (mul ks x w i j ^^ mul ks z y i j) = false := pol.symm.trans (square i j)
  exact equal_of_xor_zero _ _ h

/-- With the simultaneous identity shift as one direction, the two entries
    of the other direction must be the same matrix. -/
theorem identity_shift (ks : List ι) (a b x y unit : Matrix ι)
    (right_identity : mul ks x unit = x) (left_identity : mul ks unit y = y)
    (square : ∀ i j, corners (mul ks a b i j)
      (mul ks (addMat a x) (addMat b y) i j)
      (mul ks (addMat a unit) (addMat b unit) i j)
      (mul ks (addMat (addMat a x) unit) (addMat (addMat b y) unit) i j) = false) :
    x = y :=
  right_identity.symm.trans ((mixed_products_equal ks a b x y unit unit square).trans left_identity)

theorem diagonal_directions_commute (ks : List ι) (a b x z : Matrix ι)
    (square : ∀ i j, corners (mul ks a b i j)
      (mul ks (addMat a x) (addMat b x) i j)
      (mul ks (addMat a z) (addMat b z) i j)
      (mul ks (addMat (addMat a x) z) (addMat (addMat b x) z) i j) = false) :
    mul ks x z = mul ks z x :=
  mixed_products_equal ks a b x x z z square

end TwoProductBoundaryLifts
