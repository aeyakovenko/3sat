import Std

namespace CycleGroupVerdict

/-- The entries (1,2), (2,3), (1,3) of a unitriangular 3 by 3 matrix over F₂. -/
structure UT3 where
  x : Bool
  y : Bool
  z : Bool
  deriving DecidableEq

def mul (a b : UT3) : UT3 :=
  ⟨a.x ^^ b.x, a.y ^^ b.y, (a.z ^^ b.z) ^^ (a.x && b.y)⟩

def one : UT3 := ⟨false, false, false⟩

def inv (a : UT3) : UT3 := ⟨a.x, a.y, a.z ^^ (a.x && a.y)⟩

theorem mul_assoc (a b c : UT3) : mul (mul a b) c = mul a (mul b c) := by
  cases a; cases b; cases c
  decide +revert

theorem one_mul (a : UT3) : mul one a = a := by
  cases a; decide +revert

theorem mul_one (a : UT3) : mul a one = a := by
  cases a; decide +revert

theorem left_inverse (a : UT3) : mul (inv a) a = one := by
  cases a; decide +revert

theorem right_inverse (a : UT3) : mul a (inv a) = one := by
  cases a; decide +revert

/-- The determinant of the two horizontal vectors in F₂². -/
def det (a b : UT3) : Bool := (a.x && b.y) ^^ (a.y && b.x)

/-- Add a bit to the central coordinate. -/
def shift (d : Bool) (a : UT3) : UT3 := ⟨a.x, a.y, a.z ^^ d⟩

theorem shift_mul (d : Bool) (a b : UT3) : mul (shift d a) b = shift d (mul a b) := by
  cases a; cases b; decide +revert

theorem mul_shift (d : Bool) (a b : UT3) : mul a (shift d b) = shift d (mul a b) := by
  cases a; cases b; decide +revert

theorem mul_swap (a b : UT3) : mul b a = shift (det a b) (mul a b) := by
  cases a; cases b; decide +revert

def product : List UT3 → UT3
  | [] => one
  | a :: as => mul a (product as)

theorem product_append (as bs : List UT3) : product (as ++ bs) = mul (product as) (product bs) := by
  induction as with
  | nil => simp [product, one_mul]
  | cons a as ih => simp [product, ih, mul_assoc]

/-- A contiguous block transposition leaves both horizontal coordinates unchanged
    and adds the horizontal determinant to the central coordinate, in any context. -/
theorem block_swap (pre u v post : List UT3) :
    product (pre ++ v ++ u ++ post) =
      shift (det (product u) (product v)) (product (pre ++ u ++ v ++ post)) := by
  simp only [product_append]
  rw [mul_assoc (product pre) (product v) (product u),
      mul_assoc (product pre) (product u) (product v),
      mul_swap (product u) (product v), mul_shift, shift_mul]

theorem verdict_swap (pre u v post : List UT3) :
    (product (pre ++ v ++ u ++ post)).z =
      ((product (pre ++ u ++ v ++ post)).z ^^ det (product u) (product v)) := by
  exact congrArg UT3.z (block_swap pre u v post)

end CycleGroupVerdict
