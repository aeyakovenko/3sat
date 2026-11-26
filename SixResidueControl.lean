import Std

/-! Finite differences of integer-valued functions on the cyclic group of order six. -/
namespace SixResidueControl

structure Row where
  v0 : Int
  v1 : Int
  v2 : Int
  v3 : Int
  v4 : Int
  v5 : Int
  deriving DecidableEq

def shift (f : Row) : Row := ⟨f.v1, f.v2, f.v3, f.v4, f.v5, f.v0⟩
def sub (f g : Row) : Row :=
  ⟨f.v0-g.v0, f.v1-g.v1, f.v2-g.v2, f.v3-g.v3, f.v4-g.v4, f.v5-g.v5⟩
def d1 (f : Row) : Row := sub (shift f) f
def d2 (f : Row) : Row := sub (shift (shift f)) f
def d3 (f : Row) : Row := sub (shift (shift (shift f))) f

def iterate : Nat → Row → Row
  | 0, f => f
  | n+1, f => d1 (iterate n f)

/-- The third power of D1 fixes every function in the image of D2 D3. -/
theorem difference_period (f : Row) :
    d1 (d1 (d1 (d2 (d3 f)))) = d2 (d3 f) := by
  cases f
  simp only [d1,d2,d3,shift,sub,Row.mk.injEq]
  omega

/-- The length parameter t=3q+3 gives exactly 3q+1 unit increments. -/
theorem multiple_of_three (q : Nat) (f : Row) :
    iterate (3*q+1) (d2 (d3 f)) = d1 (d2 (d3 f)) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 3*(q+1)+1 = ((3*q+1)+1)+1+1 by omega]
    change d1 (d1 (d1 (iterate (3*q+1) (d2 (d3 f))))) = _
    rw [ih]
    exact congrArg d1 (difference_period f)

def verdict (payload : Bool) : Row :=
  ⟨if payload then 1 else 0, 1, 0, 0, 0, 0⟩

/-- The common integer coefficient is a unit for either source verdict. -/
theorem top_unit (q : Nat) (payload : Bool) :
    (iterate (3*q+1) (d2 (d3 (verdict payload)))).v0 = 1 := by
  rw [multiple_of_three]
  cases payload <;> decide

def backward (f : Row) : Row := ⟨f.v5, f.v0, f.v1, f.v2, f.v3, f.v4⟩
def neg (f : Row) : Row := ⟨-f.v0, -f.v1, -f.v2, -f.v3, -f.v4, -f.v5⟩

/-- Reversing a unit switch shifts the derivative back one residue and negates it. -/
theorem negative_increment (f : Row) : sub (backward f) f = neg (backward (d1 f)) := by
  cases f
  simp only [backward,d1,shift,sub,neg,Row.mk.injEq]
  omega

end SixResidueControl
