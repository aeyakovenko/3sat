import Std.Tactic.BVDecide

namespace PackedCubic

structure Bits where
  a : Bool
  b : Bool
  c : Bool

def add (x y : Bits) : Bits := ⟨x.a ^^ y.a, x.b ^^ y.b, x.c ^^ y.c⟩

def monomial (x : Bits) : Bool := x.a && x.b && x.c

def derivative (f : Bits → Bool) (direction x : Bits) : Bool :=
  f (add x direction) ^^ f x

/-- Third differences of a product of three affine bits on three independent
    input blocks. Directions are the linear parts evaluated at block differences. -/
theorem mixedThird (x y z base : Bits) :
    derivative (derivative (derivative monomial x) y) z base =
      ((x.a && y.b && z.c) ^^ (x.a && z.b && y.c) ^^
       (y.a && x.b && z.c) ^^ (y.a && z.b && x.c) ^^
       (z.a && x.b && y.c) ^^ (z.a && y.b && x.c)) := by
  rcases x with ⟨_, _, _⟩
  rcases y with ⟨_, _, _⟩
  rcases z with ⟨_, _, _⟩
  rcases base with ⟨_, _, _⟩
  simp only [derivative, monomial, add]
  bv_decide

def sign (b : Bool) : Int := if b then -1 else 1

/-- The numerator of the eight-term quadratic-phase expansion at a point. -/
def translatedSum (x : Bits) : Int :=
  ([false, true].flatMap fun a =>
    [false, true].flatMap fun b =>
      [false, true].map fun c =>
        sign (derivative monomial ⟨a, b, c⟩ x)).sum

theorem cubicExpansion (a b c : Bool) :
    translatedSum ⟨a, b, c⟩ = 6 * sign (monomial ⟨a, b, c⟩) := by
  cases a <;> cases b <;> cases c <;> decide

end PackedCubic
