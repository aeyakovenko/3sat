import Std

namespace AffineCodeTwoSat

abbrev Word (I : Type) := I → Bool

def zero {I : Type} : Word I := fun _ => false

def add {I : Type} (x y : Word I) : Word I := fun i => xor (x i) (y i)

def mul {I : Type} (x y : Word I) : Word I := fun i => x i && y i

def med (a b c : Bool) := (a && b) || (a && c) || (b && c)

def majority {I : Type} (a b c : Word I) : Word I := fun i => med (a i) (b i) (c i)

/-- After translation by one accepted point, majority closure gives intersection. -/
theorem translatedIntersection {I : Type} (t x y : Word I) :
    add t (majority t x y) = mul (add t x) (add t y) := by
  funext i
  cases a : t i <;> cases b : x i <;> cases c : y i <;> simp [add, mul, majority, med, a, b, c]

private theorem distribute {I : Type} (x y z : Word I) :
    mul x (add y z) = add (mul x y) (mul x z) := by
  funext i
  cases a : x i <;> cases b : y i <;> cases c : z i <;> simp [mul, add, a, b, c]

private theorem commute {I : Type} (x y : Word I) : mul x y = mul y x := by
  funext i; simp [mul, Bool.and_comm]

private theorem timesZero {I : Type} (x : Word I) : mul x zero = zero := by
  funext i; simp [mul, zero]

inductive Span {I : Type} (S : Word I → Prop) : Word I → Prop where
  | z : Span S zero
  | gen {x} : S x → Span S x
  | plus {x y} : Span S x → Span S y → Span S (add x y)

private theorem timesGenerator {I : Type} {S : Word I → Prop}
    (closed : ∀ u v, S u → S v → S (mul u v)) {x y : Word I}
    (hx : S x) (hy : Span S y) : Span S (mul x y) := by
  induction hy with
  | z => rw [timesZero]; exact .z
  | gen h => exact .gen (closed _ _ hx h)
  | plus _ _ a b => rw [distribute]; exact .plus a b

/-- The entire binary linear span of an intersection-closed set is a ring. -/
theorem spanClosed {I : Type} {S : Word I → Prop}
    (closed : ∀ u v, S u → S v → S (mul u v)) {x y : Word I}
    (hx : Span S x) (hy : Span S y) : Span S (mul x y) := by
  induction hy with
  | z => rw [timesZero]; exact .z
  | gen h => rw [commute]; exact timesGenerator closed h hx
  | plus _ _ a b => rw [distribute]; exact .plus a b

/-- A nonzero minimal support in the ring is either wholly present or wholly
    absent from each ring word. These are the disjoint pieces used in the basis. -/
theorem atomicIntersection {I : Type} {C : Word I → Prop} {a x : Word I}
    (ha : C a) (hx : C x) (closed : ∀ u v, C u → C v → C (mul u v))
    (minimal : ∀ z, C z → (∀ i, z i = true → a i = true) → z ≠ zero → z = a) :
    mul a x = zero ∨ mul a x = a := by
  by_cases h : mul a x = zero
  · exact Or.inl h
  · exact Or.inr (minimal _ (closed _ _ ha hx) (fun i hi => by cases h : a i <;> simp_all [mul]) h)

end AffineCodeTwoSat
