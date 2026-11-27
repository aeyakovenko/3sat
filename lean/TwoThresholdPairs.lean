import Std

namespace TwoThresholdPairs

def majority (a b c : Bool) := (a && b) || (a && c) || (b && c)

theorem clauseClosure :
    ∀ a b c u v w : Bool,
      (a || u) = true → (b || v) = true → (c || w) = true →
      (majority a b c || majority u v w) = true := by decide

theorem majorityNeg : ∀ a b c : Bool,
    majority (!a) (!b) (!c) = !(majority a b c) := by decide

theorem agreePair : ∀ a b : Bool, majority a a b = a := by decide

theorem disagreePair : ∀ a b c : Bool, a ≠ b → majority a b c = c := by decide

def middle {ι : Type} (x y z : ι → Bool) : ι → Bool :=
  fun i => majority (x i) (y i) (z i)

def inBox {ι : Type} (x y z : ι → Bool) := ∀ i, x i = y i → z i = x i

theorem middleInBox {ι : Type} (x y z : ι → Bool) : inBox x y (middle x y z) := by
  intro i hi
  simp only [middle, ← hi, agreePair]

/-- Along an edge of the box-adjacency graph of a majority-closed set, any
other model agrees with one endpoint on every changing coordinate together. -/
theorem edgeBundle {ι : Type} (points : (ι → Bool) → Prop) (x a z : ι → Bool)
    (median : points (middle x a z))
    (edge : ∀ y, points y → inBox x a y → y = x ∨ y = a) :
    (∀ i, x i ≠ a i → z i = x i) ∨ (∀ i, x i ≠ a i → z i = a i) := by
  rcases edge _ median (middleInBox x a z) with hx | ha
  · left
    intro i hdiff
    exact (disagreePair _ _ _ hdiff).symm.trans (congrFun hx i)
  · right
    intro i hdiff
    exact (disagreePair _ _ _ hdiff).symm.trans (congrFun ha i)

end TwoThresholdPairs
