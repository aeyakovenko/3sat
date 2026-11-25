import Std

namespace ParityPinRectangles

variable {V E I : Type}

/-- Vertex coordinates carry independent bits and edge coordinates carry their parities. -/
def Valid (u v : E → V) (a : Sum V E → Bool) : Prop :=
  ∀ e, a (.inr e) = Bool.xor (a (.inl (u e))) (a (.inl (v e)))

/-- Take the left coordinates from the first input and the right coordinates from the second. -/
def mix (left : Sum V E → Bool) (a b : Sum V E → Bool) : Sum V E → Bool :=
  fun z => if left z then a z else b z

def Rectangle (left : Sum V E → Bool) (member : (Sum V E → Bool) → Prop) : Prop :=
  ∀ a b, member a → member b → member (mix left a b)

/-- The edge bit and one endpoint are on the same side of the cut.
    Select the endpoint on the other side, with u on the left and v on the right. -/
def opposite (left : Sum V E → Bool) (u v : E → V) (e : E) : V :=
  if left (.inr e) then v e else u e

private theorem xor_left_cancel {a b c : Bool}
    (h : Bool.xor a b = Bool.xor a c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem xor_right_cancel {a b c : Bool}
    (h : Bool.xor a c = Bool.xor b c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Two original inputs and just one of the two coordinate exchanges already fix the
    opposite endpoint at every oriented crossing edge. -/
theorem mixed_edge_fixes_opposite (left : Sum V E → Bool) (u v : E → V)
    (a b : Sum V E → Bool) (e : E)
    (hu : left (.inl (u e)) = true) (hv : left (.inl (v e)) = false)
    (ha : Valid u v a) (hb : Valid u v b) (hm : Valid u v (mix left a b)) :
    a (.inl (opposite left u v e)) = b (.inl (opposite left u v e)) := by
  cases he : left (.inr e) with
  | false =>
    have h := hm e
    simp only [mix, he, hu, hv, Bool.false_eq_true, if_false, if_true] at h
    simpa [opposite, he] using xor_right_cancel (h.symm.trans (hb e))
  | true =>
    have h := hm e
    simp only [mix, he, hu, hv, Bool.false_eq_true, if_false, if_true] at h
    simpa [opposite, he] using xor_left_cancel ((ha e).symm.trans h)

/-- A matching across the cut is indexed by any type I. A nonempty accepting rectangle
    fixes one distinct vertex bit per index, with the first member supplying their values. -/
theorem matching_fixes_distinct_bits (left : Sum V E → Bool) (u v : E → V)
    (edge : I → E) (hu : ∀ i, left (.inl (u (edge i))) = true)
    (hv : ∀ i, left (.inl (v (edge i))) = false)
    (disjoint : ∀ i j z, (z = u (edge i) ∨ z = v (edge i)) →
      (z = u (edge j) ∨ z = v (edge j)) → i = j)
    (member : (Sum V E → Bool) → Prop) (rect : Rectangle left member)
    (sound : ∀ a, member a → Valid u v a)
    (base : Sum V E → Bool) (hbase : member base) :
    (∀ i j, opposite left u v (edge i) = opposite left u v (edge j) → i = j) ∧
    (∀ a, member a → ∀ i, base (.inl (opposite left u v (edge i))) =
      a (.inl (opposite left u v (edge i)))) := by
  have endpoint (i : I) : opposite left u v (edge i) = u (edge i) ∨
      opposite left u v (edge i) = v (edge i) := by
    cases he : left (.inr (edge i)) <;> simp [opposite, he]
  constructor
  · intro i j eq
    exact disjoint i j _ (endpoint i) (eq ▸ endpoint j)
  · intro a ha i
    exact mixed_edge_fixes_opposite left u v base a (edge i) (hu i) (hv i)
      (sound base hbase) (sound a ha) (sound _ (rect base a hbase ha))

end ParityPinRectangles
