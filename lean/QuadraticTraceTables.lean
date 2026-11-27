import Std

namespace QuadraticTraceTables

def bitCost (z : Int) : Int := z * (z - 1)

theorem bitCost_nonneg (z : Int) : 0 ≤ bitCost z := by
  by_cases h : 0 ≤ z
  · by_cases h0 : z = 0
    · simp [h0, bitCost]
    · exact Int.mul_nonneg h (by omega)
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

theorem bitCost_zero (z : Int) : bitCost z = 0 ↔ z = 0 ∨ z = 1 := by
  simp [bitCost, Int.mul_eq_zero]
  omega

def rowSum (f : α → Int) : List α → Int
  | [] => 0
  | x :: xs => f x + rowSum f xs

theorem sum_nonneg (f : α → Int) (h : ∀ x, 0 ≤ f x) (xs : List α) :
    0 ≤ rowSum f xs := by
  induction xs with
  | nil => change (0 : Int) ≤ 0; decide
  | cons x xs ih => exact Int.add_nonneg (h x) ih

theorem sum_zero_pointwise (f : α → Int) (h : ∀ x, 0 ≤ f x) (xs : List α)
    (hz : rowSum f xs = 0) : ∀ x ∈ xs, f x = 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a
    have ht := sum_nonneg f h xs
    change f a + rowSum f xs = 0 at hz
    have hf : f a = 0 := by omega
    have hs : rowSum f xs = 0 := by omega
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hf
    · exact ih hs x hx

theorem checkedBits (f : α → Int) (xs : List α)
    (hz : rowSum (fun x => bitCost (f x)) xs = 0) :
    ∀ x ∈ xs, f x = 0 ∨ f x = 1 := by
  intro x hx
  exact (bitCost_zero _).mp
    (sum_zero_pointwise _ (fun a => bitCost_nonneg (f a)) xs hz x hx)

def val (b : Bool) : Int := if b then 1 else 0

def andCost (a b z : Bool) : Int :=
  val a * val b - 2 * val a * val z - 2 * val b * val z + 3 * val z

theorem andCost_nonneg : ∀ a b z, 0 ≤ andCost a b z := by decide

theorem andCost_zero : ∀ a b z, andCost a b z = 0 ↔ z = (a && b) := by decide

theorem checkedAnd (f g h : α → Bool) (xs : List α)
    (hz : rowSum (fun x => andCost (f x) (g x) (h x)) xs = 0) :
    ∀ x ∈ xs, h x = (f x && g x) := by
  intro x hx
  exact (andCost_zero _ _ _).mp
    (sum_zero_pointwise _ (fun a => andCost_nonneg (f a) (g a) (h a)) xs hz x hx)

def sign (b : Bool) : Int := if b then -1 else 1

/-- Elimination of a coupled pair of internal binary variables. -/
theorem gauss_pair : ∀ a b : Bool,
    (1 + sign a + sign b + sign ((!a).xor b) = 2 * sign (a && b)) := by decide

/-- The one-variable sum imposes one affine equation. -/
theorem gauss_single : ∀ a : Bool, 1 + sign a = if a then 0 else 2 := by decide

/-- Every summary collision must persist at two inputs of opposite colors for this
    obstruction to rule out an exact decoder. The trace calculation supplies those inputs. -/
theorem injective_of_collision_crossing (E : α → β) (f : α → Bool) (decode : β → Bool)
    (correct : ∀ x, decode (E x) = f x)
    (crossing : ∀ x y, E x = E y → x ≠ y →
      ∃ u v, E u = E v ∧ f u ≠ f v) :
    ∀ x y, E x = E y → x = y := by
  intro x y same
  apply Classical.byContradiction
  intro distinct
  obtain ⟨u, v, huv, hcolor⟩ := crossing x y same distinct
  exact hcolor ((correct u).symm.trans ((congrArg decode huv).trans (correct v)))

end QuadraticTraceTables
