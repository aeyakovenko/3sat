import Std

namespace LowRankInverseChart

/-- The chart finds a basis for the entire image. Its inverse gives a
    factorization without reading the matrix entries individually. -/
theorem reconstruct {V K : Type} (X : V → V) (A : K → V) (B : V → K) (Tinv : K → K)
    (cover : ∀ y, ∃ u, X y = X (A u))
    (left : ∀ u, Tinv (B (X (A u))) = u) (y : V) :
    X (A (Tinv (B (X y)))) = X y := by
  obtain ⟨u, hu⟩ := cover y
  rw [hu, left]

/-- A system with two unchanged occurrences of X obtains a coordinate of the
    small chart. In a binary linear space its right equation is equivalent
    to B (X (A z + R y)) = 0. -/
theorem uniqueReply {V K : Type} (X R : V → V) (A : K → V) (B : V → K)
    (Tinv : K → K) (left : ∀ u, Tinv (B (X (A u))) = u)
    (right : ∀ u, B (X (A (Tinv u))) = u) (i z : K) :
    B (X (A z)) = B (X (R (X (A i)))) ↔
      z = Tinv (B (X (R (X (A i))))) := by
  constructor
  · intro h
    rw [← left z, h]
  · intro h
    rw [h, right]

private def total (domain : List α) (f : α → Nat) : Nat := (domain.map f).sum

private theorem totalAdd (xs : List α) (f g : α → Nat) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    change (f a + g a) + total xs _ = (f a + total xs f) + (g a + total xs g)
    rw [ih]
    omega

private theorem totalZero (xs : List α) : total xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change 0 + total xs (fun _ => 0) = 0
    rw [Nat.zero_add, ih]

private theorem swapSums (xs : List α) (ys : List β) (f : α → β → Nat) :
    total xs (fun x => total ys (f x)) = total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil => exact (totalZero ys).symm
  | cons a xs ih =>
    change total ys (f a) + total xs (fun x => total ys (f x)) =
      total ys (fun y => f a y + total xs (fun x => f x y))
    rw [totalAdd, ih]

/-- Cyclic parity of a product of rectangular binary matrices, of independently
    indexed sizes. Computing integer sums first then reducing modulo two gives
    the same parity as matrix operations over the binary field. -/
theorem cyclicParity (xs : List α) (ys : List β) (u : α → β → Nat) (v : β → α → Nat) :
    total xs (fun x => total ys (fun y => u x y * v y x)) % 2 =
    total ys (fun y => total xs (fun x => v y x * u x y)) % 2 := by
  rw [swapSums xs ys]
  simp only [Nat.mul_comm]

end LowRankInverseChart
