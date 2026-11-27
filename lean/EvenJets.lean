import Std

namespace EvenJets

/-- Addition and subtraction in the residue ring satisfy this one cancellation law. -/
structure SumOps (A : Type) where
  add : A → A → A
  sub : A → A → A
  cancel : ∀ a b, sub (add a b) a = b

def weight : List Bool → Nat
  | [] => 0
  | false :: xs => weight xs
  | true :: xs => weight xs + 1

/-- Evaluate squarefree coefficients by summing over the submasks of an input. -/
def zeta (o : SumOps A) (c : List Bool → A) : List Bool → A
  | [] => c []
  | false :: xs => zeta o (fun y => c (false :: y)) xs
  | true :: xs => o.add (zeta o (fun y => c (false :: y)) xs)
                          (zeta o (fun y => c (true :: y)) xs)

/-- Recover one coefficient using only differences on its Boolean subcube. -/
def invert (o : SumOps A) (v : List Bool → A) : List Bool → A
  | [] => v []
  | false :: xs => invert o (fun y => v (false :: y)) xs
  | true :: xs => invert o (fun y => o.sub (v (true :: y)) (v (false :: y))) xs

theorem invert_zeta (o : SumOps A) (a : List Bool) (c : List Bool → A) :
    invert o (zeta o c) a = c a := by
  induction a generalizing c with
  | nil => rfl
  | cons bit xs ih =>
    cases bit <;> simp [invert, zeta, o.cancel, ih]

theorem invert_on_ball (o : SumOps A) (a : List Bool) (f g : List Bool → A)
    (h : ∀ y, y.length = a.length → weight y ≤ weight a → f y = g y) :
    invert o f a = invert o g a := by
  induction a generalizing f g with
  | nil => exact h [] rfl (by decide)
  | cons b xs ih =>
    cases b
    · apply ih
      intro y len bound
      exact h (false :: y) (by simp [len]) bound
    · apply ih
      intro y len bound
      rw [h (true :: y) (by simp [len]) (by simp [weight]; omega)]
      rw [h (false :: y) (by simp [len]) (by simp [weight]; omega)]

/-- Sparse tests recover every possibly nonzero coefficient of degree at most m. -/
theorem coefficients_from_ball (o : SumOps A) (n m : Nat) (c d : List Bool → A)
    (high : ∀ y, y.length = n → m < weight y → c y = d y)
    (tests : ∀ y, y.length = n → weight y ≤ m → zeta o c y = zeta o d y)
    (a : List Bool) (len : a.length = n) : c a = d a := by
  by_cases within : weight a ≤ m
  · rw [← invert_zeta o a c, ← invert_zeta o a d]
    exact invert_on_ball o a _ _ (fun y hy wy => tests y (hy.trans len) (by omega))
  · exact high a len (by omega)

end EvenJets
