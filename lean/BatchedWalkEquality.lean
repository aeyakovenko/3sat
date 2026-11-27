import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Abel

namespace BatchedWalkEquality

abbrev Bit := ZMod 2
abbrev Payload (s q : Nat) := (Fin s × Fin q) → Bool

/-- The shifted shear followed by the inverse plain shear translates right.
    The plain shear followed by the inverse shifted shear translates left. -/
theorem horizontal_pair_moves {u : Nat} (x y : ZMod u) :
    (x + (y + y + 1)) - (y + y) = x + 1 ∧
    (x + (y + y)) - (y + y + 1) = x - 1 := by
  constructor <;> abel

def allGood (x y : Payload s q) : Prop := ∀ i p, x (i,p) = y (i,p)

theorem good_iff (x y : Payload s q) : allGood x y ↔ x = y := by
  constructor
  · intro h
    funext pair
    obtain ⟨i, p⟩ := pair
    exact h i p
  · rintro rfl
    exact fun _ _ => rfl

noncomputable def goodMatrix (s q : Nat) : Matrix (Payload s q) (Payload s q) Bit :=
  by classical exact fun x y => if allGood x y then 1 else 0

theorem good_rank (s q : Nat) : (goodMatrix s q).rank = 2 ^ (s*q) := by
  classical
  have ident : goodMatrix s q = 1 := by
    ext x y
    simp [goodMatrix, good_iff, Matrix.one_apply]
  rw [ident, Matrix.rank_one]
  simp

/-- All-ones squared vanishes over F₂ when the payload has positive length. -/
theorem squared_ones (s q : Nat) (h : 0 < s * q) :
    let J : Matrix (Payload s q) (Payload s q) Bit := fun _ _ => 1
    J * J = 0 := by
  classical
  intro J
  ext x y
  have hcard : Fintype.card (Payload s q) = 2 ^ (s*q) := by
    simp [Payload]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  change (J * J) x y = 0
  rw [Matrix.mul_apply]
  change (∑ _ : Payload s q, (1:Bit) * 1) = 0
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
  rw [hk, pow_succ, Nat.cast_mul]
  have two : ((2:Nat):Bit) = 0 := by decide
  rw [two, mul_zero]

theorem miss_rank (s q : Nat) (h : 0 < s * q) :
    let J : Matrix (Payload s q) (Payload s q) Bit := fun _ _ => 1
    (J - goodMatrix s q).rank = 2 ^ (s*q) := by
  classical
  intro J
  have ident : goodMatrix s q = 1 := by
    ext x y
    simp [goodMatrix, good_iff, Matrix.one_apply]
  have hneg : -(J:Matrix (Payload s q) (Payload s q) Bit) = J := by
    ext x y
    change -(1:Bit) = 1
    decide
  have square : (J - goodMatrix s q) * (J - goodMatrix s q) = 1 := by
    rw [ident, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    rw [show J*J = 0 from squared_ones s q h, zero_sub, hneg]
    abel
  have lo := Matrix.rank_mul_le_left (J - goodMatrix s q) (J - goodMatrix s q)
  rw [square, Matrix.rank_one] at lo
  have bound := le_antisymm (Matrix.rank_le_card_width _) lo
  simpa [Payload, Fintype.card_fun] using bound

#print axioms horizontal_pair_moves
#print axioms good_rank
#print axioms miss_rank

end BatchedWalkEquality
