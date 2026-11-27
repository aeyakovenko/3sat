import Std.Tactic.BVDecide

namespace NativeEightStepPortfolios

abbrev Word := BitVec 4

def sat (p q m n : Word) : Prop :=
  (p &&& m = 0) ∧ (q &&& n = 0) ∧ (m ≠ 15 ∨ n ≠ 15)

def fetched (p q m n j : Word) : Word :=
  if j = 0 then p else if j = 1 then q else if j = 2 then m
  else if j = 3 then n else 0

def threeRows (p q m n : Word) : Prop :=
  let j := q &&& n
  let x := fetched p q m n j
  if 9 < m then m = 11 ∧ x = 4
  else if m.slt j then x = 6 else x = 8

def paired (a p q m n : Word) : Prop :=
  let j := q &&& n
  let x := fetched p q m n j
  if m = ~~~(a+1) then j = 0 ∧ x = a+1
  else m = ~~~a ∧ x = a

def eligible (a : Word) : Prop := a = 4 ∨ a = 6 ∨ a = 8 ∨ a = 10

private theorem reify (c : Prop) [Decidable c] (u v : Prop) :
    (if c then u else v) ↔ (c ∧ u) ∨ (¬c ∧ v) := by
  by_cases h : c <;> simp [h]

theorem threeRows_sound (p q m n : Word) :
    threeRows p q m n → sat p q m n := by
  unfold threeRows fetched sat
  simp only [reify]
  bv_decide

theorem paired_sound (a p q m n : Word) :
    eligible a → paired a p q m n → sat p q m n := by
  unfold eligible paired fetched sat
  simp only [reify]
  bv_decide

theorem threeRows_targets (p q : Word) (hp : 4 ≤ p ∧ p ≤ 11) (hq : 4 ≤ q ∧ q ≤ 11) :
    threeRows p q (~~~p) (~~~q) ↔ (p = 4 ∨ p = 6 ∨ p = 8) := by
  have casesP : p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 11 := by bv_decide
  rcases casesP with h | h | h | h | h | h | h | h <;> subst p <;>
    simp [threeRows, fetched] <;> decide

theorem paired_targets (a p q : Word) (ha : eligible a)
    (hp : 4 ≤ p ∧ p ≤ 11) (hq : 4 ≤ q ∧ q ≤ 11) :
    paired a p q (~~~p) (~~~q) ↔ (p = a ∨ p = a+1) := by
  unfold eligible at ha
  unfold paired fetched
  simp only [reify]
  bv_decide

end NativeEightStepPortfolios
