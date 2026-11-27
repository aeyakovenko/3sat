import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-! A shared collection of arbitrary feature bits is decoded affinely. Changing
one group from its default makes exactly one nondefault equality flag true.
Subtracting the default observation removes every decoder's constant term. -/

namespace DenseGroupFlagRank

abbrev Bit := ZMod 2
abbrev Flag (G : Type*) {A : Type*} (base : A) := G × {a : A // a ≠ base}

variable {G A I : Type*} [Fintype G] [Fintype A] [Fintype I]
  [DecidableEq G] [DecidableEq A]

def oneChange (base : A) (j : Flag G base) (g : G) : A :=
  if g = j.1 then j.2.val else base

omit [Fintype G] [Fintype A] [DecidableEq A] in
private theorem oneChange_eq_iff (base : A) (j l : Flag G base) :
    oneChange base j l.1 = l.2.val ↔ j = l := by
  rcases j with ⟨g, a, ha⟩
  rcases l with ⟨g', a', ha'⟩
  by_cases h : g' = g
  · subst g'
    simp [oneChange]
  · simp [oneChange, h, Ne.symm h, Ne.symm ha']

/-- Only the default payload and single-group changes need be decoded correctly.
The features may depend arbitrarily on all groups and share one index space. -/
theorem nondefault_flags_require (base : A) (feature : (G → A) → I → Bit)
    (bias : Flag G base → Bit) (coeff : Matrix I (Flag G base) Bit)
    (correct : ∀ (x : G → A), (x = (fun _ => base) ∨ ∃ j, x = oneChange base j) →
      ∀ j : Flag G base, bias j + ∑ i, feature x i * coeff i j =
        if x j.1 = j.2.val then 1 else 0) :
    Fintype.card G * (Fintype.card A - 1) ≤ Fintype.card I := by
  classical
  let diffs : Matrix (Flag G base) I Bit :=
    fun j i => feature (oneChange base j) i - feature (fun _ => base) i
  have factor : diffs * coeff = 1 := by
    ext j l
    have zero := correct (fun _ => base) (Or.inl rfl) l
    simp [Ne.symm l.2.property] at zero
    have spike := correct (oneChange base j) (Or.inr ⟨j, rfl⟩) l
    simp only [oneChange_eq_iff] at spike
    change (∑ i, (feature (oneChange base j) i - feature (fun _ => base) i) * coeff i l) =
      (1 : Matrix (Flag G base) (Flag G base) Bit) j l
    rw [Matrix.one_apply]
    simp only [sub_mul, Finset.sum_sub_distrib]
    calc
      _ = (bias l + ∑ i, feature (oneChange base j) i * coeff i l) -
            (bias l + ∑ i, feature (fun _ => base) i * coeff i l) := by abel
      _ = _ := by rw [spike, zero, sub_zero]
  have bound := (Matrix.rank_mul_le_left diffs coeff).trans (Matrix.rank_le_card_width diffs)
  rw [factor, Matrix.rank_one, Fintype.card_prod] at bound
  have card : Fintype.card {a : A // a ≠ base} = Fintype.card A - 1 := by
    rw [Fintype.card_subtype_compl (fun a : A => a = base)]
    simp
  simpa only [card] using bound

/-- For r-bit row groups and U shared feature bits the exact lower bound is
the group count times the number of nonzero words in a group. -/
theorem binary_group_bound (groups r U : Nat)
    (feature : (Fin groups → Fin r → Bool) → Fin U → Bit)
    (bias : Flag (Fin groups) (fun _ : Fin r => false) → Bit)
    (coeff : Matrix (Fin U) (Flag (Fin groups) (fun _ : Fin r => false)) Bit)
    (correct : ∀ x (j : Flag (Fin groups) (fun _ : Fin r => false)),
      bias j + ∑ i, feature x i * coeff i j =
        if x j.1 = j.2.val then 1 else 0) :
    groups * (2 ^ r - 1) ≤ U := by
  simpa using nondefault_flags_require (fun _ : Fin r => false) feature bias coeff
    (fun x _ j => correct x j)

#print axioms nondefault_flags_require
#print axioms binary_group_bound

end DenseGroupFlagRank
