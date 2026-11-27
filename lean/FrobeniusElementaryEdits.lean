import Std

namespace FrobeniusElementaryEdits

variable {ι : Type u} [DecidableEq ι]

abbrev BinaryMap (ι : Type u) := (ι → Bool) → ι → Bool

def transvection (i j : ι) : BinaryMap ι :=
  fun v k => if k = i then (v k ^^ v j) else v k

def unitMap (i j : ι) : BinaryMap ι :=
  fun v k => if k = i then v j else false

def plus (P Q : BinaryMap ι) : BinaryMap ι :=
  fun v k => P v k ^^ Q v k

/-- Binary span of maps obtained by at most two elementary row additions. -/
inductive Spanned : BinaryMap ι → Prop where
  | identity : Spanned id
  | single (i j : ι) (h : i ≠ j) : Spanned (transvection i j)
  | double (i j p q : ι) (h : i ≠ j) (h' : p ≠ q) :
      Spanned (transvection i j ∘ transvection p q)
  | add {p q : BinaryMap ι} : Spanned p → Spanned q → Spanned (plus p q)

theorem off_diagonal (i j : ι) : plus id (transvection i j) = unitMap i j := by
  funext v k
  by_cases h : k = i
  · subst k
    cases h₁ : v i <;> cases h₂ : v j <;> simp [plus, transvection, unitMap, h₁, h₂]
  · simp [plus, transvection, unitMap, h]

theorem diagonal (i j : ι) (hij : i ≠ j) :
    plus (plus id (transvection i j))
      (plus (transvection j i) (transvection i j ∘ transvection j i)) =
    unitMap i i := by
  funext v k
  by_cases hi : k = i
  · subst k
    cases h₁ : v i <;> cases h₂ : v j <;>
      simp [plus, transvection, unitMap, Function.comp, hij, h₁, h₂]
  · by_cases hj : k = j
    · subst k
      cases h₁ : v i <;> cases h₂ : v j <;>
        simp [plus, transvection, unitMap, Function.comp, Ne.symm hij, h₁, h₂]
    · simp [plus, transvection, unitMap, Function.comp, hi, hj]

theorem every_unit (another : ∀ i : ι, ∃ j, i ≠ j) (i j : ι) :
    Spanned (unitMap i j) := by
  by_cases h : i = j
  · subst j
    obtain ⟨j, hij⟩ := another i
    rw [← diagonal i j hij]
    exact .add (.add .identity (.single i j hij))
      (.add (.single j i (Ne.symm hij)) (.double i j j i hij (Ne.symm hij)))
  · rw [← off_diagonal i j]
    exact .add .identity (.single i j h)

end FrobeniusElementaryEdits
