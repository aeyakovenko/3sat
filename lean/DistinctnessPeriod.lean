import Std

namespace DistinctnessPeriod

def Injective {I A : Type} (f : I → A) : Prop := ∀ ⦃i j⦄, f i = f j → i = j

def swap {A : Type} [DecidableEq A] (a b x : A) : A :=
  if x = a then b else if x = b then a else x

private theorem swap_twice {A : Type} [DecidableEq A] (a b x : A) :
    swap a b (swap a b x) = x := by
  by_cases h : x = a
  · subst x
    by_cases e : b = a <;> simp_all [swap]
  · by_cases e : x = b
    · subst x
      simp [swap, h]
    · simp [swap, h, e]

private theorem injective_swap {A : Type} [DecidableEq A] (a b : A) :
    Injective (swap a b) := by
  intro i j eq
  have h := congrArg (swap a b) eq
  simpa only [swap_twice] using h

/-- In a list of distinct records, two specified distinct positions can be
assigned any two distinct alphabet symbols without increasing the alphabet. -/
theorem prescribe_two {I A : Type} [DecidableEq A] (u : I → A) (hu : Injective u)
    {i j : I} (hij : i ≠ j) {a b : A} (hab : a ≠ b) :
    ∃ x : I → A, Injective x ∧ x i = a ∧ x j = b := by
  let v := fun p => swap (u i) a (u p)
  have hv : Injective v := by
    intro c d eq
    exact hu (injective_swap (u i) a eq)
  have vi : v i = a := by simp [v, swap]
  have vj : a ≠ v j := fun eq => hij (hv (vi.trans eq))
  refine ⟨fun p => swap (v j) b (v p), ?_, ?_, ?_⟩
  · intro c d eq
    exact hv (injective_swap (v j) b eq)
  · change swap (v j) b (v i) = a
    rw [vi]
    simp [swap, vj, hab]
  · simp [swap]

/-- Any independent row-wise bijections preserving distinctness agree on every
alphabet symbol, provided one distinct list exists. Surjectivity suffices on
the row maps for this direction. -/
theorem common_relabeling {I A : Type} [DecidableEq A] (u : I → A) (hu : Injective u)
    (f : I → A → A) (onto : ∀ j a, ∃ b, f j b = a)
    (preserve : ∀ x : I → A, Injective x → Injective (fun i => f i (x i))) :
    ∀ i j a, f i a = f j a := by
  intro i j a
  by_cases same : i = j
  · subst j
    rfl
  · obtain ⟨b, hb⟩ := onto j (f i a)
    by_cases ab : a = b
    · subst b
      exact hb.symm
    · obtain ⟨x, distinct, xi, xj⟩ := prescribe_two u hu same ab
      have equal : f i (x i) = f j (x j) := by rw [xi, xj, hb]
      exact False.elim (same (preserve x distinct equal))

/-- Applied to XOR translations, equality of the row functions at zero gives
equality of the shifts. -/
theorem xor_period_common {I : Type} {w : Nat} (u : I → BitVec w) (hu : Injective u)
    (shift : I → BitVec w)
    (keep : ∀ x : I → BitVec w, Injective x →
      Injective (fun i => shift i ^^^ x i)) (i j : I) : shift i = shift j := by
  have onto (j : I) (a : BitVec w) : ∃ b, shift j ^^^ b = a := by
    refine ⟨shift j ^^^ a, ?_⟩
    simp [← BitVec.xor_assoc]
  have h := common_relabeling u hu (fun p x => shift p ^^^ x) onto keep i j 0
  simpa using h

end DistinctnessPeriod
