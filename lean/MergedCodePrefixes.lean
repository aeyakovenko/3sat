import Std

namespace MergedCodePrefixes

inductive QueryTree (I : Type) where
  | halt (answer : Bool)
  | test (index : I) (low high : QueryTree I)

def run {I : Type} (x : I → Bool) : QueryTree I → Bool
  | .halt b => b
  | .test i l h => if x i then run x h else run x l

def reads {I : Type} (x : I → Bool) : QueryTree I → List I
  | .halt _ => []
  | .test i l h => i :: (if x i then reads x h else reads x l)

theorem identical_answers {I : Type} (x y : I → Bool) (t : QueryTree I)
    (agree : ∀ i ∈ reads x t, x i = y i) : run x t = run y t := by
  induction t with
  | halt b => rfl
  | test j l h il ih =>
    have first : x j = y j := agree j (by simp [reads])
    cases flag : x j with
    | false =>
      have other : y j = false := first.symm.trans flag
      simp only [run, flag, other, Bool.false_eq_true, if_false]
      exact il (fun i hi => agree i (by simp [reads, flag, hi]))
    | true =>
      have other : y j = true := first.symm.trans flag
      simp only [run, flag, other, if_true]
      exact ih (fun i hi => agree i (by simp [reads, flag, hi]))

/-- Both prefixes have reached the same continuation. A changed old bit must
    occur on the genuine suffix whenever the two required verdicts differ. -/
theorem genuine_crossing {I : Type} (x y : I → Bool) (past : I → Prop)
    (t : QueryTree I) (sameOutside : ∀ i, ¬ past i → x i = y i)
    (opposite : run x t ≠ run y t) :
    ∃ i ∈ reads x t, past i ∧ x i ≠ y i := by
  classical
  apply Classical.byContradiction
  intro noWitness
  apply opposite
  apply identical_answers
  intro i hi
  by_cases changed : x i = y i
  · exact changed
  · have within : past i := Classical.byContradiction (fun outside => changed (sameOutside i outside))
    exact (noWitness ⟨i, hi, within, changed⟩).elim

end MergedCodePrefixes
