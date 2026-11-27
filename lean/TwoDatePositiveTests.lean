import Std

namespace TwoDatePositiveTests

/-- A sound recurring disjunction on different dates gives one of two sound
recurring single-date detectors. The late detector may see the first verdict. -/
theorem trimPair (accepted : Nat → Nat → Nat → Prop) (positive : Nat → Prop)
    (order : ∀ i u v, accepted i u v → i ≤ u ∧ u < v)
    (sound : ∀ i u v, accepted i u v → positive u ∨ positive v)
    (recurs : ∀ n, ∃ i u v, n ≤ i ∧ accepted i u v) :
    ((∀ i u v, accepted i u v → ¬positive u → positive v) ∧
      ∀ n, ∃ i u v, n ≤ v ∧ accepted i u v ∧ ¬positive u) ∨
    (∃ cutoff, (∀ i u v, cutoff ≤ i → accepted i u v → positive u) ∧
      ∀ n, ∃ i u v, cutoff ≤ i ∧ n ≤ u ∧ accepted i u v) := by
  classical
  by_cases bad : ∀ n, ∃ i u v, n ≤ i ∧ accepted i u v ∧ ¬positive u
  · left
    constructor
    · intro i u v h no
      exact (sound i u v h).resolve_left no
    · intro n
      obtain ⟨i,u,v,hin,h,no⟩ := bad n
      obtain ⟨first,second⟩ := order i u v h
      exact ⟨i,u,v,by omega,h,no⟩
  · right
    obtain ⟨cutoff, nonePast⟩ := Classical.not_forall.mp bad
    refine ⟨cutoff, ?_, ?_⟩
    · intro i u v later h
      apply Classical.byContradiction
      intro no
      exact nonePast ⟨i,u,v,later,h,no⟩
    · intro n
      obtain ⟨i,u,v,h,hits⟩ := recurs (max n cutoff)
      have ord := (order i u v hits).1
      exact ⟨i,u,v,by omega,by omega,hits⟩

/-- Two distinct negative preemptions would have supplied one of the
joint events excluded by the local checks. -/
theorem twoPreemptions {Rank Word : Type} (first second : Rank → Word → Prop)
    (firstNeg secondNeg : Word → Prop) (isEarlier : Rank → Prop)
    (p q : Prop)
    (before₁ : ¬p → ∃ f y, isEarlier f ∧ firstNeg y ∧ first f y)
    (before₂ : ¬p → ¬q → ∃ g z, isEarlier g ∧ secondNeg z ∧ second g z)
    (retires : ∀ f g y z, first f y → second g z → f ≠ g)
    (excluded : ∀ f g y z, isEarlier f → isEarlier g → f ≠ g →
      firstNeg y → secondNeg z → ¬(first f y ∧ second g z)) : p ∨ q := by
  classical
  by_cases hp : p
  · exact Or.inl hp
  · right
    apply Classical.byContradiction
    intro hq
    obtain ⟨f,y,hf,hy,ha⟩ := before₁ hp
    obtain ⟨g,z,hg,hz,hb⟩ := before₂ hp hq
    exact excluded f g y z hf hg (retires f g y z ha hb) hy hz ⟨ha,hb⟩

end TwoDatePositiveTests
