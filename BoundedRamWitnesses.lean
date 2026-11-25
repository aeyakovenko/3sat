import Std

namespace BoundedRamWitnesses

/-- The clock coefficient may be encoded in the program package. 'bad' can
    mean wrong verdict or failure to halt by the package's deadline. -/
theorem finite_suite_iff {Input : Type} (bits : Input → Nat) (bad : Nat → Input → Prop) :
    (∀ p, ∃ x, bad p x) ↔
    ∀ s, ∃ H, ∀ p, p ≤ s → ∃ x, bits x ≤ H ∧ bad p x := by
  constructor
  · intro witnesses s
    induction s with
    | zero =>
      obtain ⟨x, hx⟩ := witnesses 0
      exact ⟨bits x, fun p hp => by
        have : p = 0 := by omega
        subst p
        exact ⟨x, Nat.le_refl _, hx⟩⟩
    | succ s ih =>
      obtain ⟨H, prev⟩ := ih
      obtain ⟨x, hx⟩ := witnesses (s+1)
      refine ⟨max H (bits x), ?_⟩
      intro p hp
      by_cases h : p ≤ s
      · obtain ⟨y, hy, hb⟩ := prev p h
        exact ⟨y, Nat.le_trans hy (Nat.le_max_left _ _), hb⟩
      · have : p = s+1 := by omega
        subst p
        exact ⟨x, Nat.le_max_right _ _, hx⟩
  · intro suites p
    obtain ⟨_, all⟩ := suites p
    obtain ⟨x, _, h⟩ := all p (Nat.le_refl _)
    exact ⟨x, h⟩

/-- Worst-case asymptotic exclusion asks for an individual witness for each
    multiplier and each lower bound on input length. -/
theorem no_eventual_clock_iff {Input : Type} (bits time : Input → Nat) :
    (¬ ∃ C B : Nat, 0 < C ∧ ∀ x, B ≤ bits x → time x ≤ C * bits x) ↔
    ∀ C B : Nat, 0 < C → ∃ x, B ≤ bits x ∧ C * bits x < time x := by
  classical
  constructor
  · intro no C B hC
    apply Classical.byContradiction
    intro none
    apply no
    refine ⟨C, B, hC, ?_⟩
    intro x hB
    apply Nat.le_of_not_gt
    exact fun ht => none ⟨x, hB, ht⟩
  · intro find has
    obtain ⟨C, B, hC, bound⟩ := has
    obtain ⟨x, hB, ht⟩ := find C B hC
    exact (Nat.not_lt_of_ge (bound x hB)) ht

end BoundedRamWitnesses

namespace BoundedRamWitnesses

/-- Bits of code are not needed for this accounting lemma: s is a bound on
    stored instructions with at most two immediate numeric operands each. -/
theorem address_charge {s d k reads makers time : Nat}
    (visits : k ≤ reads) (sources : k ≤ 2*s+d+makers)
    (separate : reads+makers ≤ time) (enough : 4*s+2*d ≤ k) :
    3*k ≤ 2*time := by omega

/-- Four further required word positions pay for the two extra immediates
    that an arbitrary additional stored instruction can supply. -/
theorem extend_required_words {s d k : Nat} (h : 4*s+2*d ≤ k) :
    4*(s+1)+2*d ≤ k+4 := by omega

end BoundedRamWitnesses
