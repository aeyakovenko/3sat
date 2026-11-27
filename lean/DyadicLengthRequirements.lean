import Std

namespace DyadicLengthRequirements

/-- Each requirement can claim a length in at most one block. -/
theorem earlier_claims_stop (award : Nat → Option Nat) (e : Nat) :
    ∃ cutoff, ∀ i < e, ∀ j, award i = some j → j < cutoff := by
  induction e with
  | zero => exact ⟨0, by omega⟩
  | succ e ih =>
    obtain ⟨cutoff, h⟩ := ih
    cases he : award e with
    | none =>
      refine ⟨cutoff, ?_⟩
      intro i hi j hj
      by_cases eq : i = e
      · subst i
        simp_all
      · exact h i (by omega) j hj
    | some b =>
      refine ⟨max cutoff (b + 1), ?_⟩
      intro i hi j hj
      by_cases eq : i = e
      · subst i
        have : b = j := Option.some.inj (he.symm.trans hj)
        omega
      · have old := h i (by omega) j hj
        omega

/-- A live requirement can miss an eligible block only when a smaller
    requirement claims a length there. Infinitely many opportunities suffice. -/
theorem infinite_opportunities_pay (award : Nat → Option Nat) (eligible : Nat → Prop)
    (e activation : Nat)
    (unbounded : ∀ start, ∃ j ≥ start, eligible j)
    (blocked : ∀ j ≥ activation, eligible j → award e = none →
      ∃ i < e, award i = some j) :
    ∃ b, award e = some b := by
  cases he : award e with
  | some b => exact ⟨b, rfl⟩
  | none =>
    obtain ⟨last, old⟩ := earlier_claims_stop award e
    obtain ⟨j, hj, hjEligible⟩ := unbounded (max activation last)
    obtain ⟨i, hi, hclaim⟩ := blocked j (by omega) hjEligible he
    have := old i hi j hclaim
    omega

/-- Every fast signal suppressed by a higher-priority award comes from a
    common list of at most E exceptional stages for the first E requirements. -/
theorem common_exception_list (award : Nat → Option Nat) (E : Nat)
    (suppressed : Nat → Prop)
    (charge : ∀ j, suppressed j → ∃ e < E, award e = some j) :
    ∃ stages : List Nat, stages.length ≤ E ∧ ∀ j, suppressed j → j ∈ stages := by
  refine ⟨(List.range E).filterMap award, ?_, ?_⟩
  · simpa using List.length_filterMap_le award (List.range E)
  · intro j hj
    obtain ⟨e, he, h⟩ := charge j hj
    exact List.mem_filterMap.mpr ⟨e, List.mem_range.mpr he, h⟩

/-- A proof may depend on the advertised output bit and on arbitrary extra
    data. Eventual absence for each sign gives one common cutoff. -/
theorem both_signs_stop {W : Type} (test : Bool → Nat → W → Prop)
    (bounded : ∀ b, ∃ cutoff, ∀ n ≥ cutoff, ∀ w, ¬ test b n w) :
    ∃ cutoff, ∀ n ≥ cutoff, ∀ b w, ¬ test b n w := by
  obtain ⟨lo, h₀⟩ := bounded false
  obtain ⟨hi, h₁⟩ := bounded true
  refine ⟨max lo hi, ?_⟩
  intro n hn b w
  cases b
  · exact h₀ n (by omega) w
  · exact h₁ n (by omega) w

end DyadicLengthRequirements
