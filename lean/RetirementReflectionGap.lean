import Std

namespace RetirementReflectionGap

/-- The same rank cannot be awarded on both days. -/
theorem adjacent_losses (win : Nat → Prop)
    (once : ∀ i j, win i → win j → i = j) (j : Nat) :
    ¬win (2*j) ∨ ¬win (2*j+1) := by
  by_cases h : win (2*j)
  · right
    intro h'
    have eq := once _ _ h h'
    omega
  · exact Or.inl h

/-- Classical eventual loss follows from single retirement alone. -/
theorem eventual_loss (win : Nat → Prop)
    (once : ∀ i j, win i → win j → i = j) :
    ∃ cutoff, ∀ j, cutoff ≤ j → ¬win j := by
  by_cases h : ∃ i, win i
  · obtain ⟨i, hi⟩ := h
    refine ⟨i+1, ?_⟩
    intro j hj wj
    have eq := once i j hi wj
    omega
  · exact ⟨0, fun j _ hj => h ⟨j, hj⟩⟩

/-- The logical core of the two directions. Here badProof means that the
    theory has a contradiction proof. The arithmetization of the hypotheses
    and the finite-priority scheduling argument are outside this statement. -/
theorem never_iff_consistent (win proofWin proofLoss : Nat → Prop) (badProof : Prop)
    (signal : ∀ j, win j → badProof ∨ proofLoss j)
    (encode : ∀ j, win j → proofWin j)
    (combine : ∀ j, proofWin j → proofLoss j → badProof)
    (monitor : badProof → ∃ j, win j) :
    (∀ j, ¬win j) ↔ ¬badProof := by
  constructor
  · intro never bad
    obtain ⟨j, h⟩ := monitor bad
    exact never j h
  · intro consistent j w
    rcases signal j w with bad | negative
    · exact consistent bad
    · exact consistent (combine j (encode j w) negative)

/-- A proof of any particular tail, together with numeralwise proofs of
    every earlier loss, closes the proof of uniform nonretirement. -/
theorem no_certified_cutoff (individual tail : Nat → Prop) (uniform : Prop)
    (each : ∀ j, individual j)
    (join : ∀ cutoff, (∀ j, j < cutoff → individual j) → tail cutoff → uniform)
    (incomplete : ¬uniform) : ∀ cutoff, ¬tail cutoff :=
  fun cutoff witness => incomplete (join cutoff (fun j _ => each j) witness)

end RetirementReflectionGap
