import Std

namespace LinearElimination

/-- A total deterministic decision has accepting traces on true instances
    and rejecting traces on false instances. Either trace polarity can absorb
    a checker into the preceding Boolean quantifier block. -/
theorem absorb_all {U Trace : Type}
    (truth : U → Prop) (rejects : U → Trace → Prop)
    (exactReject : ∀ u, (∃ w, rejects u w) ↔ ¬ truth u) :
    (∀ u, truth u) ↔ ∀ u w, ¬ rejects u w := by
  classical
  constructor
  · intro ht u w hw
    exact (exactReject u).mp ⟨w, hw⟩ (ht u)
  · intro ht u
    exact Classical.byContradiction (fun h =>
      let ⟨w, hw⟩ := (exactReject u).mpr h
      ht u w hw)

theorem absorb_some {U Trace : Type}
    (truth : U → Prop) (accepts : U → Trace → Prop)
    (exactAccept : ∀ u, (∃ w, accepts u w) ↔ truth u) :
    (∃ u, truth u) ↔ ∃ u w, accepts u w := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨w, hw⟩ := (exactAccept u).mpr hu
    exact ⟨u, w, hw⟩
  · rintro ⟨u, w, hw⟩
    exact ⟨u, (exactAccept u).mp ⟨w, hw⟩⟩

end LinearElimination
