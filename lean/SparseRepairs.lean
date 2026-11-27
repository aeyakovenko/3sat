import Std

namespace SparseRepairs

/-- All sites outside the touched set read only unchanged assignment bits. -/
theorem patch_sound (reads : C → V → Prop) (test : C → (V → Bool) → Prop)
    (locality : ∀ c a b, (∀ v, reads c v → a v = b v) → test c a → test c b)
    (changed : V → Prop) (touched : C → Prop) (base patched : V → Bool)
    (occurrences : ∀ c v, changed v → reads c v → touched c)
    (unchanged : ∀ v, ¬ changed v → base v = patched v)
    (offList : ∀ c, ¬ touched c → test c base)
    (onList : ∀ c, touched c → test c patched) : ∀ c, test c patched := by
  classical
  intro c
  by_cases marked : touched c
  · exact onList c marked
  · apply locality c base patched _ (offList c marked)
    intro v hv
    exact unchanged v (fun h => marked (occurrences c v h hv))

/-- A consistent list of pins disjoint from the part inspected by a local
    predicate preserves both possible values at a center in the inspected set. -/
theorem remote_pins (region pinned : V → Prop) (center : V) (target : Bool)
    (values : V → Bool) (test : (V → Bool) → Prop)
    (locality : ∀ a b, (∀ v, region v → a v = b v) → test a → test b)
    (inside : region center) (disjoint : ∀ v, region v → ¬ pinned v) :
    (∃ a, test a ∧ a center = target ∧ ∀ v, pinned v → a v = values v) ↔
    ∃ a, test a ∧ a center = target := by
  classical
  constructor
  · rintro ⟨a, ha, hc, _⟩
    exact ⟨a, ha, hc⟩
  · rintro ⟨a, ha, hc⟩
    let b := fun v => if pinned v then values v else a v
    have keep : ∀ v, region v → a v = b v := by
      intro v hv
      simp [b, disjoint v hv]
    refine ⟨b, locality a b keep ha, (keep center inside).symm.trans hc, ?_⟩
    intro v hv
    simp [b, hv]

end SparseRepairs
