import Std

namespace FingerprintWitnessOrder

/-- If every row has an isolating challenge, its challenge and fingerprint
    together encode that row injectively. -/
theorem common_collision {Row Seed Digest : Type} (fingerprint : Seed → Row → Digest)
    (noCode : ∀ f : Row → Seed × Digest, ¬ (∀ x y, f x = f y → x = y)) :
    ∃ x, ∀ s, ∃ y, y ≠ x ∧ fingerprint s y = fingerprint s x := by
  classical
  apply Classical.byContradiction
  intro fail
  have isolated : ∀ x, ∃ s, ∀ y, fingerprint s y = fingerprint s x → y = x := by
    intro x
    apply Classical.byContradiction
    intro noSeed
    apply fail
    refine ⟨x, ?_⟩
    intro s
    apply Classical.byContradiction
    intro noOther
    apply noSeed
    refine ⟨s, ?_⟩
    intro y eq
    apply Classical.byContradiction
    intro neq
    exact noOther ⟨y, neq, eq⟩
  let seed := fun x => Classical.choose (isolated x)
  let encode := fun x => (seed x, fingerprint (seed x) x)
  apply noCode encode
  intro x y eq
  have sameSeed : seed x = seed y := congrArg Prod.fst eq
  have sameDigest : fingerprint (seed x) x = fingerprint (seed y) y := congrArg Prod.snd eq
  rw [sameSeed] at sameDigest
  exact Classical.choose_spec (isolated y) x sameDigest

/-- A matching read contribution remains matching when the unchanged
    contributions from the rest of the trace are combined with it. -/
theorem with_shared_records {Summary : Type} (combine : Summary → Summary → Summary)
    (other first second : Summary) (same : first = second) :
    combine other first = combine other second := congrArg (combine other) same

end FingerprintWitnessOrder
