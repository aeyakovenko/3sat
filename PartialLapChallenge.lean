import Std

namespace PartialLapChallenge

/-- An address-specific stream has one optional final word per transaction. -/
def latest {Word : Type} (atTime : Nat → Option Word) : Nat → Option (Nat × Word)
  | 0 => none
  | t + 1 =>
    match atTime t with
    | some value => some (t, value)
    | none => latest atTime t

theorem initialization_iff {Word : Type} (atTime : Nat → Option Word) (t : Nat) :
    latest atTime t = none ↔ ∀ k, k < t → atTime k = none := by
  induction t with
  | zero => simp [latest]
  | succ t ih =>
    cases hit : atTime t with
    | none =>
      rw [show latest atTime (t + 1) = latest atTime t by simp [latest, hit], ih]
      constructor
      · intro empty k hk
        by_cases endTime : k = t
        · simpa [endTime] using hit
        · exact empty k (by omega)
      · intro empty k hk
        exact empty k (by omega)
    | some value =>
      constructor
      · simp [latest, hit]
      · intro empty
        exact False.elim (by simpa [hit] using empty t (by omega))

theorem supplier_iff {Word : Type} (atTime : Nat → Option Word) (t p : Nat) (v : Word) :
    latest atTime t = some (p,v) ↔
      p < t ∧ atTime p = some v ∧ ∀ k, p < k → k < t → atTime k = none := by
  induction t with
  | zero => simp [latest]
  | succ t ih =>
    cases hit : atTime t with
    | none =>
      rw [show latest atTime (t + 1) = latest atTime t by simp [latest, hit], ih]
      constructor
      · rintro ⟨before, source, empty⟩
        refine ⟨by omega, source, ?_⟩
        intro k afterSource beforeEnd
        by_cases endTime : k = t
        · simpa [endTime] using hit
        · exact empty k afterSource (by omega)
      · rintro ⟨before, source, empty⟩
        have different : p ≠ t := by
          rintro rfl
          simp [hit] at source
        exact ⟨by omega, source, fun k hk hkt => empty k hk (by omega)⟩
    | some value =>
      constructor
      · intro found
        have pairs : (t, value) = (p,v) := Option.some.inj (by simpa [latest, hit] using found)
        cases pairs
        exact ⟨by omega, hit, by intros; omega⟩
      · rintro ⟨before, source, empty⟩
        have sameTime : p = t := by
          apply Classical.byContradiction
          intro diff
          have nothing := empty t (by omega) (by omega)
          simp [hit] at nothing
        subst p
        have sameValue := Option.some.inj (hit.symm.trans source)
        simp [latest, hit, sameValue]

universe u

/-- One game layer includes positions of each smaller permitted root rank. -/
def valid (Sketch : Nat → Type u) (structural : (n : Nat) → Sketch n → Prop)
    (challenges : (n : Nat) → Sketch (n+1) → Sketch n → Prop) :
    (n : Nat) → Sketch n → Prop
  | 0, s => structural 0 s
  | n+1, s => structural (n+1) s ∧ ¬ ∃ a, challenges n s a ∧ valid Sketch structural challenges n a

/-- Completeness of genuine intervening rows and soundness of the local
structure suffice for any finite number of alternating challenges. -/
theorem valid_iff_authentic (Sketch : Nat → Type u) (structural auth : (n : Nat) → Sketch n → Prop)
    (challenges : (n : Nat) → Sketch (n+1) → Sketch n → Prop)
    (base : ∀ s, structural 0 s ↔ auth 0 s)
    (well : ∀ n s, auth n s → structural n s)
    (unchallenged : ∀ n s a, auth (n+1) s → challenges n s a → ¬ auth n a)
    (exposed : ∀ n s, structural (n+1) s → ¬ auth (n+1) s → ∃ a, challenges n s a ∧ auth n a) :
    ∀ n s, valid Sketch structural challenges n s ↔ auth n s := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih =>
    intro s
    change (structural (n+1) s ∧ ¬ ∃ a, challenges n s a ∧ valid Sketch structural challenges n a) ↔ _
    constructor
    · rintro ⟨okay, noCounter⟩
      apply Classical.byContradiction
      intro bad
      obtain ⟨a, attack, honest⟩ := exposed n s okay bad
      exact noCounter ⟨a, attack, (ih a).mpr honest⟩
    · intro honest
      refine ⟨well _ _ honest, ?_⟩
      rintro ⟨a, attack, legal⟩
      exact unchallenged n s a honest attack ((ih a).mp legal)

#print axioms supplier_iff
#print axioms valid_iff_authentic

end PartialLapChallenge
