import Std

/-! Sharing a full model among marked files and the exact semantics of the
one-way counter used to extend the edit cube by one position. -/
namespace EditWitnessBanks

def Independent {V E : Type} (inc : E → V → Prop) (support : V → Prop) : Prop :=
  ∀ e, ¬ (∀ v, inc e v → support v)

def HasBank {V E : Type} (inc : E → V → Prop) (Color : Type) : Prop :=
  ∃ bank : Color → V → Prop,
    (∀ c, Independent inc (bank c)) ∧ ∀ v, ∃ c, bank c v

theorem bank_iff_coloring {V E Color : Type} (inc : E → V → Prop) :
    HasBank inc Color ↔
      ∃ paint : V → Color, ∀ c, Independent inc (fun v => paint v = c) := by
  constructor
  · rintro ⟨bank, valid, covers⟩
    let paint := fun v => Classical.choose (covers v)
    have mem (v : V) : bank (paint v) v := Classical.choose_spec (covers v)
    refine ⟨paint, fun c e bad => valid c e ?_⟩
    intro v hv
    rw [← bad v hv]
    exact mem v
  · rintro ⟨paint, proper⟩
    exact ⟨fun c v => paint v = c, proper, fun v => ⟨paint v, rfl⟩⟩

def count (value : Nat → Bool) : Nat → Nat
  | 0 => 0
  | i+1 => count value i + (if value i then 1 else 0)

theorem count_mono (v : Nat → Bool) (i b : Nat) (h : i ≤ b) :
    count v i ≤ count v b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- Column zero is hardwired true. Only columns through k+1 are inspected. -/
structure Checks (v : Nat → Bool) (b k : Nat) (r : Nat → Nat → Prop) : Prop where
  zero : ∀ i ≤ b, r i 0
  keep : ∀ i < b, ∀ j ≤ k+1, r i j → r (i+1) j
  step : ∀ i < b, ∀ j ≤ k, v i = true → r i j → r (i+1) (j+1)
  cap : ∀ i ≤ b, ¬ r i (k+1)

theorem propagates {v b k r} (checks : Checks v b k r) (i : Nat) (hi : i ≤ b) :
    ∀ j ≤ k+1, j ≤ count v i → r i j := by
  induction i with
  | zero =>
    intro j _ bound
    simp [count] at bound
    subst j
    exact checks.zero 0 hi
  | succ i ih =>
    intro j limit bound
    have prev : i < b := by omega
    cases j with
    | zero => exact checks.zero _ hi
    | succ j =>
      cases bit : v i with
      | false =>
        simp [count, bit] at bound
        exact checks.keep i prev _ limit (ih (by omega) _ limit bound)
      | true =>
        simp [count, bit] at bound
        exact checks.step i prev j (by omega) bit (ih (by omega) j (by omega) (by omega))

theorem counter_iff (v : Nat → Bool) (b k : Nat) :
    (∃ r, Checks v b k r) ↔ count v b ≤ k := by
  constructor
  · rintro ⟨r, h⟩
    have under : ¬ k+1 ≤ count v b := fun tooMany =>
      h.cap b (by omega) (propagates h b (by omega) (k+1) (by omega) tooMany)
    omega
  · intro cap
    refine ⟨fun i j => j ≤ count v i, ?_⟩
    constructor
    · intros; exact Nat.zero_le _
    · intro i _ j _ seen
      exact Nat.le_trans seen (Nat.le_add_right _ _)
    · intro i _ j _ bit seen
      simpa [count, bit] using Nat.succ_le_succ seen
    · intro i hi over
      have lower := count_mono v i b hi
      change k+1 ≤ count v i at over
      omega

#print axioms bank_iff_coloring
#print axioms counter_iff
end EditWitnessBanks
