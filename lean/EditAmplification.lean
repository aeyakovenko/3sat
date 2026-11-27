import Std

namespace EditAmplification

/-- Positive query units force C. Negative element units forbid B.
    Each database edge is the Horn implication C(q) → B(i). -/
def SatPins (edge : Q → I → Prop) (demand : Q → Prop) (forbid : I → Prop) : Prop :=
  ∃ (c : Q → Prop) (b : I → Prop),
    (∀ q, demand q → c q) ∧ (∀ i, forbid i → ¬ b i) ∧ (∀ q i, c q → edge q i → b i)

theorem satPins_iff (edge : Q → I → Prop) (demand : Q → Prop) (forbid : I → Prop) :
    SatPins edge demand forbid ↔ ∀ q i, demand q → forbid i → ¬ edge q i := by
  constructor
  · rintro ⟨c, b, hc, hb, he⟩ q i hq hi hqi
    exact hb i hi (he q i (hc q hq) hqi)
  · intro clean
    refine ⟨demand, fun i => ∃ q, demand q ∧ edge q i, fun _ h => h, ?_, ?_⟩
    · rintro i hi ⟨q, hq, hqi⟩
      exact clean q i hq hi hqi
    · intro q i hq hqi
      exact ⟨q, hq, hqi⟩

/-- `none` is the retirement bit; each `some j` is one low index bit. -/
def idBits (word : J → Bool) (retired : Bool) : Option J → Bool
  | none => retired
  | some j => word j

def increases (x y : J → Bool) : Prop := ∀ j, x j = true → y j = true

theorem record_lifecycle (word : J → Bool) :
    increases (idBits (fun _ => false) false) (idBits word false) ∧
    increases (idBits word false) (idBits word true) := by
  constructor <;> intro j hj <;> cases j <;> simp_all [idBits]

private theorem sum_separate (rows : List T) (f g : T → Nat) :
    (rows.map (fun t => f t + g t)).sum = (rows.map f).sum + (rows.map g).sum := by
  induction rows with
  | nil => simp
  | cons t ts ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Sum of edit distances equals summed per-row variation; both counts include
    one contribution for each changed (edit,row) pair. -/
theorem total_variation (edits : List E) (rows : List T) (cost : E → T → Nat) :
    (edits.map (fun e => (rows.map (cost e)).sum)).sum =
      (rows.map (fun t => (edits.map (fun e => cost e t)).sum)).sum := by
  induction edits with
  | nil =>
    induction rows with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Nat.zero_add] at ih ⊢
      exact ih
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [sum_separate]

end EditAmplification
