import Std

/-! Repeating a block of forecast layers while allowing every timestamp column.
The state can be a row vector, a tuple of row vectors, or any transition state.
An assertion can express membership in a subspace supplied by a finite basis. -/

namespace ForecastBlockLift

variable {Layer Column State : Type}

/-- Each layer may receive any column, independently of every other layer. -/
def Reach (step : Layer → Column → State → State) : List Layer → State → State → Prop
  | [], x, z => x = z
  | layer :: layers, x, z => ∃ c, Reach step layers (step layer c x) z

theorem reach_append (step : Layer → Column → State → State)
    (left right : List Layer) (x z : State) :
    Reach step (left ++ right) x z ↔
      ∃ y, Reach step left x y ∧ Reach step right y z := by
  induction left generalizing x with
  | nil => simp [Reach]
  | cons layer layers ih =>
    change (∃ c, Reach step (layers ++ right) (step layer c x) z) ↔
      ∃ y, (∃ c, Reach step layers (step layer c x) y) ∧ Reach step right y z
    constructor
    · rintro ⟨c, h⟩
      obtain ⟨y, h₁, h₂⟩ := (ih _).mp h
      exact ⟨y, ⟨c, h₁⟩, h₂⟩
    · rintro ⟨y, ⟨c, h₁⟩, h₂⟩
      exact ⟨c, (ih _).mpr ⟨y, h₁, h₂⟩⟩

/-- A finite chain of local assertions, one transition check per layer. -/
inductive Certified (step : Layer → Column → State → State) :
    (State → Prop) → List Layer → (State → Prop) → Prop where
  | nil (P : State → Prop) : Certified step P [] P
  | cons {P Q R : State → Prop} {layer : Layer} {layers : List Layer}
      (transition : ∀ x, P x → ∀ c, Q (step layer c x))
      (tail : Certified step Q layers R) : Certified step P (layer :: layers) R

theorem Certified.sound {step : Layer → Column → State → State}
    {P Q : State → Prop} {layers : List Layer} (cert : Certified step P layers Q) :
    ∀ x, P x → ∀ z, Reach step layers x z → Q z := by
  induction cert with
  | nil _ =>
    intro x hx z h
    exact (show x = z from h) ▸ hx
  | cons transition _ ih =>
    intro x hx z h
    obtain ⟨c, tail⟩ := h
    exact ih _ (transition x hx c) _ tail

def repeatBlock (block : List Layer) : Nat → List Layer
  | 0 => []
  | k + 1 => repeatBlock block k ++ block

/-- The exact invariant, if needed, is the union of the states reachable
after the prefix followed by any number of complete blocks. -/
theorem all_repetitions_iff (step : Layer → Column → State → State)
    (pre block post : List Layer) (initial : State) (good : State → Prop) :
    (∀ k z, Reach step (pre ++ repeatBlock block k ++ post) initial z → good z) ↔
      ∃ P : State → Prop,
        (∀ x, Reach step pre initial x → P x) ∧
        (∀ x, P x → ∀ y, Reach step block x y → P y) ∧
        (∀ x, P x → ∀ z, Reach step post x z → good z) := by
  constructor
  · intro safe
    let P := fun x => ∃ k, Reach step (pre ++ repeatBlock block k) initial x
    refine ⟨P, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨0, by simpa [repeatBlock] using hx⟩
    · rintro x ⟨k, hx⟩ y hy
      refine ⟨k + 1, ?_⟩
      rw [repeatBlock, ← List.append_assoc, reach_append]
      exact ⟨x, hx, hy⟩
    · rintro x ⟨k, hx⟩ z hz
      exact safe k z ((reach_append step _ _ _ _).mpr ⟨x, hx, hz⟩)
  · rintro ⟨P, starts, closed, finishes⟩
    have preserved : ∀ k x, Reach step (pre ++ repeatBlock block k) initial x → P x := by
      intro k
      induction k with
      | zero => simpa [repeatBlock] using starts
      | succ k ih =>
        intro y hy
        rw [repeatBlock, ← List.append_assoc, reach_append] at hy
        obtain ⟨x, hx, blockRun⟩ := hy
        exact closed x (ih x hx) y blockRun
    intro k z hz
    obtain ⟨x, hx, postRun⟩ := (reach_append step _ _ _ _).mp hz
    exact finishes x (preserved k x hx) z postRun

/-- A local certificate for a nonempty loop and its prefix/suffix gives safe
schedules of strictly increasing lengths. Each traversal gets fresh columns. -/
theorem block_lift {step : Layer → Column → State → State} {initial : State}
    {pre block post : List Layer} {P good : State → Prop} (nonempty : 0 < block.length)
    (entry : Certified step (fun x => initial = x) pre P)
    (loop : Certified step P block P) (finish : Certified step P post good) :
    (∀ k z, Reach step (pre ++ repeatBlock block k ++ post) initial z → good z) ∧
    (∀ k, (pre ++ repeatBlock block k ++ post).length <
      (pre ++ repeatBlock block (k + 1) ++ post).length) := by
  constructor
  · exact (all_repetitions_iff step pre block post initial good).mpr
      ⟨P, entry.sound initial rfl, loop.sound, finish.sound⟩
  · intro k
    simp only [repeatBlock, List.length_append]
    omega

end ForecastBlockLift
