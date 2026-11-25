import Std

namespace NestedTimedCores

variable {Program Input : Type} (truth : Input → Bool)
  (run : Program → Input → Nat → Option Bool)

/-- Programs may abstain on any valid input. `Input` ranges over valid files. -/
def Sound (p : Program) : Prop :=
  ∀ x t b, run p x t = some b → b = truth x

def Refuted (p : Program) : Prop :=
  ∃ x t b, run p x t = some b ∧ b ≠ truth x

theorem refuted_iff (p : Program) : Refuted truth run p ↔ ¬ Sound truth run p := by
  classical
  constructor
  · rintro ⟨x, t, b, hr, wrong⟩ hs
    exact wrong (hs x t b hr)
  · intro h
    apply Classical.byContradiction
    intro noError
    apply h
    intro x t b hr
    apply Classical.byContradiction
    intro wrong
    exact noError ⟨x, t, b, hr, wrong⟩

variable (deadline : Input → Nat)

def AllSlow (p : Program) (block : List Input) : Prop :=
  ∀ x ∈ block, run p x (deadline x) = none

/-- A finite certificate is checked separately for each machine. An actual
    wrong halt or a timeout on every corner are the two possible records. -/
def Certificate (pool : List Program) (block : List Input) : Prop :=
  ∀ p ∈ pool, Refuted truth run p ∨ AllSlow run deadline p block

theorem certificate_iff (pool : List Program) (block : List Input) :
    Certificate truth run deadline pool block ↔
    ∀ p ∈ pool, Sound truth run p → AllSlow run deadline p block := by
  classical
  constructor
  · intro hc p hp hs
    rcases hc p hp with err | slow
    · exact False.elim ((refuted_iff truth run p).mp err hs)
    · exact slow
  · intro h p hp
    by_cases hs : Sound truth run p
    · exact Or.inr (h p hp hs)
    · exact Or.inl ((refuted_iff truth run p).mpr hs)

/-- Here the rank bounds the dimensions, time multipliers and size of the
    effective pool. The clock bound of one globally correct program is
    enough to block any nonempty stage with that program and deadline. -/
theorem timely_prevents_stage (pool : List Program) (block : List Input) (p : Program)
    (hp : p ∈ pool) (hs : Sound truth run p)
    (timely : ∃ x ∈ block, ∃ b, run p x (deadline x) = some b) :
    ¬ Certificate truth run deadline pool block := by
  intro h
  obtain ⟨x, hx, b, hr⟩ := timely
  have empty := ((certificate_iff truth run deadline pool block).mp h p hp hs) x hx
  simp [hr] at empty

/-- On independent variable sets the same assignment on the anchor extends
    to the new formula at each satisfiable corner. -/
theorem independent_extension_iff {A B : Type} (anchor : A → Prop) (fresh : B → Prop)
    (a : A) (ha : anchor a) :
    (∃ b, anchor a ∧ fresh b) ↔ ∃ b, fresh b := by
  exact ⟨fun ⟨b, _, hb⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, ha, hb⟩⟩

/-- Once an unsatisfiable seed is retained as clauses, every extension
    is unsatisfiable even when it introduces new variables. -/
theorem keeps_unsat {A B : Type} (old : A → Prop) (new : B → Prop) (restrict : B → A)
    (retains : ∀ b, new b → old (restrict b)) (noOld : ¬ ∃ a, old a) :
    ¬ ∃ b, new b := fun ⟨b,h⟩ => noOld ⟨_,retains b h⟩

end NestedTimedCores
