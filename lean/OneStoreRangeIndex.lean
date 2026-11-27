import Std

namespace OneStoreRangeIndex

variable {Pos Key : Type} [DecidableEq Key]

def checked (key : Pos → Key) (index : Key → Option Pos) (y : Key) : Option Pos := do
  let p ← index y
  if key p = y then some p else none

theorem reports_genuine (key : Pos → Key) (index : Key → Option Pos) (y : Key) (p : Pos)
    (h : checked key index y = some p) : key p = y := by
  cases answer : index y with
  | none => simp [checked, answer] at h
  | some v =>
    by_cases sameKey : key v = y
    · simp [checked, answer, sameKey] at h
      simpa [← h] using sameKey
    · simp [checked, answer, sameKey] at h

/-- Checking the query induced by every domain point suffices, including when many
    points share an image. An arbitrary absent query need not receive a challenge. -/
theorem miss_iff (key : Pos → Key) (index : Key → Option Pos)
    (complete : ∀ p, checked key index (key p) ≠ none) (y : Key) :
    checked key index y = none ↔ ¬ ∃ p, key p = y := by
  constructor
  · intro miss ⟨p, hp⟩
    exact complete p (hp ▸ miss)
  · intro absent
    cases h : checked key index y with
    | none => rfl
    | some p => exact False.elim (absent ⟨p, reports_genuine key index y p h⟩)

section Replay

variable {State Addr Word : Type} [DecidableEq Addr]

/-- One physical store per step, and the fixed initial contents are an argument. -/
def write (old : Addr → Word) (event : Option (Addr × Word)) (a : Addr) : Word :=
  match event with
  | none => old a
  | some (k,v) => if k = a then v else old a

def chartMem (initial : Addr → Word) (chart : Nat → Option (Addr × Word)) : Nat → Addr → Word
  | 0 => initial
  | t+1 => write (chartMem initial chart t) (chart t)

def actual (initial : Addr → Word) (boot : State) (emit : State → Option (Addr × Word))
    (step : State → (Addr → Word) → State) : Nat → State × (Addr → Word)
  | 0 => (boot, initial)
  | t+1 => let (s, m) := actual initial boot emit step t
           (step s m, write m (emit s))

/-- Concatenated block states become the true registers and memory, when the
    observed stores and every transition agree with the single proposed chart. -/
theorem checked_replay (initial : Addr → Word) (boot : State)
    (emit : State → Option (Addr × Word)) (step : State → (Addr → Word) → State)
    (chart : Nat → Option (Addr × Word)) (observed : Nat → State) (T : Nat)
    (start : observed 0 = boot) (events : ∀ t < T, emit (observed t) = chart t)
    (steps : ∀ t < T, observed (t+1) = step (observed t) (chartMem initial chart t)) :
    ∀ t ≤ T, actual initial boot emit step t = (observed t, chartMem initial chart t) := by
  intro t
  induction t with
  | zero => simp [actual, chartMem, start]
  | succ t ih =>
    intro bound
    have before : t < T := by omega
    simp [actual, ih (by omega), chartMem, events t before, steps t before]

end Replay
end OneStoreRangeIndex
