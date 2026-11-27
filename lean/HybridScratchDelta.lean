import Std

namespace HybridScratchDelta

variable {Address Value : Type}

/-- An explicit value, including zero, overrides the preceding memory. -/
def install (old : Address → Value) (patch : Address → Option Value) : Address → Value :=
  fun a => (patch a).getD (old a)

/-- Patches preceding an interval, in decreasing order of time. -/
def predecessor (initial : Address → Value) :
    List (Address → Option Value) → Address → Value
  | [], a => initial a
  | p :: earlier, a => (p a).getD (predecessor initial earlier a)

structure Interval (Address Value : Type) where
  actual : (Address → Value) → Address → Value
  touched : Address → Prop
  patch : Address → Option Value

/-- The local replay leaves untouched locations unchanged and checks all touched
    locations and all declared patch entries. -/
def passes (s : Interval Address Value) (old : Address → Value) : Prop :=
  (∀ a, ¬s.touched a → s.actual old a = old a) ∧
  (∀ a, (s.touched a ∨ (s.patch a).isSome = true) →
    s.actual old a = install old s.patch a)

theorem local_agreement (s : Interval Address Value) (old : Address → Value)
    (h : passes s old) : s.actual old = install old s.patch := by
  funext a
  by_cases touch : s.touched a
  · exact h.2 a (Or.inl touch)
  · cases hp : s.patch a with
    | none => simpa [install, hp] using h.1 a touch
    | some v => exact h.2 a (Or.inr (by simp [hp]))

def checkFrom (initial : Address → Value) (history : List (Address → Option Value)) :
    List (Interval Address Value) → Prop
  | [] => True
  | s :: rest =>
    passes s (predecessor initial history) ∧ checkFrom initial (s.patch :: history) rest

def execute (old : Address → Value) : List (Interval Address Value) → Address → Value
  | [] => old
  | s :: rest => execute (s.actual old) rest

def extendHistory (history : List (Address → Option Value)) :
    List (Interval Address Value) → List (Address → Option Value)
  | [] => history
  | s :: rest => extendHistory (s.patch :: history) rest

/-- All independently checked intervals recover the global memory by predecessor,
    even when the same sparse address has been erased or written many times. -/
theorem glue (initial : Address → Value) (history : List (Address → Option Value))
    (rest : List (Interval Address Value)) (ok : checkFrom initial history rest) :
    execute (predecessor initial history) rest =
      predecessor initial (extendHistory history rest) := by
  induction rest generalizing history with
  | nil => rfl
  | cons s rest ih =>
    obtain ⟨nowOk, laterOk⟩ := ok
    change execute (s.actual (predecessor initial history)) rest = _
    rw [local_agreement s _ nowOk]
    exact ih (s.patch :: history) laterOk

example : predecessor (fun _ : Bool => 0)
    [fun a => if a then some 0 else none, fun _ => some 91] true = 0 := by decide

end HybridScratchDelta
