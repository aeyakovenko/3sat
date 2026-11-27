import Std

namespace StrategyCutReadback

/-- A deterministic decoder after its label, query, and random tape are fixed. -/
inductive ProbeTree (Address Value Answer : Type) where
  | leaf (answer : Answer)
  | probe (address : Address) (next : Value → ProbeTree Address Value Answer)

variable {Address Value Answer : Type}

def evaluate (memory : Address → Value) : ProbeTree Address Value Answer → Answer
  | .leaf answer => answer
  | .probe address next => evaluate memory (next (memory address))

def avoids (omitted : Address → Prop) (memory : Address → Value) :
    ProbeTree Address Value Answer → Prop
  | .leaf _ => True
  | .probe address next => ¬ omitted address ∧ avoids omitted memory (next (memory address))

/-- Fixing a trace outside an omitted coordinate set fixes its output and omission event. -/
theorem indistinguishable (omitted : Address → Prop) (original alternative : Address → Value)
    (same : ∀ a, ¬ omitted a → original a = alternative a)
    (tree : ProbeTree Address Value Answer) (outside : avoids omitted original tree) :
    evaluate original tree = evaluate alternative tree ∧ avoids omitted alternative tree := by
  induction tree with
  | leaf answer => exact ⟨rfl, True.intro⟩
  | probe address next ih =>
    obtain ⟨safe, further⟩ := outside
    have agree := same address safe
    obtain ⟨value, safeTail⟩ := ih (original address) further
    simp only [evaluate, avoids, ← agree]
    exact ⟨value, safe, safeTail⟩

end StrategyCutReadback
