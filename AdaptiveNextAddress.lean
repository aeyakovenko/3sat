import Std

namespace AdaptiveNextAddress

/-- Disjoint tags in the simulation; `other` includes the rest of physical memory. -/
inductive Word where
  | zero | hub | port | cell (a : Nat) | val (v : Nat) | other (z : Nat)
  deriving DecidableEq

open Word
abbrev Memory := Word → Word

def put (m : Memory) (a x : Word) : Memory := fun b => if b = a then x else m b

/-- The only write goes to the word just read and stores the next head. -/
def visit (m : Memory) (head next : Word) : Memory := put m (m head) next

def Represents (m : Memory) (guest : Nat → Nat) : Prop :=
  m hub = port ∧ (∀ v, m (val v) = zero ∨ m (val v) = port) ∧
  (∀ a, m (cell a) = val (guest a) ∨ (m (cell a) = zero ∧ guest a = 0))

def cycle (m : Memory) (a v : Nat) : Memory :=
  visit (visit (visit (visit m hub (cell a)) (cell a) port) port (val v)) (val v) hub

/-- The second visit returns the correct old value (zero has two representations). -/
theorem readOld {m : Memory} {g : Nat → Nat} (rep : Represents m g) (a : Nat) :
    (visit m hub (cell a)) (cell a) = val (g a) ∨
      ((visit m hub (cell a)) (cell a) = zero ∧ g a = 0) := by
  simpa [visit, put, rep.1] using rep.2.2 a

/-- The four compulsory stores implement one arbitrary guest write. An unchanged
    payload gives a guest read while preserving the full representation invariant. -/
theorem cycleWrites {m : Memory} {g : Nat → Nat} (rep : Represents m g) (a v : Nat) :
    Represents (cycle m a v) (fun b => if b = a then v else g b) := by
  obtain ⟨hh, tags, cells⟩ := rep
  let m1 := visit m hub (cell a)
  let m2 := visit m1 (cell a) port
  let m3 := visit m2 port (val v)
  have atCell : m1 (cell a) = m (cell a) := by simp [m1, visit, put, hh]
  have old := cells a
  have atPort : m2 port = cell a := by
    rcases old with o | ⟨o, _⟩ <;> simp [m2, visit, atCell, o, m1, put, hh]
  have e1 : m1 = put m port (cell a) := by simp [m1, visit, hh]
  have e2 : m2 = put m1 (m (cell a)) port := by rw [show m2 = put m1 (m1 (cell a)) port from rfl, atCell]
  have e3 : m3 = put m2 (cell a) (val v) := by rw [show m3 = put m2 (m2 port) (val v) from rfl, atPort]
  have tagSafe (z : Nat) : m3 (val z) = zero ∨ m3 (val z) = port := by
    rcases old with o | ⟨o, _⟩
    · by_cases matchOld : z = g a
      · simp [e3, e2, e1, put, o, matchOld]
      · simpa [e3, e2, e1, put, o, matchOld] using tags z
    · simpa [e3, e2, e1, put, o] using tags z
  have untouched (z : Nat) (ne : z ≠ a) : m3 (cell z) = m (cell z) := by
    rcases old with o | ⟨o, _⟩ <;> simp [e3, e2, e1, put, ne, o]
  change Represents (visit m3 (val v) hub) _
  have e4 : visit m3 (val v) hub = put m3 (m3 (val v)) hub := rfl
  refine ⟨?_, ?_, ?_⟩
  · rcases tagSafe v with tv | tv <;> rcases old with o | ⟨o, _⟩ <;>
      rw [e4, tv, e3, e2, e1] <;> simp [put, o, hh]
  · intro z
    rcases tagSafe v with tv | tv <;> simpa [visit, put, tv] using tagSafe z
  · intro z
    by_cases ne : z = a
    · subst z
      left
      rcases tagSafe v with tv | tv <;> rw [e4, tv, e3] <;> simp [put]
    · rcases tagSafe v with tv | tv <;> simpa [visit, put, tv, ne, untouched z ne] using cells z

end AdaptiveNextAddress
