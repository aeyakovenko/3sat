import Std

namespace AdaptiveOneBitPayload

/-- A word split into all its high bits and its least significant bit.
    All statements also apply on any fixed finite range of high parts. -/
abbrev Word := Nat × Bool
abbrev Memory := Word → Word

def put (m : Memory) (a x : Word) : Memory := fun z => if z = a then x else m z

def payload (p : Word) (flip : Bool) : Word := (p.1, Bool.xor p.2 flip)

def step (m : Memory) (p : Word) (flip : Bool) : Memory :=
  put m (m p) (payload p flip)

def hub (c : Bool) : Word := (0, c)

/-- After the first probe, reading the old bit as an address returns the target address.
    The displayed memory update fully accounts for both writes. -/
theorem two_probes (m : Memory) (p : Word) (old newBit : Bool) (h : m p = hub old) :
    step (step m p false) (hub old) (old != newBit) =
      put (put m (hub old) p) p (hub newBit) := by
  have keep : payload p false = p := by cases p with | mk k b => cases b <;> rfl
  have setValue : payload (hub old) (old != newBit) = hub newBit := by
    cases old <;> cases newBit <;> rfl
  simp [step, h, keep, setValue, put]

/-- Initial undirected adjacency after identifying two addresses differing in their low bit. -/
def neighbors (initial : Memory) (i j : Nat) : Prop :=
  (∃ b, (initial (i, b)).1 = j) ∨ (∃ b, (initial (j, b)).1 = i)

def allowed (initial m : Memory) : Prop := ∀ p, neighbors initial p.1 (m p).1

theorem initially_allowed (initial : Memory) : allowed initial initial := by
  intro p
  exact Or.inl ⟨p.2, rfl⟩

theorem step_allowed {initial m : Memory} (h : allowed initial m) (p : Word) (flip : Bool) :
    allowed initial (step m p flip) := by
  intro z
  by_cases hz : z = m p
  · subst z
    simpa [step, put, payload, neighbors, or_comm] using h p
  · simpa [step, put, hz] using h z

inductive Reach (initial : Memory) : Memory → Prop where
  | start : Reach initial initial
  | write {m : Memory} : Reach initial m → (p : Word) → (flip : Bool) →
      Reach initial (step m p flip)

theorem reach_allowed {initial m : Memory} (run : Reach initial m) : allowed initial m := by
  induction run with
  | start => exact initially_allowed _
  | write _ p flip ih => exact step_allowed ih p flip

/-- If neither member of a pair occurs as an initial value, each of its cells
    can carry at most four possible words. The two Boolean witnesses select them. -/
theorem four_values_outside_image_pairs {initial m : Memory} (run : Reach initial m)
    (p : Word) (outside : ∀ a, (initial a).1 ≠ p.1) :
    ∃ b t : Bool, m p = ((initial (p.1, b)).1, t) := by
  obtain ⟨b, hb⟩ | ⟨b, hb⟩ := reach_allowed run p
  · exact ⟨b, (m p).2, Prod.ext hb.symm rfl⟩
  · exact False.elim (outside _ hb)

end AdaptiveOneBitPayload
