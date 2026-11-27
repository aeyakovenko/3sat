import Std

namespace SelectorReachabilityClauses

variable {V I : Type}

structure Graph (V I : Type) where
  query : V → I
  child : V → Bool → V
  internal : V → Prop

inductive Reaches (g : Graph V I) (input : I → Bool) (start : V) : V → Prop where
  | root : Reaches g input start start
  | step {v} (h : Reaches g input start v) (branch : g.internal v) :
      Reaches g input start (g.child v (input (g.query v)))

/-- Under fixed selector pins these are precisely the two width-three
    clauses at an internal vertex plus the starting and rejecting pins. -/
def Satisfies (g : Graph V I) (input : I → Bool) (start reject : V)
    (marked : V → Prop) : Prop :=
  marked start ∧ ¬ marked reject ∧ ∀ v, g.internal v →
    (¬ marked v ∨ input (g.query v) = true ∨ marked (g.child v false)) ∧
    (¬ marked v ∨ input (g.query v) = false ∨ marked (g.child v true))

theorem sat_iff_unreachable (g : Graph V I) (input : I → Bool) (start reject : V) :
    (∃ marked, Satisfies g input start reject marked) ↔ ¬ Reaches g input start reject := by
  classical
  constructor
  · rintro ⟨marked, hstart, hend, clauses⟩ path
    have closed (v : V) (h : Reaches g input start v) : marked v := by
      induction h with
      | root => exact hstart
      | @step a _ internal ih =>
        obtain ⟨left, right⟩ := clauses a internal
        cases bit : input (g.query a) with
        | false => simpa [bit, ih] using left
        | true => simpa [bit, ih] using right
    exact hend (closed _ path)
  · intro h
    refine ⟨Reaches g input start, .root, h, ?_⟩
    intro v internal
    cases bit : input (g.query v) with
    | false =>
      refine ⟨?_, Or.inr (Or.inl rfl)⟩
      by_cases visited : Reaches g input start v
      · exact Or.inr (Or.inr (by simpa [bit] using Reaches.step visited internal))
      · exact Or.inl visited
    | true =>
      refine ⟨Or.inr (Or.inl rfl), ?_⟩
      by_cases visited : Reaches g input start v
      · exact Or.inr (Or.inr (by simpa [bit] using Reaches.step visited internal))
      · exact Or.inl visited

end SelectorReachabilityClauses
