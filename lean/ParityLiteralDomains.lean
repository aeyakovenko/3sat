import Std

namespace ParityLiteralDomains

structure Literal (V : Type) where
  name : V
  required : Bool

def Holds (a : V → Bool) (l : Literal V) : Prop := a l.name = l.required

/-- All clauses besides the edited one, and all other literals of that clause. -/
def WithLiteral (rest others : (V → Bool) → Prop) (l : Literal V) : Prop :=
  ∃ a, rest a ∧ (others a ∨ Holds a l)

/-- A witness of the accepting file must use the old literal and must falsify
    the new one, even if the names and signs both changed. -/
theorem pivotal (rest others : (V → Bool) → Prop) (old new : Literal V)
    (a : V → Bool) (valid : rest a) (clause : others a ∨ Holds a old)
    (rejects : ¬ WithLiteral rest others new) :
    Holds a old ∧ ¬ Holds a new ∧ ¬ others a := by
  have noOther : ¬ others a := fun h => rejects ⟨a, valid, Or.inl h⟩
  exact ⟨clause.resolve_left noOther,
    fun h => rejects ⟨a, valid, Or.inr h⟩, noOther⟩

/-- Arbitrary values of two blocks have a common positive completion. In
    that completion the pivotal witness of the second literal must also
    reject each one-bit change of that literal. -/
theorem disjointNames (f : P → Literal V) (g : Q → Literal V)
    (edge : Q → Q → Prop) (neighbor : ∀ q, ∃ t, edge t q)
    (witness : ∀ p q, ∃ a, Holds a (f p) ∧ Holds a (g q) ∧
      ∀ t, edge q t → ¬ Holds a (g t)) :
    ∀ p q, (f p).name ≠ (g q).name := by
  intro p q same
  by_cases sign : (f p).required = (g q).required
  · obtain ⟨t, adj⟩ := neighbor q
    obtain ⟨a, hp, _, change⟩ := witness p t
    apply change q adj
    simpa only [Holds, ← same, ← sign] using hp
  · obtain ⟨a, hp, hq, _⟩ := witness p q
    exact sign (hp.symm.trans ((congrArg a same).trans hq))

/-- If all other clauses are unchanged by setting a variable, a model of
    the remaining clauses extends to one satisfying its occurrence. -/
theorem freshName (rest others : (V → Bool) → Prop) (lit : Literal V)
    (hasModel : ∃ a, rest a)
    (fresh : ∀ a, rest a → ∃ b, rest b ∧ b lit.name = lit.required) :
    WithLiteral rest others lit := by
  obtain ⟨a, ha⟩ := hasModel
  obtain ⟨b, hb, val⟩ := fresh a ha
  exact ⟨b, hb, Or.inr val⟩

/-- This version discharges the freshness premise on an actual list of clauses
    rather than requiring an invariance assumption on a predicate. -/
def models (a : V → Bool) (formula : List (List (Literal V))) : Prop :=
  ∀ clause ∈ formula, ∃ l ∈ clause, Holds a l

theorem restoreFresh (formula : List (List (Literal V))) (lit : Literal V)
    (a : V → Bool) (ok : models a formula)
    (absent : ∀ clause ∈ formula, ∀ l ∈ clause, l.name ≠ lit.name) :
    ∃ b, models b formula ∧ Holds b lit := by
  classical
  let b := fun v => if v = lit.name then lit.required else a v
  refine ⟨b, ?_, ?_⟩
  · intro clause hc
    obtain ⟨l, hl, truth⟩ := ok clause hc
    refine ⟨l, hl, ?_⟩
    simpa [Holds, b, absent clause hc l hl] using truth
  · simp [Holds, b]

end ParityLiteralDomains
