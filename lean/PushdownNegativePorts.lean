import Std

namespace PushdownNegativePorts

structure Rules (State Symbol : Type) where
  neutral : State → State → Prop
  push : State → Symbol → State → Prop
  pop : State → Symbol → State → Prop

inductive Balanced {State Symbol : Type} (r : Rules State Symbol) : State → State → Prop where
  | empty (a) : Balanced r a a
  | step {a b} (edge : r.neutral a b) : Balanced r a b
  | join {a b c} (left : Balanced r a b) (right : Balanced r b c) : Balanced r a c
  | wrap {a b c d z} (push : r.push a z b) (inner : Balanced r b c)
      (pop : r.pop c z d) : Balanced r a d

structure Closed {State Symbol : Type} (r : Rules State Symbol) (rel : State → State → Prop) :
    Prop where
  empty : ∀ a, rel a a
  step : ∀ {a b}, r.neutral a b → rel a b
  join : ∀ {a b c}, rel a b → rel b c → rel a c
  wrap : ∀ {a b c d z}, r.push a z b → rel b c → r.pop c z d → rel a d

variable {State Symbol : Type} {r : Rules State Symbol} {rel : State → State → Prop}

theorem least (closed : Closed r rel) {a b} (path : Balanced r a b) : rel a b := by
  induction path with
  | empty a => exact closed.empty a
  | step edge => exact closed.step edge
  | join _ _ ih₁ ih₂ => exact closed.join ih₁ ih₂
  | wrap push _ pop ih => exact closed.wrap push ih pop

def addPair (r : Rules State Symbol) (p q : State) : Rules State Symbol :=
  { r with neutral := fun a b => r.neutral a b ∨ (a = p ∧ b = q) }

theorem closeWithPair (p q : State) (closed : Closed r rel) (edge : rel p q) :
    Closed (addPair r p q) rel := by
  refine ⟨closed.empty, ?_, closed.join, closed.wrap⟩
  intro a b step
  rcases step with old | ⟨rfl, rfl⟩
  · exact closed.step old
  · exact edge

theorem shortcut_is_conservative {a b p q : State} (existing : Balanced r p q)
    (augmented : Balanced (addPair r p q) a b) : Balanced r a b := by
  have closed : Closed r (Balanced r) :=
    ⟨Balanced.empty, Balanced.step, Balanced.join, Balanced.wrap⟩
  exact least (closeWithPair p q closed existing) augmented

/-- Exact criterion for whether a proposed extra pair can occur in any
    inductive certificate that still separates the specified root pair. -/
theorem admissible_iff (r : Rules State Symbol) (start stop p q : State) :
    (∃ rel, Closed r rel ∧ rel p q ∧ ¬rel start stop) ↔
      ¬Balanced (addPair r p q) start stop := by
  constructor
  · rintro ⟨rel, closed, edge, excluded⟩ path
    exact excluded (least (closeWithPair p q closed edge) path)
  · intro impossible
    refine ⟨Balanced (addPair r p q), ?_, Balanced.step (Or.inr ⟨rfl, rfl⟩), impossible⟩
    exact ⟨Balanced.empty, fun edge => Balanced.step (Or.inl edge), Balanced.join,
      fun push path pop => Balanced.wrap (r := addPair r p q) push path pop⟩

/-- An authentic path forces a one. An accepting context with one neutral
    hole forces a zero, even for overapproximations with arbitrary extra pairs. -/
theorem forced_port (r : Rules State Symbol) (start stop p q : State) (bit : Prop)
    (positive : bit → Balanced r p q)
    (negative : ¬bit → Balanced (addPair r p q) start stop)
    (closed : Closed r rel) (excluded : ¬rel start stop) : rel p q ↔ bit := by
  constructor
  · intro edge
    apply Classical.byContradiction
    intro falseBit
    exact excluded (least (closeWithPair p q closed edge) (negative falseBit))
  · exact fun trueBit => least closed (positive trueBit)

end PushdownNegativePorts
