import Std

namespace ThresholdPortColoring

/-- The Boolean tag is true at the head and false at the tail. -/
abbrev Port (V : Type) := V × Bool

def Join {V : Type} (rows : V → V → Prop) (p q : Port V) : Prop :=
  p.2 = true ∧ q.2 = false ∧ rows p.1 q.1

/-- Adjacent ports have equal colors. The two ports of a variable differ. -/
def Allowed {V C : Type} (rows : V → V → Prop) (paint : Port V → C) : Prop :=
  (∀ v, paint (v, false) ≠ paint (v, true)) ∧
  ∀ p q, Join rows p q → paint p = paint q

/-- Contract every equality row, retaining one inequality per variable. -/
theorem contraction {V C : Type} (rows : V → V → Prop) :
    (∃ paint : Port V → C, Allowed rows paint) ↔
    ∃ c : Quot (Join rows) → C,
      ∀ v, c (Quot.mk _ (v, false)) ≠ c (Quot.mk _ (v, true)) := by
  constructor
  · rintro ⟨paint, different, compatible⟩
    exact ⟨Quot.lift paint compatible, different⟩
  · rintro ⟨c, different⟩
    exact ⟨fun p => c (Quot.mk _ p), different,
      fun _ _ edge => congrArg c (Quot.sound edge)⟩

/-- The threshold MSF property is sufficient at each fixed threshold. -/
theorem preserve_of_connected {V C : Type} {all kept : V → V → Prop}
    (sub : ∀ p q, Join kept p q → Join all p q)
    (covered : ∀ p q, Join all p q →
      Quot.mk (Join kept) p = Quot.mk (Join kept) q)
    (paint : Port V → C) : Allowed kept paint ↔ Allowed all paint := by
  constructor
  · rintro ⟨distinct, respects⟩
    exact ⟨distinct, fun p q row =>
      congrArg (Quot.lift paint respects) (covered p q row)⟩
  · rintro ⟨distinct, respects⟩
    exact ⟨distinct, fun p q row => respects p q (sub p q row)⟩

inductive Ink | zero | one | two deriving DecidableEq, Repr

instance {p : Ink → Prop} [DecidablePred p] : Decidable (∀ i, p i) :=
  decidable_of_iff (p .zero ∧ p .one ∧ p .two) (by
    constructor
    · rintro ⟨h, j, k⟩ i
      cases i <;> assumption
    · intro h
      exact ⟨h _, h _, h _⟩)

instance {p : Ink → Prop} [DecidablePred p] : Decidable (∃ i, p i) :=
  decidable_of_iff (p .zero ∨ p .one ∨ p .two) (by
    constructor
    · rintro (h | h | h)
      · exact ⟨.zero, h⟩
      · exact ⟨.one, h⟩
      · exact ⟨.two, h⟩
    · rintro ⟨i, h⟩
      cases i with
      | zero => exact Or.inl h
      | one => exact Or.inr (Or.inl h)
      | two => exact Or.inr (Or.inr h))

private def color (b : Bool) : Ink := if b then .one else .zero

def triangle (a b c : Bool) : Prop :=
  ∃ x y z : Ink, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
    x ≠ color a ∧ y ≠ color b ∧ z ≠ color c

instance (a b c : Bool) : Decidable (triangle a b c) :=
  by unfold triangle; infer_instance

def nae (a b c : Bool) : Prop := a ≠ b ∨ b ≠ c

theorem triangle_nae : ∀ a b c, triangle a b c ↔ nae a b c := by
  unfold nae
  decide

theorem clause_split : ∀ a b c : Bool,
    (a || b || c) = true ↔ ∃ z : Bool, nae a b z ∧ nae (!z) c false := by
  unfold nae
  decide

/-- Two adjacent anchors force three terminals to have the same color. -/
theorem split_three : ∀ a b c : Ink,
    (∃ x y : Ink, x ≠ y ∧ a ≠ x ∧ a ≠ y ∧
      b ≠ x ∧ b ≠ y ∧ c ≠ x ∧ c ≠ y) ↔ (a = b ∧ b = c) := by decide

end ThresholdPortColoring
