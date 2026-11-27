import Std

namespace PlantedColorRepair

inductive Color | red | green | blue deriving DecidableEq

instance {p : Color → Prop} [DecidablePred p] : Decidable (∀ c, p c) :=
  decidable_of_iff (p .red ∧ p .green ∧ p .blue) (by
    constructor
    · rintro ⟨r, g, b⟩ c
      cases c <;> assumption
    · intro h
      exact ⟨h _, h _, h _⟩)

structure Fiber where
  a : Color
  b : Color
  c : Color
  deriving DecidableEq

def regular (x : Fiber) : Prop := x.a ≠ x.b ∧ x.a ≠ x.c ∧ x.b ≠ x.c

def compatible (x y : Fiber) : Prop :=
  x.a ≠ y.b ∧ x.a ≠ y.c ∧ x.b ≠ y.a ∧ x.b ≠ y.c ∧ x.c ≠ y.a ∧ x.c ≠ y.b

def repeated (x : Fiber) : Color := if x.a = x.b then x.a else if x.a = x.c then x.a else x.b

private theorem reverse {x y : Fiber} (h : compatible x y) : compatible y x := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨Ne.symm h₃, Ne.symm h₅, Ne.symm h₁, Ne.symm h₆, Ne.symm h₂, Ne.symm h₄⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 1000000 in
theorem agree_of_regular (x y : Fiber) (h : compatible x y) (r : regular x) : x = y := by
  cases x with | mk a b c =>
    cases y with | mk d e f =>
      revert h r
      revert a b c d e f
      unfold compatible regular
      decide

set_option maxRecDepth 24000 in
set_option maxHeartbeats 1000000 in
theorem repeated_differ (x y : Fiber) (h : compatible x y) (r : ¬regular x)
    (s : ¬regular y) : repeated x ≠ repeated y := by
  cases x with | mk a b c =>
    cases y with | mk d e f =>
      revert h r s
      cases a <;> cases b <;> (revert c d e f; unfold compatible regular repeated; decide)

theorem midpoint_crossing {x mid y : Fiber} (mixed : ¬(regular x ↔ regular y)) :
    ¬(compatible x mid ∧ compatible mid y) := by
  rintro ⟨left, right⟩
  apply mixed
  constructor
  · intro h
    have a := agree_of_regular x mid left h
    have b := agree_of_regular mid y right (a ▸ h)
    exact b ▸ a ▸ h
  · intro h
    have a := agree_of_regular y mid (reverse right) h
    have b := agree_of_regular mid x (reverse left) (a ▸ h)
    exact b ▸ a ▸ h

instance (x : Fiber) : Decidable (regular x) := by unfold regular; infer_instance
instance (x y : Fiber) : Decidable (compatible x y) := by unfold compatible; infer_instance

def fiberType (x : Fiber) : Option Fiber := if regular x then some x else none

theorem type_compatible {x y : Fiber} (h : compatible x y) : fiberType x = fiberType y := by
  by_cases r : regular x
  · rw [agree_of_regular x y h r]
  · have s : ¬regular y := fun hy => r (agree_of_regular y x (reverse h) hy ▸ hy)
    simp [fiberType, r, s]

structure Link where
  left : Fiber
  middle : Fiber
  right : Fiber

private def crossing (e : Link) : Nat := if fiberType e.left = fiberType e.right then 0 else 1
private def bad (x y : Fiber) : Nat := if compatible x y then 0 else 1

/-- Each crossing expander link has a separate incompatible subdivided edge. -/
theorem countCrossings (links : List Link) :
    (links.map crossing).sum ≤
      (links.map (fun e => bad e.left e.middle + bad e.middle e.right)).sum := by
  induction links with
  | nil => simp
  | cons e tail ih =>
    have one : crossing e ≤ bad e.left e.middle + bad e.middle e.right := by
      by_cases h : compatible e.left e.middle
      · by_cases g : compatible e.middle e.right
        · have eq := (type_compatible h).trans (type_compatible g)
          simp [crossing, bad, eq, h, g]
        · simp [bad, h, g, crossing]
          split <;> decide
      · simp [bad, h, crossing]
        split <;> omega
    simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add one ih

inductive Walk {V : Type} (edge : V → V → Prop) : V → V → Prop
  | refl (v : V) : Walk edge v v
  | step {u v w : V} : Walk edge u v → edge v w → Walk edge u w

private theorem transport {V : Type} {edge : V → V → Prop} {s : V → Fiber}
    (legal : ∀ x y, edge x y → compatible (s x) (s y)) {x y : V}
    (walk : Walk edge x y) (r : regular (s x)) : s x = s y := by
  induction walk with
  | refl => rfl
  | step w e ih => exact ih.trans (agree_of_regular _ _ (legal _ _ e) (ih ▸ r))

/-- Adding the missing same-index edge makes existence of a repair
equivalent to three-colorability of the original connected graph. -/
theorem repair_iff {V : Type} (edge : V → V → Prop)
    (connected : ∀ x y, Walk edge x y) {a b : V} (marked : edge a b) :
    (∃ s : V → Fiber, (∀ x y, edge x y → compatible (s x) (s y)) ∧ (s a).a ≠ (s b).a) ↔
    ∃ t : V → Color, ∀ x y, edge x y → t x ≠ t y := by
  constructor
  · rintro ⟨s, h, pin⟩
    have collapsed (v : V) : ¬regular (s v) := by
      intro r
      have ha := transport h (connected v a) r
      have hb := transport h (connected v b) r
      exact pin (congrArg Fiber.a (ha.symm.trans hb))
    exact ⟨fun v => repeated (s v), fun x y e =>
      repeated_differ _ _ (h x y e) (collapsed x) (collapsed y)⟩
  · rintro ⟨t, h⟩
    refine ⟨fun v => ⟨t v,t v,t v⟩, ?_, h a b marked⟩
    intro x y e
    have hn := h x y e
    exact ⟨hn, hn, hn, hn, hn, hn⟩

end PlantedColorRepair
