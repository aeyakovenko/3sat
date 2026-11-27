import Std

namespace ThreePageRoutes

/-- A macro edge switches labels exactly once on a chain of consecutive layers. -/
def wire (src dst switch layer : Nat) : Nat :=
  if layer ≤ switch then src else dst

theorem one_interface (src dst switch layer : Nat) :
    (layer = switch ∧ wire src dst switch layer = src ∧
      wire src dst switch (layer+1) = dst) ∨
    (layer ≠ switch ∧ wire src dst switch layer = wire src dst switch (layer+1)) := by
  by_cases h : layer = switch
  · subst layer
    have hnext : ¬switch + 1 ≤ switch := by omega
    exact Or.inl ⟨rfl, by simp [wire], by simp [wire, hnext]⟩
  · right
    refine ⟨h, ?_⟩
    by_cases k : layer < switch
    · have h₁ : layer ≤ switch := by omega
      have h₂ : layer + 1 ≤ switch := by omega
      simp [wire, h₁, h₂]
    · have h₁ : ¬ layer ≤ switch := by omega
      have h₂ : ¬ layer + 1 ≤ switch := by omega
      simp [wire, h₁, h₂]

def projects (cut : Nat → Nat → Prop) (length label : Nat) : Prop :=
  ∃ t, t ≤ length ∧ cut t label

theorem lifts_past_deletions {cut : Nat → Nat → Prop} {len src dst switch : Nat}
    (startSafe : ¬projects cut len src) (endSafe : ¬projects cut len dst)
    {layer : Nat} (ht : layer ≤ len) : ¬cut layer (wire src dst switch layer) := by
  unfold wire
  split <;> intro bad
  · exact startSafe ⟨layer, ht, bad⟩
  · exact endSafe ⟨layer, ht, bad⟩

/-- In opposite orders, two increasing endpoint pairs have nested positions. -/
theorem nested (w i a b fa fb : Nat) (hab : a < b) (hb : b < w)
    (hf : fa < fb) (hfb : fb < w) :
    i+a < i+b ∧ i+b < i+w+(w-1-fb) ∧
    i+w+(w-1-fb) < i+w+(w-1-fa) := by omega

/-- Directed paths that survive deletion; singleton walks include their vertex. -/
inductive Path {V : Type} (edge : V → V → Prop) (safe : V → Prop) : V → V → Prop where
  | nil {x} (hx : safe x) : Path edge safe x x
  | next {x y z} (hx : safe x) (step : edge x y) (tail : Path edge safe y z) :
      Path edge safe x z

theorem start_safe {V : Type} {e : V → V → Prop} {s : V → Prop} {x y : V}
    (p : Path e s x y) : s x := by cases p <;> assumption

theorem append {V : Type} {e : V → V → Prop} {s : V → Prop} {x y z : V}
    (a : Path e s x y) (b : Path e s y z) : Path e s x z := by
  induction a with
  | nil => exact b
  | next hx step _ ih => exact .next hx step (ih b)

theorem lift_path {V W : Type} {e : V → V → Prop} {f : W → W → Prop}
    {s : V → Prop} {t : W → Prop} (rep : V → W)
    (kept : ∀ x, s x → t (rep x))
    (liftEdge : ∀ x y, s x → s y → e x y → Path f t (rep x) (rep y))
    {a b : V} (p : Path e s a b) : Path f t (rep a) (rep b) := by
  induction p with
  | nil hx => exact .nil (kept _ hx)
  | next hx step rest ih => exact append (liftEdge _ _ hx (start_safe rest) step) ih

/-- The route fixes the target prefix and the source suffix. A fiber is in
bijection with the remaining source prefix and target suffix. -/
def label {P S : Type} (routes : (P × S) × (P × S)) : P × S :=
  (routes.2.1, routes.1.2)

def inFiber {P S : Type} (z : P × S) (free : P × S) :
    {r : (P × S) × (P × S) // label r = z} :=
  ⟨((free.1, z.2), (z.1, free.2)), by cases z; rfl⟩

def freeBits {P S : Type} {z : P × S}
    (r : {r : (P × S) × (P × S) // label r = z}) : P × S :=
  (r.val.1.1, r.val.2.2)

theorem fiber_left {P S : Type} (z free : P × S) :
    freeBits (inFiber z free) = free := by cases free; rfl

theorem fiber_right {P S : Type} {z : P × S}
    (r : {r : (P × S) × (P × S) // label r = z}) :
    inFiber z (freeBits r) = r := by
  rcases r with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩, h⟩
  subst z
  rfl

end ThreePageRoutes
