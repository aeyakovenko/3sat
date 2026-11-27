import Std

namespace ThresholdForestParity

/-- Chord bits are ordered as left, middle, right. The same triple on the tree
    repeats each bit twice, at edges (12,23), (34,45), and (56,67). -/
structure Triple where
  x : Bool
  y : Bool
  z : Bool
  deriving DecidableEq, Repr

instance {p : Triple → Prop} [DecidablePred p] : Decidable (∀ t, p t) :=
  decidable_of_iff (∀ x y z : Bool, p ⟨x,y,z⟩) ⟨fun h ⟨x,y,z⟩ => h x y z, fun h x y z => h ⟨x,y,z⟩⟩

/-- B changes the middle tree pair by the parity of the two outer chords. -/
def change (t : Triple) : Triple := ⟨t.x, xor (xor t.x t.y) t.z, t.z⟩

def tree (isB : Bool) (c : Triple) : Triple := if isB then change c else c

def allowed (active c : Triple) : Prop :=
  (c.x = true → active.x = true) ∧ (c.y = true → active.y = true) ∧
  (c.z = true → active.z = true)

instance (active c : Triple) : Decidable (allowed active c) := by unfold allowed; infer_instance

/-- Admit the middle chord before either outer chord. -/
def ordered (active : Triple) : Prop := (active.x = true ∨ active.z = true) → active.y = true

instance (active : Triple) : Decidable (ordered active) := by unfold ordered; infer_instance

def feasible (isB : Bool) (active c t : Triple) : Prop := allowed active c ∧ t = tree isB c

theorem tree_involutive : ∀ b c, tree b (tree b c) = c := by decide

theorem allowed_unchanged : ∀ a b c, ordered a → (allowed a (tree b c) ↔ allowed a c) := by decide

/-- The full forest-only marginal at each completed or partial prefix is
    identical in both instances. The explicit preimage is tree b t. -/
theorem forest_projection (a t : Triple) (b : Bool) (ha : ordered a) :
    (∃ c, feasible b a c t) ↔ allowed a t := by
  constructor
  · rintro ⟨c, h, rfl⟩
    exact (allowed_unchanged a b c ha).mpr h
  · intro h
    exact ⟨tree b t, (allowed_unchanged a b t ha).mpr h, (tree_involutive b t).symm⟩

/-- Chord-only marginal at every prefix, independent of the active order. -/
theorem chord_projection (a c : Triple) (b : Bool) :
    (∃ t, feasible b a c t) ↔ allowed a c := by
  constructor
  · rintro ⟨_, h, _⟩; exact h
  · exact fun h => ⟨tree b c, h, rfl⟩

private def full : Triple := ⟨true,true,true⟩

/-- The two pins say that chord 35 is absent and path edge 34 is present. -/
theorem two_pins : ∀ b : Bool,
    (∃ c t, feasible b full c t ∧ c.y = false ∧ t.y = true) ↔ b = true := by
  intro b
  constructor
  · rintro ⟨c,t,⟨_,rfl⟩,h,k⟩
    cases b <;> simp_all [tree]
  · rintro rfl
    exact ⟨⟨true,false,false⟩, ⟨true,true,false⟩, ⟨by decide, rfl⟩, rfl, rfl⟩

/-- Conditioning on one auxiliary bit k = x xor z gives signed equalities;
    the two leaves precisely cover the B relation. -/
theorem two_pieces : ∀ c t : Triple,
    (t = tree true c) ↔ (t.x = c.x ∧ t.z = c.z ∧
      ∃ k : Bool, c.z = xor c.x k ∧ t.y = xor c.y k) := by decide

private def maj (x y z : Bool) := (x && y) || (x && z) || (y && z)

private def median (a b c : Triple) : Triple :=
  ⟨maj a.x b.x c.x, maj a.y b.y c.y, maj a.z b.z c.z⟩

/-- Three bona fide legal pairs whose coordinatewise majority is illegal in B.
    Every existentially projected 2-CNF is closed under this operation. -/
theorem majority_failure :
    let a : Triple := ⟨true,false,false⟩
    let b : Triple := ⟨false,true,false⟩
    let c : Triple := ⟨false,false,true⟩
    median (tree true a) (tree true b) (tree true c) ≠ tree true (median a b c) := by decide

end ThresholdForestParity
