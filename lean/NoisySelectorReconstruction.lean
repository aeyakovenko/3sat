import Std

namespace NoisySelectorReconstruction

/-- A translation-invariant distance on a group of binary words, measured
in integer Hamming positions (before division by the common row length). -/
structure BinaryMetric (V : Type) where
  add : V → V → V
  zero : V
  dist : V → V → Nat
  assoc : ∀ x y z, add (add x y) z = add x (add y z)
  comm : ∀ x y, add x y = add y x
  cancel : ∀ x y, add x (add x y) = y
  shift : ∀ x y z, dist (add x z) (add y z) = dist x y
  reverse : ∀ x y, dist x y = dist y x
  triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
  weight : ∀ x y, dist x y = dist (add x y) zero

theorem any_match_floor (m : BinaryMetric V) (code : V → Prop)
    (closed : ∀ x y, code x → code y → code (m.add x y)) (w : V) (floor : Nat)
    (nearest : ∀ z, code z → floor ≤ m.dist w z)
    (a b : V) (ha : code a) (hb : code b) :
    floor ≤ m.dist a (m.add b w) := by
  have h := nearest (m.add a b) (closed _ _ ha hb)
  rw [m.weight] at h
  rw [m.weight a (m.add b w), ← m.assoc a b w, m.comm (m.add a b) w]
  exact h

theorem translated_match_cost (m : BinaryMetric V) (nearest w x : V) :
    m.dist x (m.add (m.add x nearest) w) = m.dist nearest w := by
  rw [m.weight x, m.assoc, m.cancel, ← m.weight]

theorem permutation_by_translation (m : BinaryMetric V)
    (code : V → Prop) (closed : ∀ x y, code x → code y → code (m.add x y))
    (near : V) (inCode : code near) :
    (∀ x, code x → code (m.add near x)) ∧
    (∀ x, code x → ∃ y, (code y ∧ m.add near y = x) ∧
      ∀ z, code z ∧ m.add near z = x → z = y) := by
  constructor
  · exact fun x inside => closed near x inCode inside
  · intro x inside
    refine ⟨m.add near x, ⟨closed _ _ inCode inside, m.cancel near x⟩, ?_⟩
    intro y h
    rw [← h.2, m.cancel]

theorem sum_bound (m : BinaryMetric V) (x y a b : V) :
    m.dist (m.add x y) (m.add a b) ≤ m.dist x a + m.dist y b := by
  calc
    m.dist (m.add x y) (m.add a b) ≤ m.dist (m.add x y) (m.add a y) +
        m.dist (m.add a y) (m.add a b) := m.triangle _ _ _
    _ = m.dist x a + m.dist y b := by
      congr 1
      · exact m.shift _ _ _
      · rw [m.comm a y, m.comm a b, m.shift]

/-- The nearest prototype to the XOR of two prototypes belongs to the true
sum if the code separation is greater than six prototype radii. -/
theorem prototype_sum (m : BinaryMetric V) (r : Nat) (u v x y good bad other : V)
    (hx : m.dist x u ≤ r) (hy : m.dist y v ≤ r)
    (hg : m.dist good (m.add u v) ≤ r) (hb : m.dist bad other ≤ r)
    (apart : 6*r < m.dist (m.add u v) other) :
    m.dist (m.add x y) good < m.dist (m.add x y) bad := by
  have hsum := sum_bound m x y u v
  have hgood := m.triangle (m.add x y) (m.add u v) good
  have hbad := m.triangle (m.add u v) (m.add x y) other
  have hopper := m.triangle (m.add x y) bad other
  rw [m.reverse (m.add u v) good] at hgood
  rw [m.reverse (m.add u v) (m.add x y)] at hbad
  omega

end NoisySelectorReconstruction
