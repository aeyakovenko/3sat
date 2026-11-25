import Std

namespace UnsignedCubicGadgets
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048

/-- The two ternary vertex tables, with the last argument of R its tap. -/
abbrev E (a b c : Bool) : Prop := a.toNat + b.toNat + c.toNat = 1
abbrev R (a b c : Bool) : Prop := a = b ∧ (c = true → a = true)

abbrev Copy (x y z : Bool) : Prop := x = y ∧ y = z

/-- The three boundary bits are x, y, z and the triangle edges are a, b, c. -/
abbrev Triangle (x y z a b c : Bool) : Prop :=
  R x a c ∧ R y b a ∧ R z c b

theorem triangle_exact :
    ∀ x y z a b c : Bool, Triangle x y z a b c ↔
      Copy x y z ∧ a = x ∧ b = x ∧ c = x := by decide

/-- Two distinct triangle vertices feed E, so no edges become parallel.
The third port z of E is to be connected to a free unary terminator. -/
theorem triangle_and_one_exact :
    ∀ x y u a b c z : Bool, (Triangle x y u a b c ∧ E y u z) ↔
      x = false ∧ y = false ∧ u = false ∧ a = false ∧ b = false ∧
      c = false ∧ z = true := by decide

theorem with_zero_negates : ∀ x y : Bool, E x y false ↔ y = !x := by decide

/-- K4 with one edge deleted. The endpoints missing that edge carry x and y.
At the four vertices the unordered edge names are (x,a,b), (y,c,d),
(a,c,e) and (b,d,e). -/
abbrev DiamondNot (x y a b c d e : Bool) : Prop :=
  R x b a ∧ R y d c ∧ R c e a ∧ E b d e

theorem diamond_not_exact :
    ∀ x y a b c d e : Bool, DiamondNot x y a b c d e ↔
      y = !x ∧ a = false ∧ b = x ∧ c = false ∧ d = y ∧ e = false := by decide

abbrev DiamondImp (x y a b c d e : Bool) : Prop :=
  R a b x ∧ R y d c ∧ R c e a ∧ R b e d

theorem diamond_imp_exact :
    ∀ x y a b c d e : Bool, DiamondImp x y a b c d e ↔
      (x = true → y = true) ∧ a = y ∧ b = y ∧ c = y ∧ d = y ∧ e = y := by decide

/-- Subdivide an edge of K4 and leave a boundary port x at its new vertex.
The five port triples are (x,a,b), (a,c,d), (b,e,f), (c,e,g), (d,f,g). -/
abbrev UnaryFree (x a b c d e f g : Bool) : Prop :=
  R x b a ∧ R a d c ∧ R e f b ∧ R c g e ∧ R f g d

theorem free_exact :
    ∀ x a b c d e f g : Bool, UnaryFree x a b c d e f g ↔
      a = x ∧ b = x ∧ c = x ∧ d = x ∧ e = x ∧ f = x ∧ g = x := by decide

abbrev UnaryZero (x a b c d e f g : Bool) : Prop :=
  R a b x ∧ R c d a ∧ E b e f ∧ R e g c ∧ R d g f

theorem zero_exact :
    ∀ x a b c d e f g : Bool, UnaryZero x a b c d e f g ↔
      x = false ∧ a = false ∧ b = false ∧ c = true ∧ d = true ∧
      e = true ∧ f = false ∧ g = true := by decide

abbrev UnaryOne (x a b c d e f g : Bool) : Prop :=
  R x b a ∧ R c d a ∧ R b f e ∧ R e g c ∧ E d f g

theorem one_exact :
    ∀ x a b c d e f g : Bool, UnaryOne x a b c d e f g ↔
      x = true ∧ a = false ∧ b = true ∧ c = false ∧ d = false ∧
      e = false ∧ f = true ∧ g = false := by decide

/-- K₂,₃ with an external port at each degree-two vertex. The first hub is
R(b,c;a), the other four vertices are E. -/
abbrev ParityGate (x y z a b c d e f : Bool) : Prop :=
  R b c a ∧ E d e f ∧ E x a d ∧ E y b e ∧ E z c f

theorem parity_exact :
    ∀ x y z a b c d e f : Bool, ParityGate x y z a b c d e f ↔
      z = (x ^^ y) ∧ a = false ∧ b = !(x || y || z) ∧ c = b ∧
      d = !x ∧ e = (!y && !b) ∧ f = (!z && !b) := by decide

inductive Gate where
  | exactOne | tap0 | tap1 | tap2

abbrev direct (gate : Gate) (x y z : Bool) : Prop :=
  match gate with
  | .exactOne => E x y z
  | .tap0 => R y z x
  | .tap1 => R x z y
  | .tap2 => R x y z

theorem one_vertex_cannot_copy (gate : Gate) :
    ¬(∀ x y z : Bool, direct gate x y z ↔ Copy x y z) := by
  cases gate <;> decide

/-- In a trivalent graph with b half-edges, 3v=2e+b. For b=3 the previous
theorem excludes the sole nonempty candidate smaller than the triangle. -/
theorem three_port_minimum {v e : Nat} (incidences : 3*v = 2*e+3) (single : v ≠ 1) :
    3 ≤ v := by omega

/-- A two-port gadget containing vertices needs at least four in a simple graph.
A vertex-free unsigned wire enforces equality. -/
theorem two_port_minimum {v e : Nat} (incidences : 3*v = 2*e+2)
    (simple : 2*e ≤ v*(v-1)) : 4 ≤ v := by
  by_cases enough : 4 ≤ v
  · exact enough
  · have casesV : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
    rcases casesV with h | h | h | h <;> subst v <;> simp_all <;> omega

theorem one_port_minimum {v e : Nat} (incidences : 3*v = 2*e+1)
    (simple : 2*e ≤ v*(v-1)) : 5 ≤ v := by
  by_cases enough : 5 ≤ v
  · exact enough
  · have casesV : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 := by omega
    rcases casesV with h | h | h | h | h <;> subst v <;> simp_all <;> omega

end UnsignedCubicGadgets
