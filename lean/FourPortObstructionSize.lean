import Std

namespace FourPortObstructionSize

/-- Degree sum, density, and tree spans in the selected equality components. -/
theorem counts (v e k rows : Nat) (deg : 2 * e ≤ 3 * v + k)
    (density : 5 * v ≤ 3 * e + 2) (span : rows ≤ 2 * v + k) :
    v ≤ 3*k+4 ∧ e ≤ 5*k+6 ∧ rows ≤ 7*k+8 := by omega

theorem non_ore_counts (v e k rows : Nat) (deg : 2 * e ≤ 3 * v + k)
    (density : 5 * v ≤ 3 * e + 1) (span : rows ≤ 2 * v + k) :
    v ≤ 3*k+2 ∧ rows ≤ 7*k+4 := by omega

theorem triangle_free_counts (v e k rows : Nat) (deg : 2 * e ≤ 3 * v + k)
    (density : 5 * v + 2 ≤ 3 * e) (span : rows ≤ 2 * v + k) :
    v + 4 ≤ 3*k ∧ rows + 8 ≤ 7*k := by omega

/-- Gallai degree-three components, counted by vertices, edges, components
and pairwise vertex-disjoint cyclic blocks. -/
theorem kernel_counts (lo hi eLow eTotal comps cycles boundary : Nat)
    (forest : eLow + comps = lo + cycles) (disjoint : 3*cycles ≤ lo)
    (lowDeg : 3*lo = 2*eLow + boundary) (budget : boundary ≤ 4*hi)
    (sumDeg : 2*eTotal ≤ 3*lo + 4*hi) :
    lo + 6*comps ≤ 12*hi ∧ lo + hi + 6*comps ≤ 13*hi ∧
    eTotal + 9*comps ≤ 20*hi := by omega

/-- A coloring of an Ore composition induces a coloring of one parent:
the edge side if the terminals differ, and the unsplit side if they agree. -/
theorem glue_rejects {Color : Type} {a b : Color} {G A B : Prop}
    (edgeSide : G → a ≠ b → A) (splitSide : G → a = b → B)
    (leftNo : ¬ A) (rightNo : ¬ B) : ¬ G := by
  intro h
  by_cases same : a = b
  · exact rightNo (splitSide h same)
  · exact leftNo (edgeSide h same)

end FourPortObstructionSize
