import Std

namespace OnePointColorCore

/-- Two vertices adjacent to each end of an edge agree in a three-coloring. -/
theorem diamond : ∀ (p q s t : Fin 3), p ≠ q →
    s ≠ p → s ≠ q → t ≠ p → t ≠ q → s = t := by decide

/-- The seven selected vertices and eleven selected edges on each negative rung. -/
theorem spindle (h : Nat → Fin 3) (a c d : Nat)
    (r01 : h 0 ≠ h 1) (r12 : h 1 ≠ h 2) (r23 : h 2 ≠ h 3)
    (r3a : h 3 ≠ h a) (rcd : h c ≠ h d)
    (b1c : h 1 ≠ h c) (bca : h c ≠ h a) (bad : h a ≠ h d)
    (bd3 : h d ≠ h 3) (b30 : h 3 ≠ h 0) (b02 : h 0 ≠ h 2) : False := by
  have left := diamond (h 0) (h 2) (h 1) (h 3) b02 (Ne.symm r01) r12 b30 (Ne.symm r23)
  have right := diamond (h a) (h d) (h 3) (h c) bad r3a (Ne.symm bd3) bca rcd
  exact b1c (left.trans right)

/-- Two proper clauses padded with opposite signs of a common pin enforce the edge. -/
theorem pairedClause (a b z : Prop) :
    (¬a ∨ ¬b ∨ z) ∧ (¬a ∨ ¬b ∨ ¬z) → ¬(a ∧ b) := by
  rintro ⟨pos, neg⟩ ⟨ha, hb⟩
  have hz : z := pos.resolve_left (fun f => f ha) |>.resolve_left (fun f => f hb)
  exact (neg.resolve_left (fun f => f ha) |>.resolve_left (fun f => f hb)) hz

end OnePointColorCore
