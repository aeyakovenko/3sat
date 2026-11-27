import Std.Tactic.BVDecide

namespace CollisionFilterRectangle

/-- The actual masks in one plane have even parity on three coordinates. -/
abbrev EvenMask (x : BitVec 3) : Prop :=
  Bool.xor (x.getLsbD 0) (Bool.xor (x.getLsbD 1) (x.getLsbD 2)) = false

/-- Two independent coordinates pick a combination of two columns. -/
def combine (a b : BitVec 3) (u : BitVec 2) : BitVec 3 :=
  (if u.getLsbD 0 then a else 0) ^^^ (if u.getLsbD 1 then b else 0)

def mask (u : BitVec 2) : BitVec 3 := combine 3 5 u

theorem even_coordinates : ∀ x : BitVec 3, EvenMask x ↔ ∃ u, mask u = x := by
  decide

private theorem coordinates_zero : ∀ u : BitVec 2, mask u = 0 ↔ u = 0 := by
  decide

/-- Fifteen nonzero coefficient pairs cannot all give unequal outputs.
The bit-vector decision tactic checks the resulting twelve-bit tautology. -/
theorem column_collision : ∀ a b c d : BitVec 3, ∃ u v : BitVec 2,
    (u ≠ 0 ∨ v ≠ 0) ∧ combine a b u = combine c d v := by
  intro a b c d
  apply Classical.byContradiction
  intro none
  have gap (u v : BitVec 2) (nz : u ≠ 0 ∨ v ≠ 0) :
      combine a b u ≠ combine c d v := fun eq => none ⟨u, v, nz, eq⟩
  have gap01 := gap 0 1 (by decide)
  have gap02 := gap 0 2 (by decide)
  have gap03 := gap 0 3 (by decide)
  have gap10 := gap 1 0 (by decide)
  have gap11 := gap 1 1 (by decide)
  have gap12 := gap 1 2 (by decide)
  have gap13 := gap 1 3 (by decide)
  have gap20 := gap 2 0 (by decide)
  have gap21 := gap 2 1 (by decide)
  have gap22 := gap 2 2 (by decide)
  have gap23 := gap 2 3 (by decide)
  have gap30 := gap 3 0 (by decide)
  have gap31 := gap 3 1 (by decide)
  have gap32 := gap 3 2 (by decide)
  have gap33 := gap 3 3 (by decide)
  simp [combine] at gap01 gap02 gap03 gap10 gap11 gap12 gap13 gap20 gap21 gap22 gap23 gap30 gap31 gap32 gap33
  bv_decide

/-- No behavior is required on odd masks. -/
structure LinearOnEven (f : BitVec 3 → BitVec 3) : Prop where
  zero : f 0 = 0
  add : ∀ x y, EvenMask x → EvenMask y → f (x ^^^ y) = f x ^^^ f y

private theorem eval_mask (f : BitVec 3 → BitVec 3) (linear : LinearOnEven f)
    (u : BitVec 2) : f (mask u) = combine (f 3) (f 5) u := by
  have h : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by
    have all : ∀ u : BitVec 2, u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by decide
    exact all u
  rcases h with h | h | h | h <;> subst u
  · simpa [mask, combine] using linear.zero
  · simp [mask, combine]
  · simp [mask, combine]
  · simpa [mask, combine] using linear.add 3 5 (by decide) (by decide)

/-- A rectangle supplies an even input on each plane; at least one is nonzero,
and the two output words coincide. A zero mask on one side is allowed. -/
theorem rectangle_collision (f g : BitVec 3 → BitVec 3)
    (hf : LinearOnEven f) (hg : LinearOnEven g) :
    ∃ x y, EvenMask x ∧ EvenMask y ∧ (x ≠ 0 ∨ y ≠ 0) ∧ f x = g y := by
  obtain ⟨u, v, nonzero, equal⟩ := column_collision (f 3) (f 5) (g 3) (g 5)
  refine ⟨mask u, mask v, (even_coordinates _).mpr ⟨u, rfl⟩,
    (even_coordinates _).mpr ⟨v, rfl⟩, ?_, ?_⟩
  · rcases nonzero with h | h
    · exact Or.inl (fun z => h ((coordinates_zero u).mp z))
    · exact Or.inr (fun z => h ((coordinates_zero v).mp z))
  · simpa only [eval_mask f hf, eval_mask g hg] using equal

/-- If neither plane has its own nonzero kernel mask, both masks must be
nonzero and their common image is nonzero. -/
theorem both_nonzero (f g : BitVec 3 → BitVec 3)
    (hf : LinearOnEven f) (hg : LinearOnEven g)
    (fKernel : ∀ x, EvenMask x → f x = 0 → x = 0)
    (gKernel : ∀ y, EvenMask y → g y = 0 → y = 0) :
    ∃ x y, EvenMask x ∧ EvenMask y ∧ x ≠ 0 ∧ y ≠ 0 ∧ f x = g y ∧ f x ≠ 0 := by
  obtain ⟨x, y, ex, ey, nz, same⟩ := rectangle_collision f g hf hg
  have imageNZ : f x ≠ 0 := by
    intro z
    have xz := fKernel x ex z
    have yz := gKernel y ey (same.symm.trans z)
    exact nz.elim (fun h => h xz) (fun h => h yz)
  exact ⟨x, y, ex, ey, fun xz => imageNZ (xz ▸ hf.zero),
    fun yz => imageNZ (same.trans (yz ▸ hg.zero)), same, imageNZ⟩

end CollisionFilterRectangle
