import Std

/-! A finite three-color tile. All triangle indices and blue-lane positions
start at zero. Its two distinguished lane ports are z 1 and z 2. -/
namespace SevenTrianglePorts

abbrev Color := Fin 3

def triangle (a z b : Color) : Prop := a ≠ z ∧ z ≠ b ∧ a ≠ b

/-- Seven triangles and the blue visit order 1,4,3,5,6,0,2. -/
def Tile (y z : Nat → Color) : Prop :=
  (∀ i, i < 7 → triangle (y i) (z i) (y (i+1))) ∧
  z 1 ≠ z 4 ∧ z 4 ≠ z 3 ∧ z 3 ≠ z 5 ∧ z 5 ≠ z 6 ∧ z 6 ≠ z 0 ∧ z 0 ≠ z 2

/-- The unused color of a pair of distinct colors. -/
def third (a b : Color) : Color :=
  if a ≠ 0 ∧ b ≠ 0 then 0 else if a ≠ 1 ∧ b ≠ 1 then 1 else 2

private theorem determined : ∀ a z b : Color,
    triangle a z b → z = third a b := by unfold triangle; decide

private theorem thirdProps : ∀ a b : Color, a ≠ b → a ≠ third a b ∧ b ≠ third a b := by decide

set_option synthInstance.maxSize 500 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
/-- A small finite calculation after eliminating all seven triangle tips. -/
private theorem reduced : ∀ a b c d e f g h : Color,
    a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ e ∧ e ≠ f ∧ f ≠ g ∧ g ≠ h →
    third b c ≠ third e f ∧ third e f ≠ third d e ∧ third d e ≠ third f g ∧
    third f g ≠ third g h ∧ third g h ≠ third a b ∧ third a b ≠ third c d →
    third b c = a ∧ third c d = a ∧ a ≠ h := by decide

/-- Both exposed lane tips are the left base color, distinct from the right base color. -/
theorem ports_forced (y z : Nat → Color) (H : Tile y z) :
    z 1 = y 0 ∧ z 2 = y 0 ∧ y 0 ≠ y 7 := by
  have ht := H.1
  have tz (i : Nat) (hi : i < 7) : z i = third (y i) (y (i+1)) :=
    determined _ _ _ (ht i hi)
  have adj (i : Nat) (hi : i < 7) : y i ≠ y (i+1) := (ht i hi).2.2
  have hb := H.2
  simp only [tz 0 (by decide), tz 1 (by decide), tz 2 (by decide), tz 3 (by decide),
    tz 4 (by decide), tz 5 (by decide), tz 6 (by decide)] at hb ⊢
  exact reduced (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
    ⟨adj 0 (by decide), adj 1 (by decide), adj 2 (by decide), adj 3 (by decide),
     adj 4 (by decide), adj 5 (by decide), adj 6 (by decide)⟩ hb

/-- Explicit base and tip colors for arbitrary ordered endpoints. -/
def baseWitness (a b : Color) (i : Nat) : Color :=
  [a,b,third a b,b,third a b,a,third a b,b].getD i a

def tipWitness (a b : Color) (i : Nat) : Color :=
  [third a b,a,a,a,b,b,a].getD i a

theorem witness_valid (a b : Color) (hab : a ≠ b) :
    Tile (baseWitness a b) (tipWitness a b) := by
  have h := thirdProps a b hab
  constructor
  · intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases this with h0 | h1 | h2 | h3 | h4 | h5 | h6 <;> subst i <;>
      simp [triangle, baseWitness, tipWitness, List.getD, hab, hab.symm, h.1, h.1.symm, h.2, h.2.symm]
  · simp [tipWitness, List.getD, hab, hab.symm, h.1, h.1.symm]

/-- Exact relation of the two base ports and the first and last exposed tips. -/
theorem boundary_iff (a b s t : Color) :
    (∃ y z, Tile y z ∧ y 0 = a ∧ y 7 = b ∧ z 1 = s ∧ z 2 = t) ↔
      a ≠ b ∧ s = a ∧ t = a := by
  constructor
  · rintro ⟨y,z,H,rfl,rfl,rfl,rfl⟩
    obtain ⟨hs,ht,hab⟩ := ports_forced y z H
    exact ⟨hab,hs,ht⟩
  · rintro ⟨hab,hs,ht⟩
    subst s
    subst t
    exact ⟨baseWitness a b,tipWitness a b,witness_valid a b hab,rfl,rfl,rfl,rfl⟩

private theorem sameThird : ∀ a b s t : Color, a ≠ b →
    s ≠ a → s ≠ b → t ≠ a → t ≠ b → s = t := by decide

/-- Four consecutive triangles with their tips visited in order 1,0,3,2
are inconsistent, whatever the colors or the boundary conditions outside. -/
theorem four_tip_obstruction (y z : Nat → Color)
    (H : ∀ i, i < 4 → triangle (y i) (z i) (y (i+1)))
    (e10 : z 1 ≠ z 0) (e03 : z 0 ≠ z 3) (e32 : z 3 ≠ z 2) : False := by
  have t0 := H 0 (by decide)
  have t1 := H 1 (by decide)
  have t2 := H 2 (by decide)
  have t3 := H 3 (by decide)
  have hz0 : z 0 = y 2 := sameThird (y 1) (z 1) (z 0) (y 2)
    t1.1 t0.2.1 e10.symm t1.2.2.symm t1.2.1.symm
  have hz3 : z 3 = y 2 := sameThird (y 3) (z 2) (z 3) (y 2)
    t2.2.1.symm t3.1.symm e32 t2.2.2 t2.1
  exact e03 (hz0.trans hz3.symm)

/-- The first three triangles have a single coloring with pairwise distinct
tips. Every possible reordering of these or fewer tips is proper. -/
theorem three_tips_pairwise : ∃ y z : Nat → Color,
    (∀ i, i < 3 → triangle (y i) (z i) (y (i+1))) ∧
    (∀ i j, i < 3 → j < 3 → i ≠ j → z i ≠ z j) := by
  refine ⟨fun i => ([0,1,2,0] : List Color).getD i 0,
    fun i => ([2,0,1] : List Color).getD i 0, ?_, ?_⟩
  · intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with h | h | h <;> subst i <;> unfold triangle <;> decide
  · intro i j hi hj hij
    have ti : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have tj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases ti with h | h | h <;> subst i <;> rcases tj with h | h | h <;> subst j <;>
      first | exact False.elim (hij rfl) | decide

end SevenTrianglePorts
