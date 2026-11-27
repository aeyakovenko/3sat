import Std

/-! Fourth polarized coefficient of the graph of a Boolean outer product.
Each of the four output directions has its own pair of index classes. The two
row and two column labels in an accepted placement must be unique within
their class. This equivalence and the diagonal of the fourth block give an
explicit bijection with the multiplication triples. No assertions on formal
circuit size or the input arithmetic exponent are encoded here. -/
namespace OuterProductBoundaryCycle

structure Placement (I : Type) where
  row1 : I
  col1 : I
  row2 : I
  col2 : I
  row3 : I
  col3 : I
  row4 : I
  col4 : I

def usedOnlyTwoRows {I : Type} (p : Placement I) : Prop :=
  ∃ u w : I, p.row1 = u ∧ p.row4 = u ∧ p.row2 = w ∧ p.row3 = w

def usedOnlyTwoCols {I : Type} (p : Placement I) : Prop :=
  ∃ v s : I, p.col1 = v ∧ p.col2 = v ∧ p.col3 = s ∧ p.col4 = s

def survives {I : Type} (p : Placement I) : Prop :=
  usedOnlyTwoRows p ∧ usedOnlyTwoCols p ∧ p.col4 = p.row4

def place {I : Type} (i j k : I) : Placement I :=
  ⟨i, j, k, j, k, i, i, i⟩

theorem triangle_survives {I : Type} (i j k : I) : survives (place i j k) :=
  ⟨⟨i, k, rfl, rfl, rfl, rfl⟩, ⟨j, i, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem reconstruct {I : Type} (p : Placement I) (h : survives p) :
    p = place p.row1 p.col1 p.row2 := by
  rcases p with ⟨a,b,c,d,e,f,g,k⟩
  obtain ⟨⟨u,w,rfl,rg,rfl,re⟩,⟨v,s,rfl,rd,rfl,rk⟩,diag⟩ := h
  simp_all [place]

/-- Every surviving placement occurs exactly once in the trilinear contraction. -/
theorem unique_terms {I : Type} (p : Placement I) (h : survives p) :
    ∃ t : I × I × I, (place t.1 t.2.1 t.2.2 = p) ∧
      ∀ z : I × I × I, place z.1 z.2.1 z.2.2 = p → z = t := by
  refine ⟨(p.row1, p.col1, p.row2), (reconstruct p h).symm, ?_⟩
  rintro ⟨i,j,k⟩ hz
  cases hz
  rfl

end OuterProductBoundaryCycle
