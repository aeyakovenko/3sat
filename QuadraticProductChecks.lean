import Std

namespace QuadraticProductChecks

/-- A summand `A[i,k] B[k,j]` in the product entry `(i,j)`. -/
structure Path (ι : Type) where
  row : ι
  mid : ι
  col : ι

def Path.left (p : Path ι) := (p.row, p.mid)
def Path.right (p : Path ι) := (p.mid, p.col)
def Path.output (p : Path ι) := (p.row, p.col)

/-- Two degree-two squarefree monomials can list their factors in either order. -/
def SamePair {α : Type} (a b c d : α) : Prop :=
  (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The four A/B factors obtained from two different middle indices identify
    both paths up to *one common* swap. In particular they determine the pair of
    C-variables that could have contributed this degree-four monomial. -/
theorem quarticPathIsolation {p q r s : Path ι} (h : p.mid ≠ q.mid)
    (hl : SamePair p.left q.left r.left s.left)
    (hr : SamePair p.right q.right r.right s.right) : SamePair p q r s := by
  cases p; cases q; cases r; cases s
  simp [SamePair, Path.left, Path.right] at *
  rcases hl with ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ <;> simp_all

theorem quarticOutputIsolation {p q r s : Path ι} (h : p.mid ≠ q.mid)
    (hl : SamePair p.left q.left r.left s.left)
    (hr : SamePair p.right q.right r.right s.right) :
    SamePair p.output q.output r.output s.output := by
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := quarticPathIsolation h hl hr
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- After eliminating C*C terms, a cubic monomial from A[u,v] C[i,j]
    uniquely identifies the external A-variable and the chosen product path.
    The right edge pins the middle index, different from `v`. -/
theorem leftCubicIsolation {a b : ι × ι} {p q : Path ι}
    (h : a.2 ≠ p.mid) (hl : SamePair a p.left b q.left)
    (hr : p.right = q.right) : a = b ∧ p = q := by
  cases a; cases b; cases p; cases q
  simp [SamePair, Path.left, Path.right] at *
  rcases hl with ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ <;> simp_all

/-- The transposed pivot isolates B[u,v] C[i,j]. -/
theorem rightCubicIsolation {a b : ι × ι} {p q : Path ι}
    (h : a.1 ≠ p.mid) (hr : SamePair a p.right b q.right)
    (hl : p.left = q.left) : a = b ∧ p = q := by
  cases a; cases b; cases p; cases q
  simp [SamePair, Path.left, Path.right] at *
  rcases hr with ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ <;> simp_all

end QuadraticProductChecks
