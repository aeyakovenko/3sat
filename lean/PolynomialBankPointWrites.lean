import Std

namespace PolynomialBankPointWrites

variable {Key Word : Type}

structure Pass (Key Word : Type) where
  perm : Key → Key
  inv : Key → Key
  left_inv : ∀ x, inv (perm x) = x
  right_inv : ∀ y, perm (inv y) = y
  value : Key → Word → Word

def Pass.apply (f : Pass Key Word) (bank : Key → Word) (x : Key) : Word :=
  f.value (f.inv x) (bank (f.inv x))

def Pass.after (g f : Pass Key Word) : Pass Key Word where
  perm x := g.perm (f.perm x)
  inv x := f.inv (g.inv x)
  left_inv x := by simp [g.left_inv, f.left_inv]
  right_inv x := by simp [f.right_inv, g.right_inv]
  value x v := g.value (f.perm x) (f.value x v)

theorem composition (g f : Pass Key Word) (bank : Key → Word) :
    (g.after f).apply bank = g.apply (f.apply bank) := by
  funext x
  simp [Pass.apply, Pass.after, f.right_inv]

def point [DecidableEq Key] (bank : Key → Word) (k : Key) (word : Word) (x : Key) : Word :=
  if x = k then word else bank x

/-- A scalar overwrite follows exactly one original key through an entire
    bulk segment, even when its word transformation is noninjective. -/
theorem scalar_through_pass [DecidableEq Key] (p : Pass Key Word) (bank : Key → Word)
    (k : Key) (word : Word) :
    p.apply (point bank k word) = point (p.apply bank) (p.perm k) (p.value k word) := by
  funext x
  by_cases eq : x = p.perm k
  · subst x
    simp [Pass.apply, point, p.left_inv]
  · have ne : p.inv x ≠ k := by
      intro wrong
      apply eq
      rw [← p.right_inv x, wrong]
    simp [Pass.apply, point, eq, ne]

end PolynomialBankPointWrites
