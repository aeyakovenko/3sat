import Std

namespace CfiPackedParity

abbrev eitherPad (a b z : Bool) : Bool :=
  (a || b || z) && (a || b || !z)

theorem forgetPad (a b z : Bool) : eitherPad a b z = (a || b) := by
  cases a <;> cases b <;> cases z <;> decide

def middle (x y z : Bool) : Bool :=
  ((!x) || (!y) || (!z)) && (x || y || (!z)) &&
    (x || (!y) || z) && ((!x) || y || z)

theorem middleParity (x y z : Bool) : middle x y z = !(x ^^ y ^^ z) := by
  cases x <;> cases y <;> cases z <;> decide

theorem twistSum (a twist : Bool) : (a ^^ (a ^^ twist)) = twist := by
  cases a <;> cases twist <;> decide

/-- A degree-three spanning tree rooted at a leaf has at most two children at
    each vertex. Supply a zero-demand dummy leaf for an absent child. -/
inductive Tree
  | leaf (rhs : Bool)
  | fork (rhs : Bool) (left right : Tree)

def Tree.total : Tree → Bool
  | .leaf q => q
  | .fork q l r => q ^^ l.total ^^ r.total

def Tree.feasible : Tree → Bool → Prop
  | .leaf q, outgoing => outgoing = q
  | .fork q l r, outgoing =>
      ∃ a b : Bool, l.feasible a ∧ r.feasible b ∧ (outgoing ^^ a ^^ b) = q

theorem transfer (x a b q : Bool) : ((x ^^ a ^^ b) = q) ↔ (x = (q ^^ a ^^ b)) := by
  cases x <;> cases a <;> cases b <;> cases q <;> decide

theorem feasible_iff_total (t : Tree) (outgoing : Bool) :
    t.feasible outgoing ↔ outgoing = t.total := by
  induction t generalizing outgoing with
  | leaf q => rfl
  | fork q l r il ir =>
    simp only [Tree.feasible, Tree.total, il, ir]
    constructor
    · rintro ⟨a,b,rfl,rfl,h⟩
      exact (transfer _ _ _ _).1 h
    · intro ho
      refine ⟨l.total,r.total,rfl,rfl,?_⟩
      exact (transfer _ _ _ _).2 ho

end CfiPackedParity
