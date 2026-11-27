import Std

namespace PullbackEvaluation

inductive Tree where
  | lit (b : Bool)
  | unary (f : Bool → Bool) (t : Tree)
  | binary (f : Bool → Bool → Bool) (a b : Tree)

def value : Tree → Bool
  | .lit b => b
  | .unary f t => f (value t)
  | .binary f a b => f (value a) (value b)

/-- One saved continuation is charged only while the first child is evaluated. -/
def Fits : Tree → Nat → Prop
  | .lit _, _ => True
  | .unary _ t, r => Fits t r
  | .binary _ _ _, 0 => False
  | .binary _ a b, r+1 =>
    (Fits a r ∧ Fits b (r+1)) ∨ (Fits b r ∧ Fits a (r+1))

def Produces : Tree → Nat → Bool → Prop
  | .lit b, _, v => v = b
  | .unary f t, r, v => ∃ x, Produces t r x ∧ v = f x
  | .binary _ _ _, 0, _ => False
  | .binary f a b, r+1, v => ∃ x y,
    ((Produces a r x ∧ Produces b (r+1) y) ∨
     (Produces b r y ∧ Produces a (r+1) x)) ∧ v = f x y

theorem exact (t : Tree) (r : Nat) (v : Bool) :
    Produces t r v ↔ Fits t r ∧ v = value t := by
  induction t generalizing r v with
  | lit b => simp [Produces, Fits, value]
  | unary f t ih =>
    change (∃ x, Produces t r x ∧ v = f x) ↔ Fits t r ∧ v = f (value t)
    constructor
    · rintro ⟨x, hx, hv⟩
      obtain ⟨hf, hval⟩ := (ih r x).mp hx
      exact ⟨hf, hval ▸ hv⟩
    · rintro ⟨hf, hv⟩
      exact ⟨value t, (ih r (value t)).mpr ⟨hf,rfl⟩, hv⟩
  | binary f a b ia ib =>
    cases r with
    | zero => simp [Produces, Fits]
    | succ r =>
      simp only [Produces, Fits, value, ia, ib]
      constructor
      · rintro ⟨x, y, (⟨⟨ha, rfl⟩, ⟨hb, rfl⟩⟩ | ⟨⟨hb, rfl⟩, ⟨ha, rfl⟩⟩), hv⟩
        · exact ⟨Or.inl ⟨ha,hb⟩,hv⟩
        · exact ⟨Or.inr ⟨hb,ha⟩,hv⟩
      · rintro ⟨(⟨ha,hb⟩ | ⟨hb,ha⟩), hv⟩
        · exact ⟨value a,value b,Or.inl ⟨⟨ha,rfl⟩,⟨hb,rfl⟩⟩,hv⟩
        · exact ⟨value a,value b,Or.inr ⟨⟨hb,rfl⟩,⟨ha,rfl⟩⟩,hv⟩

end PullbackEvaluation
