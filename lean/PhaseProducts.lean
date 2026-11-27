import Std

namespace PhaseProducts

/-- Each node carries its guessed product and a mark saying whether to repair it. -/
inductive Block (α : Type) where
  | leaf (actual guess : α) (marked : Bool)
  | branch (guess : α) (marked : Bool) (left right : Block α)

def claimed : Block α → α
  | .leaf _ a _ => a
  | .branch a _ _ _ => a

def actual (op : α → α → α) : Block α → α
  | .leaf a _ _ => a
  | .branch _ _ l r => op (actual op l) (actual op r)

/-- All local identities in the subtree hold, irrespective of its marks. -/
def clean (op : α → α → α) : Block α → Prop
  | .leaf a g _ => g = a
  | .branch g _ l r => g = op (claimed l) (claimed r) ∧ clean op l ∧ clean op r

theorem clean_correct (op : α → α → α) (t : Block α) (h : clean op t) :
    claimed t = actual op t := by
  induction t with
  | leaf a g m => exact h
  | branch g m l r ihl ihr =>
    obtain ⟨hg, hl, hr⟩ := h
    change g = op (actual op l) (actual op r)
    rw [hg, ihl hl, ihr hr]

/-- A mark is required at each defective node and each of its ancestors.
    Equivalently every unmarked subtree is clean. Extra marks are permitted. -/
def covered (op : α → α → α) : Block α → Prop
  | .leaf a g m => m = false → g = a
  | .branch g m l r =>
      (m = false → clean op (.branch g m l r)) ∧ covered op l ∧ covered op r

def repair (op : α → α → α) : Block α → α
  | .leaf a g m => if m then a else g
  | .branch g m l r => if m then op (repair op l) (repair op r) else g

theorem repair_correct (op : α → α → α) (t : Block α) (h : covered op t) :
    repair op t = actual op t := by
  induction t with
  | leaf a g m =>
    cases m with
    | false => exact h rfl
    | true => rfl
  | branch g m l r ihl ihr =>
    obtain ⟨unmarked, hl, hr⟩ := h
    cases m with
    | false => exact clean_correct op (.branch g false l r) (unmarked rfl)
    | true =>
      change op (repair op l) (repair op r) = op (actual op l) (actual op r)
      rw [ihl hl, ihr hr]

/-- Local correction in an arbitrary group. The given cancellation law is a
    consequence of associativity, a right inverse and a left identity. -/
theorem correction_at_branch (mul : α → α → α) (inv : α → α)
    (assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
    (cancel : ∀ x z, mul x (mul (inv x) z) = z)
    (a l r u v : α) :
    mul (mul (inv a) (mul l r))
      (mul (mul (inv r) (mul (mul (inv l) u) r)) (mul (inv r) v)) =
    mul (inv a) (mul u v) := by
  simp only [assoc, cancel]

end PhaseProducts
