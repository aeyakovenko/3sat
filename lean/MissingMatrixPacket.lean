import Std

namespace MissingMatrixPacket

variable {κ : Type}

def dot (ks : List κ) (a b : κ → Bool) : Bool :=
  match ks with
  | [] => false
  | k :: rest => (a k && b k) ^^ dot rest a b

private theorem dot_append (l r : List κ) (a b : κ → Bool) :
    dot (l ++ r) a b = (dot l a b ^^ dot r a b) := by
  induction l with
  | nil => simp [dot]
  | cons h t ih => simp [dot, ih, Bool.xor_assoc]

/-- With one inner index outstanding, the rest of the selected dot
product can be accumulated before learning its missing operand bit. -/
theorem missing_term (left right : List κ) (h : κ) (a b : κ → Bool) :
    dot (left ++ h :: right) a b =
      ((dot left a b ^^ dot right a b) ^^ (a h && b h)) := by
  rw [dot_append, dot]
  cases dot left a b <;> cases dot right a b <;> cases a h <;> cases b h <;> decide

private theorem exchange (a b c d : Bool) :
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem dot_add_left (ks : List κ) (a r b : κ → Bool) :
    dot ks (fun i => a i ^^ r i) b = (dot ks a b ^^ dot ks r b) := by
  induction ks with
  | nil => rfl
  | cons h t ih =>
    simp only [dot, ih]
    have step : ((a h ^^ r h) && b h) = ((a h && b h) ^^ (r h && b h)) := by
      cases a h <;> cases r h <;> cases b h <;> decide
    exact (congrArg (fun z => z ^^ (dot t a b ^^ dot t r b)) step).trans (exchange _ _ _ _)

private theorem dot_symm (ks : List κ) (a b : κ → Bool) : dot ks a b = dot ks b a := by
  induction ks with
  | nil => rfl
  | cons h t ih => simp only [dot, ih, Bool.and_comm (a h) (b h)]

private theorem dot_add_right (ks : List κ) (a b s : κ → Bool) :
    dot ks a (fun i => b i ^^ s i) = (dot ks a b ^^ dot ks a s) := by
  rw [dot_symm, dot_add_left, dot_symm ks b a, dot_symm ks s a]

/-- Unmask the product of one row and one column once the four
independently queried matrix products have certified this entry. -/
theorem four_products (ks : List κ) (a b r s : κ → Bool) :
    (((dot ks (fun i => a i ^^ r i) (fun i => b i ^^ s i) ^^
       dot ks r (fun i => b i ^^ s i)) ^^ dot ks (fun i => a i ^^ r i) s) ^^
       dot ks r s) = dot ks a b := by
  simp only [dot_add_left, dot_add_right]
  cases dot ks a b <;> cases dot ks a s <;> cases dot ks r b <;> cases dot ks r s <;> decide

end MissingMatrixPacket
