import Std

namespace SparseEditTreeExtension

/-- Attach the root of the right tree as a child of the root of the left tree. -/
inductive Tree (α : Type) where
  | leaf
  | attach (left right : Tree α) (rel : α → α → Prop)

variable {α : Type} (a : α)

def Setting : Tree α → Type
  | .leaf => α
  | .attach l r _ => Setting l × Setting r

def root : (t : Tree α) → Setting t → α
  | .leaf, x => x
  | .attach l _ _, x => root l x.1

def plain : (t : Tree α) → Setting t
  | .leaf => a
  | .attach l r _ => (plain l, plain r)

def valid : (t : Tree α) → Setting t → Prop
  | .leaf, _ => True
  | .attach l r rel, x =>
    valid l x.1 ∧ valid r x.2 ∧ rel (root l x.1) (root r x.2)

def good : Tree α → Prop
  | .leaf => True
  | .attach l r rel => good l ∧ good r ∧ rel a a ∧
    ((∃ v, v ≠ a ∧ rel a v) ∨ ∀ u, ∃ v, rel u v)

theorem plain_root (t : Tree α) : root t (plain a t) = a := by
  induction t with
  | leaf => rfl
  | attach _ _ _ ih _ => exact ih

theorem plain_valid (t : Tree α) (h : good a t) : valid t (plain a t) := by
  induction t with
  | leaf => trivial
  | attach l r rel il ir =>
    obtain ⟨hl, hr, hrel, _⟩ := h
    exact ⟨il hl, ir hr, by simpa only [plain, plain_root] using hrel⟩

theorem extension (t : Tree α) (h : good a t) :
    (∃ s, valid t s ∧ root t s = a ∧ s ≠ plain a t) ∨
      ∀ v, ∃ s, valid t s ∧ root t s = v := by
  induction t with
  | leaf => exact Or.inr (fun v => ⟨v, trivial, rfl⟩)
  | attach l r rel il ir =>
    obtain ⟨hl, hr, hcenter, hedges⟩ := h
    rcases il hl with ⟨u, hu, ru, hdiff⟩ | allLeft
    · left
      refine ⟨(u, plain a r), ⟨hu, plain_valid a r hr, ?_⟩, ru, ?_⟩
      · rwa [ru, plain_root]
      · exact fun he => hdiff (congrArg Prod.fst he)
    rcases ir hr with ⟨v, hv, rv, hdiff⟩ | allRight
    · left
      refine ⟨(plain a l, v), ⟨plain_valid a l hl, hv, ?_⟩, plain_root a l, ?_⟩
      · rwa [plain_root, rv]
      · exact fun he => hdiff (congrArg Prod.snd he)
    rcases hedges with ⟨v, hv, edge⟩ | total
    · obtain ⟨s, hs, rs⟩ := allRight v
      left
      refine ⟨(plain a l, s), ⟨plain_valid a l hl, hs, ?_⟩, plain_root a l, ?_⟩
      · rwa [plain_root, rs]
      · intro he
        exact hv (rs.symm.trans ((congrArg (root r) (congrArg Prod.snd he)).trans (plain_root a r)))
    · right
      intro v
      obtain ⟨u, hu, ru⟩ := allLeft v
      obtain ⟨v', hedge⟩ := total v
      obtain ⟨s, hs, rs⟩ := allRight v'
      exact ⟨(u,s), ⟨hu,hs, by rwa [ru,rs]⟩,ru⟩

theorem some_noncenter (t : Tree α) (h : good a t) (b : α) (hne : b ≠ a) :
    ∃ s, valid t s ∧ s ≠ plain a t := by
  rcases extension a t h with ⟨s, hs, _, hdiff⟩ | all
  · exact ⟨s,hs,hdiff⟩
  · obtain ⟨s, hs, rs⟩ := all b
    exact ⟨s,hs, fun he => hne (rs.symm.trans ((congrArg (root t) he).trans (plain_root a t)))⟩

theorem clock (m k c T : Nat) (counts : 2*m ≤ T+c)
    (pack : c*(k+1) ≤ m) : 2*m - m/(k+1) ≤ T := by
  have hc : c ≤ m/(k+1) := (Nat.le_div_iff_mul_le (by omega)).2 pack
  omega

end SparseEditTreeExtension
