import Std

namespace PortfolioLocalDefects

/-- Unfolding a finite restriction DAG gives a binary game tree. -/
inductive Game where
  | leaf (value : Bool)
  | any (left right : Game)
  | all (left right : Game)

def value : Game → Bool
  | .leaf b => b
  | .any l r => value l || value r
  | .all l r => value l && value r

/-- Positive and negative votes may use different supporting components. -/
def Supported (v : Game → Bool → Prop) : Game → Bool → Prop
  | .leaf b, s => s = b
  | .any l r, true => v l true ∨ v r true
  | .any l r, false => v l false ∧ v r false
  | .all l r, true => v l true ∧ v r true
  | .all l r, false => v l false ∨ v r false

theorem supported_mono {v w : Game → Bool → Prop}
    (h : ∀ g s, v g s → w g s) (g : Game) (s : Bool)
    (ok : Supported v g s) : Supported w g s := by
  cases g with
  | leaf _ => exact ok
  | any l r =>
    cases s
    · exact ⟨h _ _ ok.1, h _ _ ok.2⟩
    · exact ok.elim (fun a => Or.inl (h _ _ a)) (fun b => Or.inr (h _ _ b))
  | all l r =>
    cases s
    · exact ok.elim (fun a => Or.inl (h _ _ a)) (fun b => Or.inr (h _ _ b))
    · exact ⟨h _ _ ok.1, h _ _ ok.2⟩

theorem correct_supported (g : Game) (s : Bool) (correct : s = value g) :
    Supported (fun x b => b = value x) g s := by
  cases g with
  | leaf b => exact correct
  | any l r =>
    cases s <;> cases hl : value l <;> cases hr : value r <;>
      simp_all [Supported, value]
  | all l r =>
    cases s <;> cases hl : value l <;> cases hr : value r <;>
      simp_all [Supported, value]

theorem supported_votes_sound (v : Game → Bool → Prop)
    (ok : ∀ g s, v g s → Supported v g s) (g : Game) (s : Bool) :
    v g s → s = value g := by
  induction g generalizing s with
  | leaf b => exact ok (.leaf b) s
  | any l r hl hr =>
    intro vote
    have step := ok (.any l r) s vote
    cases s <;> simp only [Supported] at step <;> simp only [value]
    · rw [← hl false step.1, ← hr false step.2]; rfl
    · rcases step with a | a
      · rw [← hl true a]; rfl
      · simp [← hr true a]
  | all l r hl hr =>
    intro vote
    have step := ok (.all l r) s vote
    cases s <;> simp only [Supported] at step <;> simp only [value]
    · rcases step with a | a
      · rw [← hl false a]; rfl
      · simp [← hr false a]
    · rw [← hl true step.1, ← hr true step.2]; rfl

def Votes (cast : ι → Game → Bool → Prop) (pool : ι → Prop) (g : Game) (s : Bool) :=
  ∃ i, pool i ∧ cast i g s

def Exact (cast : ι → Game → Bool → Prop) (pool : ι → Prop) :=
  ∀ g s, Votes cast pool g s ↔ s = value g

/-- A violation in the larger pool excludes its voter from every exact subpool. -/
theorem forced_removal {cast : ι → Game → Bool → Prop} {pool sub : ι → Prop}
    (inside : ∀ i, sub i → pool i) (exactSub : Exact cast sub) {i : ι} {g : Game}
    {s : Bool} (vote : cast i g s) (failed : ¬ Supported (Votes cast pool) g s) :
    ¬ sub i := by
  intro belongs
  have actual : s = value g := (exactSub g s).mp ⟨i, belongs, vote⟩
  apply failed
  apply supported_mono _ g s (correct_supported g s actual)
  intro x b good
  obtain ⟨j, hj, votes⟩ := (exactSub x b).mpr good
  exact ⟨j, inside j hj, votes⟩

/-- If both votes have local support, the disagreement propagates to a child. -/
theorem conflict_child (v : Game → Bool → Prop) (g : Game)
    (yes : Supported v g true) (no : Supported v g false) :
    match g with
    | .leaf _ => False
    | .any l r | .all l r => (v l true ∧ v l false) ∨ (v r true ∧ v r false) := by
  cases g with
  | leaf b =>
    change true = b at yes
    change false = b at no
    cases b <;> contradiction
  | any l r =>
    rcases yes with hl | hr
    · exact Or.inl ⟨hl, no.1⟩
    · exact Or.inr ⟨hr, no.2⟩
  | all l r =>
    rcases no with hl | hr
    · exact Or.inl ⟨yes.1, hl⟩
    · exact Or.inr ⟨yes.2, hr⟩

/-- The backward implication for OR lets the final coverage witness be a true leaf. -/
inductive OrTree where
  | leaf (value : Bool)
  | branch (left right : OrTree)

def OrTruth : OrTree → Prop
  | .leaf b => b = true
  | .branch l r => OrTruth l ∨ OrTruth r

theorem positive_portfolio_exact (vote : OrTree → Prop)
    (leaf : ∀ b, vote (.leaf b) ↔ b = true)
    (forward : ∀ l r, vote (.branch l r) → vote l ∨ vote r)
    (backward : ∀ l r, vote l ∨ vote r → vote (.branch l r)) (t : OrTree) :
    vote t ↔ OrTruth t := by
  induction t with
  | leaf b => exact leaf b
  | branch l r hl hr =>
    change vote (.branch l r) ↔ OrTruth l ∨ OrTruth r
    rw [← hl, ← hr]
    exact ⟨forward l r, backward l r⟩

/-- Any exact subpool survives a removal in the generic selector system. -/
theorem forced_by_implication {pool sub : ι → Prop} (inside : ∀ i, sub i → pool i)
    (i : ι) (support : ι → Prop)
    (obligation : sub i → ∃ j, sub j ∧ support j)
    (noWitness : ¬ ∃ j, pool j ∧ support j) : ¬ sub i := by
  intro h
  obtain ⟨j, hj, usable⟩ := obligation h
  exact noWitness ⟨j, inside j hj, usable⟩

end PortfolioLocalDefects
