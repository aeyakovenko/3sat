import Std

namespace NonlinearSeedChoices

variable {I : Type}

def BinaryOK (a b c x : I → Bool) : Prop := ∀ i j,
  (x i = a i ∧ x j = a j) ∨ (x i = b i ∧ x j = b j) ∨
  (x i = c i ∧ x j = c j)

def threeXor (a b c : I → Bool) (i : I) := (a i ^^ b i) ^^ c i

private theorem owner (a b c : Bool) (h : ¬ (a = b ∧ b = c)) :
    let x := (a ^^ b) ^^ c
    (x = a ∧ x ≠ b ∧ x ≠ c) ∨ (x = b ∧ x ≠ a ∧ x ≠ c) ∨
    (x = c ∧ x ≠ a ∧ x ≠ b) := by
  revert h
  cases a <;> cases b <;> cases c <;> decide

theorem xor_in_hull (a b c : I → Bool) (h : BinaryOK a b c (threeXor a b c)) :
    threeXor a b c = a ∨ threeXor a b c = b ∨ threeXor a b c = c := by
  classical
  by_cases hall : ∀ i, a i = b i ∧ b i = c i
  · left
    funext i
    rcases hall i with ⟨h₁,h₂⟩
    simp [threeXor, h₁, h₂]
  · simp only [Classical.not_forall] at hall
    obtain ⟨i, hi⟩ := hall
    rcases owner (a i) (b i) (c i) hi with ha | hb | hc
    · left
      funext j
      rcases h i j with aok | bok | cok
      · exact aok.2
      · exact (ha.2.1 bok.1).elim
      · exact (ha.2.2 cok.1).elim
    · right; left
      funext j
      rcases h i j with aok | bok | cok
      · exact (hb.2.1 aok.1).elim
      · exact bok.2
      · exact (hb.2.2 cok.1).elim
    · right; right
      funext j
      rcases h i j with aok | bok | cok
      · exact (hc.2.1 aok.1).elim
      · exact (hc.2.2 bok.1).elim
      · exact cok.2

theorem three_affine_binary (a b c x : I → Bool)
    (aff : x = a ∨ x = b ∨ x = c ∨ x = threeXor a b c) (h : BinaryOK a b c x) :
    x = a ∨ x = b ∨ x = c := by
  rcases aff with e | e | e | e
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)
  · subst x
    exact xor_in_hull a b c h

theorem marked_tree_gluing {S V : Type} (marked : S → Bool)
    (full hull : S → V → Prop) (honest abort : S → V)
    (hon : ∀ s, marked s = true → full s (honest s))
    (weaken : ∀ s v, full s v → hull s v)
    (ab : ∀ s, hull s (abort s)) :
    ∃ choice : S → V, (∀ s, hull s (choice s)) ∧
      (∀ s, marked s = true → full s (choice s)) := by
  refine ⟨fun s => if marked s then honest s else abort s, ?_, ?_⟩
  · intro s
    cases e : marked s with
    | false => simpa [e] using ab s
    | true => simpa [e] using weaken s _ (hon s e)
  · intro s hs
    simpa [hs] using hon s hs

theorem split_from_edges (a p l r : Bool) (parity : p = (l ^^ r))
    (left : l = true → a = false) (right : r = true → a = true) :
    (p = (l || r)) ∧ ¬ (l = true ∧ r = true) := by
  revert parity left right
  cases a <;> cases p <;> cases l <;> cases r <;> decide

end NonlinearSeedChoices
