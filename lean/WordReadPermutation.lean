import Std

namespace WordReadPermutation

/-- A permutation of the word slots, represented together with its inverse. -/
structure Permutation (B : Nat) where
  forward : Fin B → Fin B
  backward : Fin B → Fin B
  backward_forward : ∀ i, backward (forward i) = i
  forward_backward : ∀ i, forward (backward i) = i

private def exchange {B : Nat} (a b z : Fin B) : Fin B :=
  if z = a then b else if z = b then a else z

private theorem exchanged_twice {B : Nat} (a b z : Fin B) :
    exchange a b (exchange a b z) = z := by
  by_cases e : a = b
  · subst b
    by_cases h : z = a <;> simp [exchange, h]
  · by_cases h₁ : z = a
    · subst z
      simp [exchange, Ne.symm e]
    · by_cases h₂ : z = b
      · subst z
        simp [exchange, h₁]
      · simp [exchange, h₁, h₂]

private def changeOutput {B : Nat} (p : Permutation B) (a b : Fin B) : Permutation B where
  forward i := exchange a b (p.forward i)
  backward j := p.backward (exchange a b j)
  backward_forward i := by rw [exchanged_twice, p.backward_forward]
  forward_backward j := by rw [p.forward_backward, exchanged_twice]

/-- Repeated observations are permitted. Every destination has at most one observed
    source; every source has at most one observed destination. -/
theorem observations_extend {B : Nat} (R : Fin B → Fin B → Prop)
    (source_unique : ∀ {i j j'}, R i j → R i j' → j = j')
    (destination_unique : ∀ {i i' j}, R i j → R i' j → i = i') :
    ∃ p : Permutation B, ∀ i j, R i j → p.forward i = j := by
  classical
  have partial_extension (slots : List (Fin B)) :
      ∃ p : Permutation B, ∀ i ∈ slots, ∀ j, R i j → p.forward i = j := by
    induction slots with
    | nil =>
      exact ⟨⟨id, id, fun _ => rfl, fun _ => rfl⟩, by simp⟩
    | cons head tail ih =>
      obtain ⟨p, holds⟩ := ih
      by_cases observed : ∃ s, R head s
      · obtain ⟨s, observed⟩ := observed
        refine ⟨changeOutput p (p.forward head) s, ?_⟩
        intro i hi j hij
        by_cases e : i = head
        · subst i
          have same := source_unique observed hij
          simp [changeOutput, exchange, same]
        · have ht := (List.mem_cons.mp hi).resolve_left e
          have image_ne : p.forward i ≠ p.forward head := by
            intro eq
            exact e (by simpa [p.backward_forward] using congrArg p.backward eq)
          have source_ne : p.forward i ≠ s := by
            rw [holds i ht j hij]
            intro eq
            subst j
            exact e (destination_unique hij observed)
          simpa [changeOutput, exchange, image_ne, source_ne] using holds i ht j hij
      · refine ⟨p, ?_⟩
        intro i hi j hij
        rcases List.mem_cons.mp hi with eq | ht
        · subst i
          exact (observed ⟨j, hij⟩).elim
        · exact holds i ht j hij
  obtain ⟨p, holds⟩ := partial_extension (List.ofFn (fun i : Fin B => i))
  refine ⟨p, fun i j hij => holds i ?_ j hij⟩
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- The two collision tests are also necessary. -/
theorem compatibility_iff_extension {B : Nat} (R : Fin B → Fin B → Prop) :
    ((∀ {i j j'}, R i j → R i j' → j = j') ∧
      (∀ {i i' j}, R i j → R i' j → i = i')) ↔
      ∃ p : Permutation B, ∀ i j, R i j → p.forward i = j := by
  constructor
  · rintro ⟨one, two⟩
    exact observations_extend R @one @two
  · rintro ⟨p, hp⟩
    exact ⟨fun h h' => (hp _ _ h).symm.trans (hp _ _ h'),
      fun h h' => by
        simpa [p.backward_forward] using congrArg p.backward ((hp _ _ h).trans (hp _ _ h').symm)⟩

end WordReadPermutation
