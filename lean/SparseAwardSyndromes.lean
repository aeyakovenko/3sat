import Std

namespace SparseAwardSyndromes

abbrev Word := Nat → Bool

def diff (x y : Word) : Word := fun i => x i ^^ y i

def total : List Word → Word
  | [] => fun _ => false
  | v :: vs => fun i => v i ^^ total vs i

theorem total_false_at (xs : List Word) (i : Nat)
    (h : ∀ v ∈ xs, v i = false) : total xs i = false := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    have hv : v i = false := h _ (by simp)
    have ht : total vs i = false := ih (fun w hw => h _ (by simp [hw]))
    simp [total, hv, ht]

/-- If the selected witnesses are sorted by first disagreement, the first
one prevents any nonempty selected sum from vanishing. -/
theorem distinguished_sum (v : Word) (xs : List Word) (i : Nat)
    (hv : v i = true) (h : ∀ w ∈ xs, w i = false) :
    total (v :: xs) i = true := by
  simp [total, hv, total_false_at xs i h]

def agreesBefore (x y : Word) (i : Nat) : Prop := ∀ t < i, x t = y t

/-- A sparse alternative matching an authenticated prefix and disagreeing
at a target has a first disagreement in the intervening band. -/
theorem first_in_band (x y : Word) {l r : Nat} (prefixOk : agreesBefore x y l)
    (disagree : x r ≠ y r) :
    ∃ i, l ≤ i ∧ i ≤ r ∧ diff x y i = true ∧ ∀ j < i, diff x y j = false := by
  have findFirst : ∀ t, (∃ j ≤ t, x j ≠ y j) →
      ∃ i ≤ t, x i ≠ y i ∧ ∀ j < i, x j = y j := by
    intro t
    induction t with
    | zero =>
      rintro ⟨j, hj, h⟩
      have : j = 0 := by omega
      subst j
      exact ⟨0, by omega, h, fun j hj => False.elim (by omega)⟩
    | succ t ih =>
      intro hex
      by_cases prev : ∃ j ≤ t, x j ≠ y j
      · obtain ⟨v, hv, dv, before⟩ := ih prev
        exact ⟨v, by omega, dv, before⟩
      · obtain ⟨v,hv,dv⟩ := hex
        have eq : v = t+1 := by
          by_cases h : v = t+1
          · exact h
          · exact False.elim (prev ⟨v, by omega, dv⟩)
        subst v
        refine ⟨t+1, by omega, dv, ?_⟩
        intro j hj
        by_cases same : x j = y j
        · exact same
        · exact False.elim (prev ⟨j, by omega, same⟩)
  obtain ⟨i,hir,bad,early⟩ := findFirst r ⟨r, Nat.le_refl _, disagree⟩
  have hli : l ≤ i := by
    by_cases h : l ≤ i
    · exact h
    · exact False.elim (bad (prefixOk i (by omega)))
  refine ⟨i, hli, hir, ?_, ?_⟩
  · unfold diff
    cases hx : x i <;> cases hy : y i <;> simp_all
  · intro j hj
    simp [diff, early j hj]

/-- The sparse zone bound compounds over all independently named positions. -/
theorem iterated_zone_bound (s : Nat → Nat) (width cap : Nat)
    (shrink : ∀ i, width * s (i+1) ≤ cap * s i) (t : Nat) :
    width^t * s t ≤ cap^t * s 0 := by
  induction t with
  | zero => simp
  | succ i ih =>
    calc
      width^(i+1) * s (i+1) = width^i * (width * s (i+1)) := by
        simp [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ width^i * (cap * s i) := Nat.mul_le_mul_left _ (shrink i)
      _ = cap * (width^i * s i) := by ac_rfl
      _ ≤ cap * (cap^i * s 0) := Nat.mul_le_mul_left _ ih
      _ = cap^(i+1) * s 0 := by rw [Nat.pow_succ]; ac_rfl

/-- An observed prefix pattern forces the last bit if the extended pattern
is absent from the whole window. Symbols between the match and the endpoint
are unrestricted. -/
theorem forced_endpoint (pattern early gap : List Bool) (c last : Bool)
    (seen : pattern.Sublist early)
    (absent : ¬(pattern ++ [c]).Sublist ((early ++ gap) ++ [last])) :
    last ≠ c := by
  intro eq
  subst last
  apply absent
  exact (List.append_sublist_append_right [c]).2
    (List.sublist_append_of_sublist_left seen)

end SparseAwardSyndromes
