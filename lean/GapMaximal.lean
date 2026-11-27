import Std

namespace GapMaximal

/-- We list gaps newest first. Credit is the positive surplus over the
    threshold on the most favorable prefix, including the empty prefix. -/
def credit (t : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (credit t xs + x) - t

theorem credit_iff (t : Nat) (xs : List Nat) (k : Nat) :
    k ≤ credit t xs ↔ ∃ p s, xs = p ++ s ∧ k + t * p.length ≤ p.sum := by
  induction xs generalizing k with
  | nil =>
    constructor
    · intro h
      exact ⟨[], [], rfl, by simpa [credit] using h⟩
    · rintro ⟨p,s,h,ok⟩
      cases p with
      | nil => simpa [credit] using ok
      | cons a p => simp at h
  | cons x xs ih =>
    constructor
    · intro hk
      by_cases z : k = 0
      · subst k; exact ⟨[], x :: xs, rfl, by simp⟩
      have hneed : k + t - x ≤ credit t xs := by
        simp only [credit] at hk
        omega
      obtain ⟨p,s,h,ok⟩ := (ih _).1 hneed
      refine ⟨x :: p, s, by simp [h], ?_⟩
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one, List.sum_cons]
      omega
    · rintro ⟨p,s,h,ok⟩
      cases p with
      | nil => simp at ok; omega
      | cons y p =>
        have matchHead : x = y ∧ xs = p ++ s := List.cons.inj h
        obtain ⟨rfl, rest⟩ := matchHead
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one, List.sum_cons] at ok
        simp only [credit]
        by_cases short : x ≤ k+t
        · have tail : k + t - x ≤ credit t xs := by
            apply (ih _).2
            exact ⟨p,s,rest,by omega⟩
          omega
        · omega

/-- An endpoint qualifies precisely when a nonempty prefix of the
    newest-first list of gaps has average at least t. -/
theorem hit_iff (t x : Nat) (xs : List Nat) :
    t ≤ credit t xs + x ↔
      ∃ p s, xs = p ++ s ∧ t * (p.length + 1) ≤ x + p.sum := by
  constructor
  · intro h
    obtain ⟨p,s,hp,ok⟩ := (credit_iff t xs (t-x)).1 (by omega)
    exact ⟨p,s,hp,by rw [Nat.mul_add, Nat.mul_one]; omega⟩
  · rintro ⟨p,s,hp,ok⟩
    by_cases hx : x ≥ t
    · omega
    have hc : t - x ≤ credit t xs := by
      apply (credit_iff _ _ _).2
      refine ⟨p,s,hp,?_⟩
      rw [Nat.mul_add, Nat.mul_one] at ok
      omega
    omega

def countHits (t : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if t ≤ credit t xs + x then 1 else 0) + countHits t xs

/-- Sharp one-sided weak inequality for every finite list. For a rational
    threshold a/b, apply the result at a to gaps multiplied by b. -/
theorem weak_maximal (t : Nat) (xs : List Nat) :
    t * countHits t xs + credit t xs ≤ xs.sum := by
  induction xs with
  | nil => simp [countHits, credit]
  | cons x xs ih =>
    by_cases hit : t ≤ credit t xs + x
    · simp [countHits,credit,hit,Nat.mul_add]
      omega
    · simp [countHits,credit,hit]
      omega

end GapMaximal
