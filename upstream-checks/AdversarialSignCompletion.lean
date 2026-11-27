import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

namespace AdversarialSignCompletion

open Finset

def survivors (rows : Finset α) (f : α → Fin 8) (y : Fin 8) : Finset α :=
  rows.filter (fun x => f x ≠ y)

theorem choose_sign (rows : Finset α) (f : α → Fin 8) :
    ∃ y, (survivors rows f y).card ≤ 7 * rows.card / 8 := by
  classical
  let size := fun y : Fin 8 => (rows.filter fun a => f a = y).card
  obtain ⟨y, _, hy⟩ := Finset.exists_max_image univ size Finset.univ_nonempty
  have hsum : rows.card = ∑ j : Fin 8, size j := by
    exact Finset.card_eq_sum_card_fiberwise (by simp)
  have upper : rows.card ≤ 8 * size y := by
    rw [hsum]
    calc
      _ ≤ ∑ _ : Fin 8, size y := Finset.sum_le_sum (fun j hj => hy j hj)
      _ = _ := by simp
  have divs : size y + (survivors rows f y).card = rows.card :=
    rows.card_filter_add_card_filter_not (fun a => f a = y)
  exact ⟨y, by omega⟩

def trimmed : Nat → Nat → Nat
  | 0,n => n
  | t+1,n => trimmed t (7*n/8)

theorem trimmed_mono (t : Nat) {a b : Nat} (h : a ≤ b) : trimmed t a ≤ trimmed t b := by
  induction t generalizing a b with
  | zero => exact h
  | succ t ih => exact ih (by omega)

def matchingRows (rows : Finset α) : List ((α → Fin 8) × Fin 8) → Finset α
  | [] => rows
  | (f,y)::tail => matchingRows (survivors rows f y) tail

theorem fix_signs (rows : Finset α) (queries : List (α → Fin 8)) :
    ∃ restrictions : List ((α → Fin 8) × Fin 8),
      restrictions.map Prod.fst = queries ∧
      (matchingRows rows restrictions).card ≤ trimmed queries.length rows.card := by
  induction queries generalizing rows with
  | nil => exact ⟨[],rfl,le_rfl⟩
  | cons q qs ih =>
    obtain ⟨y,hy⟩ := choose_sign rows q
    obtain ⟨rest,hr,hrows⟩ := ih (survivors rows q y)
    refine ⟨(q,y)::rest, by simp [hr], ?_⟩
    exact hrows.trans (trimmed_mono qs.length hy)

theorem numerical_bound : trimmed 63 18758 = 0 := by decide

theorem kill_sixty_three (rows : Finset α) (queries : List (α → Fin 8))
    (length_ok : queries.length = 63) (size_ok : rows.card ≤ 18758) :
    ∃ restrictions : List ((α → Fin 8) × Fin 8),
      restrictions.map Prod.fst = queries ∧ matchingRows rows restrictions = ∅ := by
  obtain ⟨rest,hr,hrows⟩ := fix_signs rows queries
  refine ⟨rest,hr,Finset.card_eq_zero.mp ?_⟩
  rw [length_ok] at hrows
  have bound := trimmed_mono 63 size_ok
  rw [numerical_bound] at bound
  omega

#print axioms kill_sixty_three

end AdversarialSignCompletion
