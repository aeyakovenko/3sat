import Std

namespace MomentTest

/-- An entry consists of an integer key and a signed multiplicity. -/
abbrev Entry := Int × Int

def weighted (f : Int → Int) : List Entry → Int
  | [] => 0
  | (x,d) :: rest => d * f x + weighted f rest

def polynomial (coeff : List Int) (start : Nat) (x : Int) : Int :=
  match coeff with
  | [] => 0
  | a :: rest => a * x ^ start + polynomial rest (start+1) x

private theorem linear (data : List Entry) (a : Int) (f g : Int → Int) :
    weighted (fun x => a * f x + g x) data =
      a * weighted f data + weighted g data := by
  induction data with
  | nil => simp [weighted]
  | cons e rest ih =>
    rcases e with ⟨x,d⟩
    change d * (a * f x + g x) + weighted (fun y => a * f y + g y) rest =
      a * (d * f x + weighted f rest) + (d * g x + weighted g rest)
    rw [ih, Int.mul_add, Int.mul_add, Int.mul_left_comm d a (f x)]
    omega

private theorem annihilate_from (data : List Entry) (coeff : List Int) (start : Nat)
    (moments : ∀ j, start ≤ j → j < start + coeff.length →
      weighted (fun x => x ^ j) data = 0) :
    weighted (polynomial coeff start) data = 0 := by
  induction coeff generalizing start with
  | nil =>
    induction data with
    | nil => rfl
    | cons e rest ih =>
      rcases e with ⟨x,d⟩
      simpa [weighted, polynomial] using ih (by
        intro j hj upper
        simp only [List.length_nil, Nat.add_zero] at upper
        omega)
  | cons a tail ih =>
    simp only [List.length_cons] at moments
    change weighted (fun x => a * x ^ start + polynomial tail (start+1) x) data = 0
    rw [linear, moments start (by omega) (by omega), ih (start+1) (by
      intro j hj upper
      exact moments j (by omega) (by omega))]
    simp

theorem moments_annihilate (data : List Entry) (k : Nat) (coeff : List Int)
    (degree : coeff.length ≤ k+1)
    (moments : ∀ j, j ≤ k → weighted (fun x => x ^ j) data = 0) :
    weighted (polynomial coeff 0) data = 0 := by
  apply annihilate_from
  intro j _ hj
  exact moments j (by omega)

private theorem weighted_nonneg (data : List Entry) (f : Int → Int)
    (terms : ∀ e ∈ data, 0 ≤ e.2 * f e.1) : 0 ≤ weighted f data := by
  induction data with
  | nil => exact Int.le_refl _
  | cons e rest ih =>
    rcases e with ⟨x,d⟩
    exact Int.add_nonneg (terms (x,d) (by simp))
      (ih (fun e he => terms e (by simp [he])))

private theorem weighted_pos (data : List Entry) (f : Int → Int)
    (terms : ∀ e ∈ data, 0 ≤ e.2 * f e.1)
    (positive : ∃ e ∈ data, 0 < e.2 * f e.1) : 0 < weighted f data := by
  induction data with
  | nil => simp at positive
  | cons e rest ih =>
    rcases e with ⟨x,d⟩
    have tail_ok : ∀ e ∈ rest, 0 ≤ e.2 * f e.1 :=
      fun e he => terms e (by simp [he])
    obtain ⟨hit, whereHit, greater⟩ := positive
    rcases List.mem_cons.mp whereHit with same | inTail
    · subst hit
      exact Int.add_pos_of_pos_of_nonneg greater (weighted_nonneg rest f tail_ok)
    · exact Int.add_pos_of_nonneg_of_pos (terms (x,d) (by simp))
        (ih tail_ok ⟨hit, inTail, greater⟩)

theorem no_positive_polynomial (data : List Entry) (k : Nat) (coeff : List Int)
    (degree : coeff.length ≤ k+1)
    (moments : ∀ j, j ≤ k → weighted (fun x => x ^ j) data = 0)
    (terms : ∀ e ∈ data, 0 ≤ e.2 * polynomial coeff 0 e.1) :
    ¬ ∃ e ∈ data, 0 < e.2 * polynomial coeff 0 e.1 := by
  intro positive
  have strict := weighted_pos data _ terms positive
  rw [moments_annihilate data k coeff degree moments] at strict
  exact Int.lt_irrefl 0 strict

end MomentTest
