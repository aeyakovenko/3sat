import Std

namespace LeastWitnessBatch

/-- An exclusive cutoff of b asks the same question as the inclusive cutoff b-1
    when b is positive. -/
def Below (witness : Nat → Prop) (b : Nat) : Prop :=
  ∃ x, witness x ∧ x < b

/-- With one constant observer the search visits the all-zero prefix.
    Its two cutoff groups at this level have exclusive bounds 2^k and 2^(k+1). -/
def Mixed (witness : Nat → Prop) (k : Nat) : Prop :=
  ¬ Below witness (2^k) ∧ Below witness (2^(k+1))

theorem below_iff {witness : Nat → Prop} {mu : Nat} (model : witness mu)
    (least : ∀ x, witness x → mu ≤ x) (b : Nat) :
    Below witness b ↔ mu < b := by
  constructor
  · rintro ⟨x, wx, bound⟩
    exact Nat.lt_of_le_of_lt (least x wx) bound
  · exact fun h => ⟨mu, model, h⟩

theorem mixed_iff_log {witness : Nat → Prop} {mu : Nat} (model : witness mu)
    (least : ∀ x, witness x → mu ≤ x) (positive : mu ≠ 0) (k : Nat) :
    Mixed witness k ↔ k = mu.log2 := by
  simp only [Mixed, below_iff model least, Nat.not_lt, ← Nat.le_log2 positive,
    ← Nat.log2_lt positive]
  omega

/-- In a v-bit search failing on a positive source there is a unique
    mixed level and it is inside the actually visited depth range. -/
theorem unique_mixed {witness : Nat → Prop} {mu v : Nat} (model : witness mu)
    (least : ∀ x, witness x → mu ≤ x) (positive : mu ≠ 0) (fits : mu < 2^v) :
    ∃ k, k < v ∧ Mixed witness k ∧ ∀ t, Mixed witness t → t = k := by
  exact ⟨mu.log2, (Nat.log2_lt positive).2 fits,
    (mixed_iff_log model least positive _).2 rfl,
    fun t => (mixed_iff_log model least positive t).1⟩

/-- Encode an answer string with the first answer in its most significant bit. -/
def rank : List Bool → Nat
  | [] => 0
  | bit :: tail => (if bit then 2^tail.length else 0) + rank tail

theorem rank_bound (xs : List Bool) : rank xs < 2^xs.length := by
  induction xs with
  | nil => decide
  | cons b tail ih =>
    cases b <;> simp only [rank, List.length_cons, Nat.pow_succ, Bool.false_eq_true,
      ↓reduceIte, Nat.zero_add] <;> omega

section AdaptiveQueries

variable {State : Type} (yes : State → Prop) [DecidablePred yes]
    (step : State → Bool → State)

/-- A reported YES needs a witness for that query. A reported NO may
    always be guessed. Both guesses change the next query state. -/
def Feasible (s : State) : List Bool → Prop
  | [] => True
  | b :: tail => (b = true → yes s) ∧ Feasible (step s b) tail

def actual : Nat → State → List Bool
  | 0, _ => []
  | n+1, s =>
    let b := decide (yes s)
    b :: actual n (step s b)

@[simp] theorem actual_length (n : Nat) (s : State) :
    (actual yes step n s).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [actual, ih]

theorem actual_feasible (n : Nat) (s : State) :
    Feasible yes step s (actual yes step n s) := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    simp [actual, Feasible, ih]

/-- If a feasible string is different from the actual adaptive answers, its
    binary rank is strictly smaller. The transition function may depend on
    the complete query history. -/
theorem greatest_feasible (n : Nat) (s : State) (answers : List Bool)
    (len : answers.length = n) (ok : Feasible yes step s answers) :
    answers = actual yes step n s ∨ rank answers < rank (actual yes step n s) := by
  induction n generalizing s answers with
  | zero =>
    have empty := List.length_eq_zero_iff.mp len
    subst answers
    exact Or.inl rfl
  | succ n ih =>
    cases answers with
    | nil => simp at len
    | cons b tail =>
      have tl : tail.length = n := Nat.succ.inj len
      have oks := (show (b = true → yes s) ∧ Feasible yes step (step s b) tail from ok)
      by_cases h : yes s
      · cases b with
        | false =>
          right
          simpa [actual, h, rank, tl] using
            (show rank tail < 2^n + rank (actual yes step n (step s true)) by
              have small := rank_bound tail
              rw [tl] at small
              omega)
        | true =>
          rcases ih (step s true) tail tl oks.2 with eq | lt
          · left
            simp [actual, h, eq]
          · right
            simpa [actual, h, rank, tl] using lt
      · cases b with
        | false =>
          rcases ih (step s false) tail tl oks.2 with eq | lt
          · left
            simp [actual, h, eq]
          · right
            simpa [actual, h, rank] using lt
        | true => exact False.elim (h (oks.1 rfl))

end AdaptiveQueries
end LeastWitnessBatch
