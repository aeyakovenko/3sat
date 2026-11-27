import Std

namespace AdvisedClaims

/-- Sum of a signed observable over the Cartesian product of three seed lists. -/
def tripleSum (a b c : List Int) : Int :=
  (a.map fun x => (b.map fun y => (c.map fun z => x * y * z).sum).sum).sum

private theorem sum_with_coefficient (q : Int) (s : List Int) :
    (s.map fun x => q * x).sum = q * s.sum := by
  induction s with
  | nil => simp
  | cons a l ih => simp [ih, Int.mul_add]

/-- Exact, unnormalised multiplication of a Fourier coefficient for three
    independent impulses. Dividing by the three seed-space sizes gives bias. -/
theorem triple_character (a b c : List Int) :
    tripleSum a b c = (a.sum * b.sum) * c.sum := by
  have onB (x : Int) :
      (b.map fun y => (c.map fun z => x * y * z).sum).sum =
        (b.sum * c.sum) * x := by
    calc
      _ = (b.map fun y => (c.sum * x) * y).sum := by
        congr 1
        apply List.map_congr_left
        intro y _
        rw [sum_with_coefficient, Int.mul_comm (x * y), Int.mul_assoc]
      _ = _ := by rw [sum_with_coefficient]; ac_rfl
  unfold tripleSum
  simp only [onB]
  rw [sum_with_coefficient, Int.mul_comm (b.sum * c.sum) a.sum, Int.mul_assoc]

def marked (p a b c : α) [DecidableEq α] : Bool :=
  decide (p = a) ^^ decide (p = b) ^^ decide (p = c)

/-- An XOR table formed from three unit vectors has exactly the singleton
    or the three distinct marked positions displayed by this disjunction. -/
theorem one_or_three (a b c : α) [DecidableEq α] :
    (∃ d, ∀ p, marked p a b c = true ↔ p = d) ∨
    (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∀ p, marked p a b c = true ↔ p = a ∨ p = b ∨ p = c) := by
  by_cases ab : a = b
  · subst b
    left
    exact ⟨c, fun p => by by_cases h : p = a <;> simp [marked, h]⟩
  by_cases ac : a = c
  · subst c
    left
    exact ⟨b, fun p => by
      by_cases h : p = a <;> by_cases k : p = b <;> simp [marked, h, k]⟩
  by_cases bc : b = c
  · subst c
    left
    exact ⟨a, fun p => by
      by_cases h : p = a <;> by_cases k : p = b <;> simp [marked, h, k]⟩
  right
  refine ⟨ab, ac, bc, fun p => ?_⟩
  by_cases pa : p = a
  · subst p; simp [marked, ab, ac]
  by_cases pb : p = b
  · subst p; simp [marked, pa, bc]
  by_cases pc : p = c
  · subst p; simp [marked, pa, pb]
  · simp [marked, pa, pb, pc]

/-- Advice selecting a bucket containing the actual source transfers any
    certified value common to the whole bucket to that source. -/
theorem common_bucket_label {T Q : Type} (answer : T → Q → Bool)
    (bucket : T → Prop) {actual : T} (inBucket : bucket actual)
    {q : Q} {label : Bool} (constant : ∀ t, bucket t → answer t q = label) :
    answer actual q = label := constant actual inBucket

end AdvisedClaims
