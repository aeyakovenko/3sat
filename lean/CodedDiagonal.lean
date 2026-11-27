import Std

namespace CodedDiagonal

/-- Signed character evaluations on all masks. Adjoining a mask bit
    contributes a second copy, negated when its coefficient is one. -/
def characterValues : List Bool → List Int
  | [] => [1]
  | a :: rest =>
    let vals := characterValues rest
    vals ++ (if a then vals.map (fun z => -z) else vals)

private theorem neg_sum (l : List Int) :
    (l.map (fun z => -z)).sum = -l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Int.neg_add]

private theorem joined_sum (l r : List Int) :
    (l ++ r).sum = l.sum + r.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Int.add_assoc]

theorem character_sum (a : List Bool) :
    (characterValues a).sum = if true ∈ a then 0 else (2 : Int) ^ a.length := by
  induction a with
  | nil => simp [characterValues]
  | cons b tail ih =>
    cases b
    · by_cases nz : true ∈ tail
      · simp [characterValues, joined_sum, ih, nz]
      · simp [characterValues, joined_sum, ih, nz, Int.pow_succ]; omega
    · simp [characterValues, joined_sum, neg_sum]
      omega

/-- If p purports to list all strongly predicted blocks, a generated
    truth table taking an omitted pattern on its block is outside p. -/
theorem omit_block {T B : Type} (block : T → B) (listed : T → Prop)
    {source : T} {w : B} (omitted : ∀ y, listed y → block y ≠ w)
    (written : block source = w) : ¬ listed source := by
  intro inside
  exact omitted source inside written

/-- Over the binary field, a direction annihilating the old equations
    and flipping the next bit permits either demanded new value. -/
def add (x y : ι → Bool) : ι → Bool := fun i => x i ^^ y i

def Linear (f : (ι → Bool) → Bool) : Prop :=
  ∀ x y, f (add x y) = (f x ^^ f y)

theorem fresh_claim {old : σ → (ι → Bool) → Bool} {rhs : σ → Bool}
    {claim : (ι → Bool) → Bool} (oldLin : ∀ i, Linear (old i)) (lin : Linear claim)
    {x direction : ι → Bool} (consistent : ∀ i, old i x = rhs i)
    (preserve : ∀ i, old i direction = false) (flip : claim direction = true)
    (want : Bool) : ∃ y, (∀ i, old i y = rhs i) ∧ claim y = want := by
  by_cases same : claim x = want
  · exact ⟨x, consistent, same⟩
  · refine ⟨add x direction, ?_, ?_⟩
    · intro i
      rw [oldLin i x direction, preserve i, consistent i]
      simp
    · rw [lin x direction, flip]
      cases val : claim x <;> cases want <;> simp_all

/-- From the cleared Gram inequality and the strict integer gap:
    G² L ≤ M Q + (M t 2ᵇ)(L−1) implies L ≤ M Q. -/
theorem integer_list_bound (scoreSq threshold budget count : Nat)
    (gap : threshold < scoreSq)
    (gram : count * scoreSq ≤ budget + (count - 1) * threshold) :
    count ≤ budget := by
  have low : count * (threshold + 1) ≤ count * scoreSq :=
    Nat.mul_le_mul_left _ gap
  have monotone : (count - 1) * threshold ≤ count * threshold :=
    Nat.mul_le_mul_right _ (Nat.sub_le count 1)
  rw [Nat.mul_add, Nat.mul_one] at low
  omega

end CodedDiagonal
