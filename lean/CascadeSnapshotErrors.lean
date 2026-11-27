import Std

namespace CascadeSnapshotErrors

abbrev Test (Key : Type) := Key → Bool

/-- A positive filter reply asks whether the next filter can correct it. -/
def lookup (filters : List (Test Key)) (key : Key) : Bool :=
  match filters with
  | [] => false
  | first :: rest => first key && !(lookup rest key)

/-- Each level covers its positives. Its false positives become the
positives at the next level, which must distinguish them from the old positives. -/
inductive Fits {Key : Type} : List (Test Key) → (Key → Prop) → (Key → Prop) → Prop where
  | stop {pos neg} (empty : ∀ k, ¬ pos k) : Fits [] pos neg
  | level {first rest pos neg}
      (cover : ∀ k, pos k → first k = true)
      (next : Fits rest (fun k => neg k ∧ first k = true) pos) :
      Fits (first :: rest) pos neg

theorem exactOnDomain {filters : List (Test Key)} {pos neg : Key → Prop}
    (valid : Fits filters pos neg) :
    (∀ k, pos k → lookup filters k = true) ∧ (∀ k, neg k → lookup filters k = false) := by
  induction valid with
  | stop empty =>
    exact ⟨fun k hk => False.elim (empty k hk), fun _ _ => rfl⟩
  | @level first rest pos neg cover next ih =>
    constructor
    · intro k hp
      simp [lookup, cover k hp, ih.2 k hp]
    · intro k hn
      cases h : first k with
      | false => simp [lookup, h]
      | true => simp [lookup, h, ih.1 k ⟨hn, h⟩]

/-- The cardinality of the next positive set is at most half the current one. -/
inductive Shrinks : Nat → List Nat → Prop where
  | stop (a : Nat) : Shrinks a []
  | step {a b rest} (half : 2 * b ≤ a) (tail : Shrinks b rest) :
      Shrinks a (b :: rest)

theorem tailMass {a : Nat} {sizes : List Nat} (h : Shrinks a sizes) :
    sizes.sum ≤ a := by
  induction h with
  | stop => simp
  | step half _ ih =>
    simp only [List.sum_cons]
    omega

/-- Every residual class except a largest one has frequency at most half
the total. For such a class, taking logarithms of this integer inequality
shows that its contribution to the empirical entropy sum is at least log M. -/
theorem smallClassPower (M j : Nat) (half : 2 * (j + 1) ≤ M) :
    (j + 1) ^ (j + 1) ≤ M ^ j := by
  have linear : ∀ n : Nat, n + 1 ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => decide
    | succ n ih => rw [Nat.pow_succ]; omega
  calc
    (j + 1) ^ (j + 1) = (j + 1) ^ j * (j + 1) := Nat.pow_succ _ _
    _ ≤ (j + 1) ^ j * 2 ^ j := Nat.mul_le_mul_left _ (linear j)
    _ = (2 * (j + 1)) ^ j := by rw [Nat.mul_pow, Nat.mul_comm (2 ^ j)]
    _ ≤ M ^ j := Nat.pow_le_pow_left half j

theorem correctByException {baseline target : Key → Bool} {domain : Key → Prop}
    {filters : List (Test Key)}
    (valid : Fits filters (fun k => domain k ∧ baseline k ≠ target k)
                          (fun k => domain k ∧ baseline k = target k))
    (k : Key) (hk : domain k) :
    (if lookup filters k then !(baseline k) else baseline k) = target k := by
  by_cases h : baseline k = target k
  · simp [h, (exactOnDomain valid).2 k ⟨hk, h⟩]
  · rw [(exactOnDomain valid).1 k ⟨hk, h⟩]
    cases hb : baseline k <;> cases ht : target k <;> simp_all

end CascadeSnapshotErrors
