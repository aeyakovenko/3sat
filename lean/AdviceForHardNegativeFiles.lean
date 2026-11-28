import Std

namespace AdviceForHardNegativeFiles

/-- A deterministic solver run up to the negative deadline, returning SAT on timeout. -/
def defaultYes (answer : Bool) (actual budget : Nat) : Bool :=
  if actual ≤ budget then answer else true

theorem correct_cutoff {File : Type} (answer : File → Bool) (time budget : File → Nat)
    (negFast : ∀ x, answer x = false → time x ≤ budget x) (x : File) :
    defaultYes (answer x) (time x) (budget x) = answer x := by
  cases h : answer x with
  | false => simp [defaultYes, negFast x h]
  | true => simp [defaultYes]

/-- Bounded encoded lengths contain finitely many files. The corresponding bound on
running times is supplied by `shortBound`, independently of the constructor. -/
theorem hard_negatives {File : Type} (size time : File → Nat) (negative : File → Prop)
    (k : Nat) (shortBound : ∀ n, ∃ b, ∀ x, size x < n → time x ≤ b)
    (unbounded : ¬ ∃ c, ∀ x, negative x → time x ≤ c*(size x+1)^k) :
    ∃ files : Nat → File, ∀ j, negative (files j) ∧ j ≤ size (files j) ∧
      j*(size (files j)+1)^k < time (files j) := by
  classical
  have each (j : Nat) : ∃ x, negative x ∧ j ≤ size x ∧ j*(size x+1)^k < time x := by
    obtain ⟨b, hb⟩ := shortBound j
    let c := j+b+1
    have witness : ∃ x, negative x ∧ c*(size x+1)^k < time x := by
      apply Classical.byContradiction
      intro noWitness
      apply unbounded
      refine ⟨c, fun x hx => ?_⟩
      apply Classical.byContradiction
      intro late
      exact noWitness ⟨x, hx, by omega⟩
    obtain ⟨x, hx, late⟩ := witness
    have positive : 0 < (size x+1)^k := Nat.pow_pos (Nat.succ_pos _)
    have c_le_time : c < time x := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ positive) late
    refine ⟨x,hx,?_,?_⟩
    · apply Classical.byContradiction
      intro tooShort
      have := hb x (by omega)
      dsimp [c] at c_le_time
      omega
    · exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by dsimp [c]; omega)) late
  exact ⟨fun j => Classical.choose (each j), fun j => Classical.choose_spec (each j)⟩

/-- One hard sequence is selected before any constructor. The proof keeps its growing
multiplier when converting the pointwise, truncated simulation bound into an advice bound.
`accepts g x a h` means a successful h-bit suggestion within constructor g's a-th-power clock. -/
theorem simultaneous_advice {File Constructor : Type} (size time : File → Nat)
    (negative : File → Prop) (accepts : Constructor → File → Nat → Nat → Prop)
    (k : Nat) (hk : k ≤ 3)
    (shortBound : ∀ n, ∃ b, ∀ x, size x < n → time x ≤ b)
    (unbounded : ¬ ∃ c, ∀ x, negative x → time x ≤ c*(size x+1)^k)
    (simulation : ∀ g a, 1 ≤ a → a ≤ 3 → ∃ c, ∀ x h, accepts g x a h →
      min (time x) ((size x+1)^4) ≤ c * 2^h * (size x+1)^a) :
    ∃ files : Nat → File,
      (∀ j, negative (files j) ∧ j ≤ size (files j) ∧ j*(size (files j)+1)^k < time (files j)) ∧
      (∀ g a, 1 ≤ a → a ≤ 3 → ∃ c, ∀ j h, accepts g (files j) a h →
        j*(size (files j)+1)^k ≤ c * 2^h * (size (files j)+1)^a) := by
  obtain ⟨files,hard⟩ := hard_negatives size time negative k shortBound unbounded
  refine ⟨files, hard, ?_⟩
  intro g a ha hb
  obtain ⟨c,sim⟩ := simulation g a ha hb
  refine ⟨c, ?_⟩
  intro j h good
  obtain ⟨_,large,late⟩ := hard j
  let m := size (files j)+1
  have cap : j*m^k ≤ m^4 := calc
    j*m^k ≤ m*m^k := Nat.mul_le_mul_right _ (by dsimp [m]; omega)
    _ = m^(k+1) := by rw [Nat.pow_succ, Nat.mul_comm]
    _ ≤ m^4 := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  exact Nat.le_trans (Nat.le_min.mpr ⟨Nat.le_of_lt late,cap⟩) (sim (files j) h good)

end AdviceForHardNegativeFiles
