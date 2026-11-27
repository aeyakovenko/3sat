import Std

namespace TraceMultiplicityCover

theorem fairTapeResidue (r : Nat) : 2^r % 3 = 1 ∨ 2^r % 3 = 2 := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> decide

private theorem zeroMass (masses : List Nat) (allZero : ∀ a ∈ masses, a % 3 = 0) :
    masses.sum % 3 = 0 := by
  induction masses with
  | nil => rfl
  | cons a t ih =>
    have ha := allZero a (by simp)
    have ht := ih (fun b hb => allZero b (by simp [hb]))
    rw [List.sum_cons, Nat.add_mod, ha, ht]

/-- One fiber of any partition of a fixed-length fair tape is a unit in F₃. -/
theorem unitFiber {r : Nat} (masses : List Nat) (partition : masses.sum = 2^r) :
    ∃ a ∈ masses, a % 3 ≠ 0 := by
  apply Classical.byContradiction
  intro h
  have hz : ∀ a ∈ masses, a % 3 = 0 := by
    intro a ha
    apply Classical.byContradiction
    exact fun hn => h ⟨a,ha,hn⟩
  have hsum := zeroMass masses hz
  rw [partition] at hsum
  rcases fairTapeResidue r with hr | hr <;> omega

/-- Both units in F₃ are their own inverses. -/
theorem normalizeUnit (a : Nat) (ha : a % 3 ≠ 0) : a*a % 3 = 1 := by
  have hlt := Nat.mod_lt a (by decide : 0 < 3)
  have h : a % 3 = 1 ∨ a % 3 = 2 := by omega
  rw [Nat.mul_mod]
  rcases h with h | h <;> rw [h] <;> decide

/-- A sum of weighted accepting fiber counts, evaluated on a perfectly correct
    machine. Each pair contains a coefficient and a multiplicity at this input. -/
def mass (columns : List (Nat × Nat)) : Nat :=
  (columns.map (fun z => z.1 * z.2)).sum

def accepting (yes : Bool) : List (Nat × Nat) → List (Nat × Nat) :=
  List.map (fun z => (z.1, if yes then z.2 else 0))

theorem recover (yes : Bool) (columns : List (Nat × Nat))
    (onYes : yes = true → mass columns % 3 = 1) :
    mass (accepting yes columns) % 3 = (if yes then 1 else 0) := by
  cases yes with
  | true =>
    simpa [mass, accepting, List.map_map, Function.comp_def] using onYes rfl
  | false =>
    induction columns with
    | nil => rfl
    | cons z zs ih =>
      simpa [mass, accepting, List.map_map, Function.comp_def] using ih

/-- The rare-exception channel with 4^k fair tapes has a common fiber of
    size 4^k−1. Its mass vanishes even when its probability tends to one. -/
theorem powerFourResidue (k : Nat) : 4^k % 3 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem commonVanishes (k : Nat) : (4^k-1) % 3 = 0 := by
  have h := powerFourResidue k
  omega

theorem residueSquare (a : Nat) : a*a % 3 = (if a % 3 = 0 then 0 else 1) := by
  by_cases h : a % 3 = 0
  · rw [if_pos h, Nat.mul_mod, h]
  · rw [if_neg h]
    exact normalizeUnit a h

end TraceMultiplicityCover
