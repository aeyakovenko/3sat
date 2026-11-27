import Std

namespace TranslatedTapeCrossings

/-- Sum over all scalar grid residues. -/
def total (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => total f n + f n

def tally (r : Nat) : List Nat → Nat
  | [] => 0
  | a :: rest => (if r = a then 1 else 0) + tally r rest

theorem total_add (f g : Nat → Nat) (n : Nat) :
    total (fun i => f i + g i) n = total f n + total g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total, ih]; omega

theorem total_delta (a n : Nat) :
    total (fun i => if i = a then 1 else 0) n = if a < n then 1 else 0 := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    simp only [total, ih]
    split <;> split <;> split <;> omega

theorem total_zero (n : Nat) : total (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [total, ih]

/-- A unit move contributes once among the shifts; a stationary step was omitted from `moves`. -/
theorem all_crossings (B : Nat) (moves : List Nat) (valid : ∀ a ∈ moves, a < B) :
    total (fun r => tally r moves) B = moves.length := by
  induction moves with
  | nil => exact total_zero B
  | cons a rest ih =>
    simp only [tally, List.length_cons]
    rw [total_add, total_delta, if_pos (valid a (by simp)),
      ih (fun x hx => valid x (by simp [hx]))]
    omega

theorem lower_total (f : Nat → Nat) (c n : Nat) (bound : ∀ i < n, c ≤ f i) :
    c * n ≤ total f n := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    simpa [total, Nat.mul_succ] using
      Nat.add_le_add (ih (fun i hi => bound i (by omega))) (bound n (by omega))

/-- One common scalar shift, across every possible axis and tape, has few crossings. -/
theorem exists_sparse_shift (B : Nat) (positive : 0 < B) (moves : List Nat)
    (valid : ∀ a ∈ moves, a < B) : ∃ r < B, tally r moves ≤ moves.length / B := by
  apply Classical.byContradiction
  intro none
  have lower (r : Nat) (hr : r < B) : moves.length / B + 1 ≤ tally r moves := by
    have hn : ¬ tally r moves ≤ moves.length / B := fun h => none ⟨r, hr, h⟩
    omega
  have h := lower_total _ _ _ lower
  rw [all_crossings B moves valid] at h
  have impossible := (Nat.div_lt_iff_lt_mul positive).mp (Nat.lt_succ_self (moves.length / B))
  exact Nat.not_lt_of_ge h impossible

end TranslatedTapeCrossings
