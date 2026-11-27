import Std

namespace CrossingLoad

abbrev Pair := Nat × Nat

/-- The cut c follows the bit in position c. Orient each pair left to right. -/
def crosses (c : Nat) (e : Pair) : Bool := decide (e.1 ≤ c ∧ c < e.2)

def load (pairs : List Pair) (c : Nat) : Nat := pairs.countP (crosses c)

def sumCuts (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sumCuts f n + f n

private theorem sum_add (f g : Nat → Nat) (n : Nat) :
    sumCuts (fun c => f c + g c) n = sumCuts f n + sumCuts g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumCuts, ih]; omega

private theorem single_distance (e : Pair) (n : Nat) :
    sumCuts (fun c => if crosses c e then 1 else 0) n = min n e.2 - e.1 := by
  induction n with
  | zero => simp [sumCuts]
  | succ n ih =>
    rw [sumCuts, ih]
    by_cases h : n < e.2
    · rw [Nat.min_eq_left (Nat.le_of_lt h), Nat.min_eq_left (by omega : n+1 ≤ e.2)]
      by_cases l : e.1 ≤ n <;> simp [crosses, l, h] <;> omega
    · rw [Nat.min_eq_right (by omega : e.2 ≤ n), Nat.min_eq_right (by omega : e.2 ≤ n+1)]
      simp [crosses, h]

/-- The partial sum through n cuts also accounts for pairs ending past n. -/
theorem sum_load (pairs : List Pair) (n : Nat) :
    sumCuts (load pairs) n = (pairs.map (fun e => min n e.2 - e.1)).sum := by
  induction pairs with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih => simpa [sumCuts, load] using ih
  | cons e rest ih =>
    have row : load (e :: rest) =
        fun c => load rest c + (if crosses c e then 1 else 0) := by
      funext c
      simp only [load, List.countP_cons]
    rw [row, sum_add, ih, single_distance]
    simp [Nat.add_comm]

theorem total_pair_distance (pairs : List Pair) (n : Nat)
    (bounded : ∀ e ∈ pairs, e.2 ≤ n) :
    sumCuts (load pairs) n = (pairs.map (fun e => e.2 - e.1)).sum := by
  rw [sum_load]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  rw [Nat.min_eq_right (bounded e he)]

def liveValues (pairs : List Pair) (c : Nat) (word : Nat → α) : List α :=
  (pairs.filter (crosses c)).map (fun e => word e.1)

theorem live_length (pairs : List Pair) (c : Nat) (word : Nat → α) :
    (liveValues pairs c word).length = load pairs c := by
  simp [liveValues, load, List.countP_eq_length_filter]

def valid (pairs : List Pair) (word : Nat → α) : Prop :=
  ∀ e ∈ pairs, word e.1 = word e.2

def splice (c : Nat) (left right : Nat → α) (i : Nat) : α :=
  if i ≤ c then left i else right i

/-- For two internally valid words, the live values exactly determine whether
    the left prefix of one can be joined to the right suffix of the other. -/
theorem splice_iff {pairs : List Pair} {left right : Nat → α} (c : Nat)
    (oriented : ∀ e ∈ pairs, e.1 ≤ e.2)
    (left_ok : valid pairs left) (right_ok : valid pairs right) :
    valid pairs (splice c left right) ↔
      liveValues pairs c left = liveValues pairs c right := by
  simp only [liveValues, List.map_inj_left, List.mem_filter, crosses,
    decide_eq_true_eq]
  constructor
  · intro ok e h
    have result := ok e h.1
    simpa [splice, h.2.1, Nat.not_le_of_lt h.2.2, ← right_ok e h.1] using result
  · intro same e he
    have h := oriented e he
    by_cases after : c < e.2
    · by_cases before : e.1 ≤ c
      · simpa [splice, before, Nat.not_le_of_lt after, ← right_ok e he] using
          same e ⟨he, before, after⟩
      · simpa [splice, before, Nat.not_le_of_lt after] using right_ok e he
    · have before : e.1 ≤ c := by omega
      simpa [splice, before, Nat.le_of_not_gt after] using left_ok e he

end CrossingLoad
