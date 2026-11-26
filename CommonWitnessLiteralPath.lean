import Std

namespace CommonWitnessLiteralPath

/-- Put the distinguished position first and keep all other positions in natural order. -/
def rank {k : Nat} (first i : Fin k) : Nat :=
  if i.val = first.val then 0 else if i.val < first.val then i.val + 1 else i.val

theorem rank_lt {k : Nat} (first i : Fin k) : rank first i < k := by
  have hi := i.isLt
  have hf := first.isLt
  unfold rank
  split <;> first | omega | (split <;> omega)

theorem rank_injective {k : Nat} (first i j : Fin k)
    (h : rank first i = rank first j) : i = j := by
  apply Fin.ext
  unfold rank at h
  repeat' split at h
  all_goals omega

/-- After t replacements use the new literal in precisely the first t positions of the order. -/
def hybrid {k : Nat} {α : Type} (old fresh : Fin k → α) (first : Fin k) (t : Nat) :
    Fin k → α := fun i => if rank first i < t then fresh i else old i

theorem hybrid_start {k : Nat} {α : Type} (old fresh : Fin k → α) (first : Fin k) :
    hybrid old fresh first 0 = old := by
  funext i
  simp [hybrid]

theorem hybrid_finish {k : Nat} {α : Type} (old fresh : Fin k → α) (first : Fin k) :
    hybrid old fresh first k = fresh := by
  funext i
  simp [hybrid, rank_lt]

theorem changed_position {k : Nat} {α : Type} (old fresh : Fin k → α)
    (first i : Fin k) (t : Nat)
    (h : hybrid old fresh first t i ≠ hybrid old fresh first (t+1) i) :
    rank first i = t := by
  unfold hybrid at h
  split at h <;> split at h <;> first | exact False.elim (h rfl) | omega

def accepts {k : Nat} {α : Type} (holds : α → Prop) (row : Fin k → α) : Prop :=
  ∃ i, holds (row i)

/-- A model of both endpoint clauses remains a model along a k-step single-position path. -/
theorem common_witness_path {k : Nat} {α : Type} (old fresh : Fin k → α)
    (holds : α → Prop) (ho : accepts holds old) (hn : accepts holds fresh) :
    ∃ first : Fin k,
      hybrid old fresh first 0 = old ∧ hybrid old fresh first k = fresh ∧
      (∀ t, accepts holds (hybrid old fresh first t)) ∧
      (∀ t i j,
        hybrid old fresh first t i ≠ hybrid old fresh first (t+1) i →
        hybrid old fresh first t j ≠ hybrid old fresh first (t+1) j → i = j) := by
  obtain ⟨first, hf⟩ := hn
  refine ⟨first, hybrid_start _ _ _, hybrid_finish _ _ _, ?_, ?_⟩
  · intro t
    cases t with
    | zero => simpa [hybrid_start] using ho
    | succ t => exact ⟨first, by simpa [hybrid, rank] using hf⟩
  · intro t i j hi hj
    apply rank_injective first
    exact (changed_position _ _ _ _ _ hi).trans (changed_position _ _ _ _ _ hj).symm

/-- Hamming distance on a specified list of output coordinates. -/
def hamming {ι : Type} (x y : ι → Bool) : List ι → Nat
  | [] => 0
  | i :: rest => (if x i = y i then 0 else 1) + hamming x y rest

theorem hamming_triangle {ι : Type} (x y z : ι → Bool) (coords : List ι) :
    hamming x z coords ≤ hamming x y coords + hamming y z coords := by
  induction coords with
  | nil => simp [hamming]
  | cons i rest ih =>
    simp only [hamming]
    by_cases h : x i = y i
    · simp [h]
      split <;> omega
    · by_cases g : y i = z i
      · simp [h, ← g]
        omega
      · simp [h, g]
        split <;> omega

theorem hamming_self {ι : Type} (x : ι → Bool) (coords : List ι) :
    hamming x x coords = 0 := by
  induction coords <;> simp_all [hamming]

/-- The cumulative upper bound when every one of t adjacent outputs changes at most d bits. -/
theorem chain_bound {ι : Type} (rows : Nat → ι → Bool) (coords : List ι)
    (t d : Nat) (h : ∀ s, s < t → hamming (rows s) (rows (s+1)) coords ≤ d) :
    hamming (rows 0) (rows t) coords ≤ t*d := by
  induction t with
  | zero => simp [hamming_self]
  | succ t ih =>
    have a := ih (fun s hs => h s (by omega))
    have b := h t (by omega)
    have c := hamming_triangle (rows 0) (rows t) (rows (t+1)) coords
    rw [Nat.succ_mul]
    omega

/-- A large endpoint distance forces a large single-position jump through common-model clauses. -/
theorem common_witness_selector_jump {k n : Nat} {α : Type} (old fresh : Fin k → α)
    (holds : α → Prop) (ho : accepts holds old) (hn : accepts holds fresh)
    (select : (Fin k → α) → Fin n → Bool) (d : Nat)
    (far : k*d < hamming (select old) (select fresh) (List.finRange n)) :
    ∃ (first : Fin k) (t : Nat), t < k ∧
      (∀ s, accepts holds (hybrid old fresh first s)) ∧
      (∀ i j, hybrid old fresh first t i ≠ hybrid old fresh first (t+1) i →
        hybrid old fresh first t j ≠ hybrid old fresh first (t+1) j → i = j) ∧
      d < hamming (select (hybrid old fresh first t))
            (select (hybrid old fresh first (t+1))) (List.finRange n) := by
  obtain ⟨first, hs, he, valid, single⟩ := common_witness_path old fresh holds ho hn
  let rows := fun s => select (hybrid old fresh first s)
  have someJump : ∃ t, t < k ∧ d < hamming (rows t) (rows (t+1)) (List.finRange n) := by
    apply Classical.byContradiction
    intro h
    have small : ∀ s, s < k → hamming (rows s) (rows (s+1)) (List.finRange n) ≤ d := by
      intro s hsk
      apply Nat.le_of_not_lt
      exact fun large => h ⟨s, hsk, large⟩
    have bound := chain_bound rows (List.finRange n) k d small
    change hamming (select (hybrid old fresh first 0))
      (select (hybrid old fresh first k)) (List.finRange n) ≤ k*d at bound
    rw [hs, he] at bound
    omega
  obtain ⟨t, ht, large⟩ := someJump
  exact ⟨first, t, ht, valid, single t, large⟩

#print axioms common_witness_path
#print axioms common_witness_selector_jump

end CommonWitnessLiteralPath
