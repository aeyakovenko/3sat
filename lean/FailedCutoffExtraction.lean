import Std

namespace FailedCutoffExtraction

/-- On a nested sequence of witness sets, one existential query is true up
    through its last YES index. An always-NO query may simply be omitted. -/
def rank (thresholds : List Nat) (i : Nat) : Nat :=
  (thresholds.filter (fun t => decide (i ≤ t))).length

private theorem rank_mono (ts : List Nat) {i j : Nat} (h : i ≤ j) :
    rank ts j ≤ rank ts i := by
  induction ts with
  | nil => simp [rank]
  | cons a ts ih =>
    by_cases hi : i ≤ a <;> by_cases hj : j ≤ a
    · simpa [rank, hi, hj] using ih
    · simp [rank, hi, hj] at *
      omega
    · omega
    · simpa [rank, hi, hj] using ih

private theorem rank_strict (ts : List Nat) {i j : Nat} (h : i ≤ j)
    (cross : ∃ t ∈ ts, i ≤ t ∧ t < j) : rank ts j < rank ts i := by
  induction ts with
  | nil => simp at cross
  | cons a ts ih =>
    by_cases both : j ≤ a
    · have hi := Nat.le_trans h both
      have tail : ∃ t ∈ ts, i ≤ t ∧ t < j := by
        obtain ⟨t, mem, hti, htj⟩ := cross
        rcases List.mem_cons.mp mem with eq | rest
        · omega
        · exact ⟨t,rest,hti,htj⟩
      simpa [rank,hi,both] using ih tail
    · by_cases hi : i ≤ a
      · have weak := rank_mono ts h
        simp [rank,hi,both] at *
        omega
      · have tail : ∃ t ∈ ts, i ≤ t ∧ t < j := by
          obtain ⟨t,mem, hti, htj⟩ := cross
          rcases List.mem_cons.mp mem with eq | rest
          · omega
          · exact ⟨t,rest,hti,htj⟩
        simpa [rank,hi,both] using ih tail

/-- Distinguishing n adjacent changes along a nested witness chain in one
    parallel batch needs at least n existential questions. -/
theorem parallel_questions (ts : List Nat) (n : Nat)
    (changes : ∀ i < n, ∃ t ∈ ts, i ≤ t ∧ t < i+1) : n ≤ ts.length := by
  have remaining (m : Nat) (hm : m ≤ n) : m + rank ts m ≤ rank ts 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
      have prev := ih (by omega)
      have dec := rank_strict ts (Nat.le_succ m) (changes m (by omega))
      change m + 1 + rank ts (m + 1) ≤ rank ts 0
      change rank ts (m + 1) < rank ts m at dec
      omega
  have endRank := remaining n (Nat.le_refl n)
  have full : rank ts 0 = ts.length := by simp [rank]
  omega

/-- A queried point other than the two listed below gives the same answer in
    the planted-only world and a world with one extra candidate. -/
theorem untested_point {X : Type} (w x : X) (asked : List X)
    (unseen : x ∉ asked) :
    ∀ a ∈ asked, (a = w ∨ a = x) ↔ a = w := by
  intro a mem
  constructor
  · rintro (same | same)
    · exact same
    · exact False.elim (unseen (same ▸ mem))
  · exact Or.inl

/-- The lower witness of an extra/planted pair is exactly the extra
    point when it lies below the plant, so a cutoff pair changes labels
    precisely when its half-open interval contains that point. -/
theorem two_point_cutoffs (x w a b : Nat) (h : x ≤ w) :
    (¬ (∃ y, (y=x ∨ y=w) ∧ y ≤ a)) ∧ (∃ y, (y=x ∨ y=w) ∧ y ≤ b)
      ↔ a < x ∧ x ≤ b := by
  have atCut (t : Nat) : (∃ y, (y=x ∨ y=w) ∧ y ≤ t) ↔ x ≤ t := by
    constructor
    · rintro ⟨y, eq | eq, le⟩ <;> omega
    · intro le
      exact ⟨x,Or.inl rfl,le⟩
  rw [atCut a, atCut b]
  omega

end FailedCutoffExtraction
