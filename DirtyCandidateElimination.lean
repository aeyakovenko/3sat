import Std

namespace DirtyCandidateElimination

inductive Reply where
  | clean
  | miss
  | timeout
  deriving DecidableEq, Repr

/-- Truthful fast verdict or an actual cutoff. True denotes a block with a miss. -/
def truthful (dirty : Bool) : Reply → Bool
  | .clean => !dirty
  | .miss => dirty
  | .timeout => true

structure Report where
  actual : Reply
  simulated : Reply
  correction : Bool

def sound (dirty : Bool) (r : Report) : Bool :=
  truthful dirty r.actual && (r.correction || decide (r.actual = r.simulated))

abbrev Match := Report × Report

def obstruction (a b : Bool) (m : Match) : Bool :=
  decide (a ≠ b) &&
    (m.1.correction || m.2.correction || (decide (m.1.actual = .timeout) && decide (m.2.actual = .timeout)))

/-- None rejects. Otherwise false retains the first block, true the second. -/
def choice : Reply → Reply → Option Bool
  | .miss, _ | _, .miss => none
  | .clean, .timeout => some true
  | _, _ => some false

theorem dirty_wins_or_obstruction (a b : Bool) (l r : Report) (side : Bool)
    (hl : sound a l = true) (hr : sound b r = true)
    (h : choice l.simulated r.simulated = some side) :
    (if side then b else a) = (a || b) ∨ obstruction a b (l,r) = true := by
  by_cases hab : a = b
  · subst b
    cases side <;> cases a <;> simp
  · by_cases hc : l.correction || r.correction
    · right
      simp [obstruction, hab, hc]
    · obtain ⟨la, ls, lc⟩ := l
      obtain ⟨ra, rs, rc⟩ := r
      cases lc <;> cases rc <;> simp_all [sound]
      rcases hl with ⟨hl, rfl⟩
      rcases hr with ⟨hr, rfl⟩
      cases a <;> cases b <;> cases la <;> cases ra <;>
        simp_all [truthful, choice, obstruction]

/-- The trace records only comparisons actually tried, up to rejection. -/
def tournament (q : α → α → Match) (current : α) :
    List α → Option α × List (α × α)
  | [] => (some current, [])
  | j :: js =>
    let m := q current j
    match choice m.1.simulated m.2.simulated with
    | none => (none, [(current,j)])
    | some side =>
      let z := tournament q (if side then j else current) js
      (z.1, (current,j) :: z.2)

theorem winner_or_traced_obstruction (dirty : α → Bool) (q : α → α → Match)
    (hq : ∀ i j, sound (dirty i) (q i j).1 = true ∧ sound (dirty j) (q i j).2 = true)
    (current winner : α) (rest : List α)
    (won : (tournament q current rest).1 = some winner) :
    dirty winner = (dirty current || rest.any dirty) ∨
      ∃ p ∈ (tournament q current rest).2, obstruction (dirty p.1) (dirty p.2) (q p.1 p.2) = true := by
  induction rest generalizing current with
  | nil =>
    have eq : current = winner := by simpa [tournament] using won
    simp [eq]
  | cons j js ih =>
    cases hs : choice (q current j).1.simulated (q current j).2.simulated with
    | none => simp [tournament, hs] at won
    | some side =>
      let next := if side then j else current
      have next_won : (tournament q next js).1 = some winner := by
        simpa [tournament, hs, next] using won
      rcases ih next next_won with htail | ⟨p, hp, hb⟩
      · have step := dirty_wins_or_obstruction (dirty current) (dirty j)
          (q current j).1 (q current j).2 side (hq current j).1 (hq current j).2 hs
        rcases step with hlocal | bad
        · left
          have hn : dirty next = (dirty current || dirty j) := by
            cases side <;> simpa [next] using hlocal
          simpa [hn, Bool.or_assoc] using htail
        · right
          exact ⟨(current,j), by simp [tournament, hs], bad⟩
      · right
        exact ⟨p, by simp [tournament, hs, next] at hp ⊢; exact Or.inr hp, hb⟩

/-- A positive raw guard on a non-diagonal query yields a genuine opposite
comparison with a correction or two actual timeouts, even when simulated
reports on homogeneous comparisons were both corrupted. -/
theorem positive_off_diagonal (dirty : α → Bool) (q : α → α → Match)
    (hq : ∀ i j, sound (dirty i) (q i j).1 = true ∧ sound (dirty j) (q i j).2 = true)
    (current winner : α) (rest : List α)
    (won : (tournament q current rest).1 = some winner)
    (raw : dirty winner = false) (offDiag : (dirty current || rest.any dirty) = true) :
    ∃ p ∈ (tournament q current rest).2, obstruction (dirty p.1) (dirty p.2) (q p.1 p.2) = true := by
  rcases winner_or_traced_obstruction dirty q hq current winner rest won with h | h
  · simp [raw, offDiag] at h
  · exact h

#print axioms dirty_wins_or_obstruction
#print axioms positive_off_diagonal

end DirtyCandidateElimination
