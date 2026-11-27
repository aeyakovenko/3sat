import Std

namespace AnchoredLiteralCensus

/-- Symbols are pairs of visible bits, read from least to most significant. -/
inductive Pair where
  | zero | one | stop | invalid
deriving DecidableEq

def decode : List Pair → Option (List Bool)
  | [] => none
  | .zero :: xs => (decode xs).map (false :: ·)
  | .one :: xs => (decode xs).map (true :: ·)
  | .stop :: _ => some []
  | .invalid :: _ => none

/-- A completed description ignores all more significant pairs. -/
theorem decode_append {xs : List Pair} {bits : List Bool} (h : decode xs = some bits)
    (ys : List Pair) : decode (xs ++ ys) = some bits := by
  induction xs generalizing bits with
  | nil => simp [decode] at h
  | cons z xs ih =>
    cases z with
    | invalid => simp [decode] at h
    | stop => simpa [decode] using h
    | zero =>
      cases hd : decode xs with
      | none => simp [decode, hd] at h
      | some l =>
        simp only [List.cons_append, decode, ih hd]
        simpa [decode, hd] using h
    | one =>
      cases hd : decode xs with
      | none => simp [decode, hd] at h
      | some l =>
        simp only [List.cons_append, decode, ih hd]
        simpa [decode, hd] using h

private theorem finite_witnesses {ι X : Type} (pass : ι → X → Prop) (is : List ι)
    (bad : ∀ i ∈ is, ∃ x, ¬pass i x) :
    ∃ ws : List X, ws.length ≤ is.length ∧ ∀ i ∈ is, ∃ x ∈ ws, ¬pass i x := by
  induction is with
  | nil => exact ⟨[], by simp⟩
  | cons i is ih =>
    obtain ⟨w, hw⟩ := bad i (by simp)
    obtain ⟨ws, len, catches⟩ := ih (fun j hj => bad j (by simp [hj]))
    refine ⟨w :: ws, by simpa using len, ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with eq | tail
    · subst j
      exact ⟨w, by simp, hw⟩
    · obtain ⟨x, hx, fails⟩ := catches j tail
      exact ⟨x, by simp [hx], fails⟩

/-- A single test reduces arbitrary parameters to finitely many representatives.
    One further witness per representative suffices to test the entire family. -/
theorem suite_iff {ι X : Type} (pass : ι → X → Prop) (anchor : X) (reps : List ι)
    (covered : ∀ i, pass i anchor → ∃ r ∈ reps, ∀ x, pass i x ↔ pass r x) :
    (∀ i, ∃ x, ¬pass i x) ↔
    ∃ suite : List X, anchor ∈ suite ∧ suite.length ≤ reps.length + 1 ∧
      ∀ i, ∃ x ∈ suite, ¬pass i x := by
  constructor
  · intro bad
    obtain ⟨ws, len, catches⟩ := finite_witnesses pass reps (fun r _ => bad r)
    refine ⟨anchor :: ws, by simp, by simpa using len, ?_⟩
    intro i
    by_cases h : pass i anchor
    · obtain ⟨r, hr, same⟩ := covered i h
      obtain ⟨x, hx, fails⟩ := catches r hr
      exact ⟨x, by simp [hx], fun hi => fails ((same x).mp hi)⟩
    · exact ⟨anchor, by simp, h⟩
  · rintro ⟨suite, _, _, catches⟩ i
    obtain ⟨x, _, fail⟩ := catches i
    exact ⟨x, fail⟩

end AnchoredLiteralCensus
