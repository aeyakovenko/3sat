import Std

namespace FilterRectangle

/-- The transition relation allows any number of nondeterministic successors.
    A layered machine can include its public layer index in the state. -/
def reads (step : σ → α → σ → Prop) (s : σ) : List α → σ → Prop
  | [], t => s = t
  | a :: rest, t => ∃ m, step s a m ∧ reads step m rest t

theorem concatenate {step : σ → α → σ → Prop} {s m t : σ}
    {xs ys : List α} (prefixRun : reads step s xs m) (suffixRun : reads step m ys t) :
    reads step s (xs ++ ys) t := by
  induction xs generalizing s with
  | nil =>
    have eq : s = m := prefixRun
    simpa [eq] using suffixRun
  | cons a xs ih =>
    obtain ⟨u, one, tail⟩ := prefixRun
    exact ⟨u, one, ih tail⟩

/-- A state at each cut and any chosen endpoint of the final local path. -/
def segments (step : σ → α → σ → Prop) (s : σ) : List (List α × σ) → σ → Prop
  | [], t => s = t
  | (piece, m) :: rest, t => reads step s piece m ∧ segments step m rest t

theorem glue_pieces {step : σ → α → σ → Prop} {s t : σ}
    (pieces : List (List α × σ)) (ok : segments step s pieces t) :
    reads step s ((pieces.map Prod.fst).flatten) t := by
  induction pieces generalizing s with
  | nil => exact ok
  | cons p rest ih =>
    rcases p with ⟨piece,m⟩
    obtain ⟨head,tail⟩ := ok
    exact concatenate head (ih tail)

/-- Pieces may have different types or lengths. If coordinates in distinct
    pieces must agree throughout their product, their value is fixed. -/
theorem fixed_across_pieces {ι : Type} {Piece : ι → Type} {Value : Type}
    (allowed : (p : ι) → Piece p → Prop) (i j : ι) (distinct : i ≠ j)
    (leftValue : Piece i → Value) (rightValue : Piece j → Value)
    (inhabited : ∃ x : (p : ι) → Piece p, ∀ p, allowed p (x p))
    (sound : ∀ x : (p : ι) → Piece p, (∀ p, allowed p (x p)) →
      leftValue (x i) = rightValue (x j)) :
    ∃ v : Value, ∀ x : (p : ι) → Piece p, (∀ p, allowed p (x p)) →
      leftValue (x i) = v ∧ rightValue (x j) = v := by
  classical
  obtain ⟨base,base_ok⟩ := inhabited
  refine ⟨rightValue (base j), ?_⟩
  intro x x_ok
  let mixed := fun p => if p = i then x p else base p
  have mixed_ok : ∀ p, allowed p (mixed p) := by
    intro p
    by_cases eq : p = i <;> simp [mixed, eq, x_ok, base_ok]
  have left_fixed : leftValue (x i) = rightValue (base j) := by
    simpa [mixed, Ne.symm distinct] using sound mixed mixed_ok
  exact ⟨left_fixed, (sound x x_ok).symm.trans left_fixed⟩

end FilterRectangle
