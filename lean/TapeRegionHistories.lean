import Std

/-! Memory consistency for the region histories in multidimensional-tape-simulation.md.
The control verifier has reconstructed a proposed sequence of tape operations. Each
operation names a region and an offset, checks the old symbol, and writes a new
symbol. A pure read uses the claimed old symbol as its new symbol. -/
namespace TapeRegionHistories

structure Event (Region Cell Symbol : Type) where
  region : Region
  cell : Cell
  read : Symbol
  write : Symbol

def setAt [DecidableEq A] (f : A → V) (a : A) (v : V) (z : A) : V :=
  if z = a then v else f z

def valid [DecidableEq R] [DecidableEq C] (mem : R → C → S) :
    List (Event R C S) → Prop
  | [] => True
  | e :: es => mem e.region e.cell = e.read ∧
    valid (setAt mem e.region (setAt (mem e.region) e.cell e.write)) es

def validRegion [DecidableEq C] (row : C → S) : List (Event R C S) → Prop
  | [] => True
  | e :: es => row e.cell = e.read ∧ validRegion (setAt row e.cell e.write) es

def history [DecidableEq R] (r : R) (es : List (Event R C S)) :=
  es.filter (fun e => decide (e.region = r))

/-- Checking the projected history for each region verifies every claimed read. -/
theorem valid_iff_region_histories [DecidableEq R] [DecidableEq C]
    (mem : R → C → S) (es : List (Event R C S)) :
    valid mem es ↔ ∀ r, validRegion (mem r) (history r es) := by
  induction es generalizing mem with
  | nil => simp [valid, history, validRegion]
  | cons e es ih =>
    change (_ ∧ valid _ es) ↔ _
    rw [ih]
    constructor
    · rintro ⟨he, tail⟩ r
      by_cases eq : e.region = r
      · subst r
        have ht := tail e.region
        simpa [history, validRegion, setAt, he] using ht
      · simpa [history, setAt, eq, Ne.symm eq] using tail r
    · intro hs
      have both := hs e.region
      simp [history, validRegion] at both
      refine ⟨both.1, fun r => ?_⟩
      by_cases eq : e.region = r
      · subst r
        simpa [setAt, history] using both.2
      · simpa [setAt, history, eq, Ne.symm eq] using hs r

def finalRow [DecidableEq C] (row : C → S) : List (Event R C S) → C → S
  | [] => row
  | e :: es => finalRow (setAt row e.cell e.write) es

/-- Cutting one region's history at a snapshot preserves the check. -/
theorem validRegion_append [DecidableEq C] (row : C → S) (xs ys : List (Event R C S)) :
    validRegion row (xs ++ ys) ↔ validRegion row xs ∧ validRegion (finalRow row xs) ys := by
  induction xs generalizing row with
  | nil => simp [validRegion, finalRow]
  | cons e es ih => simp [validRegion, finalRow, ih, and_assoc]

/-- The outgoing row may be supplied by an existential snapshot and checked at the boundary. -/
theorem split_at_snapshot [DecidableEq C] (row : C → S) (xs ys : List (Event R C S)) :
    validRegion row (xs ++ ys) ↔ ∃ next, validRegion row xs ∧
      finalRow row xs = next ∧ validRegion next ys := by
  rw [validRegion_append]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨_, hx, rfl, hy⟩
  · rintro ⟨_, hx, rfl, hy⟩
    exact ⟨hx, hy⟩

end TapeRegionHistories
