import Std

namespace RetirementCutoff

/-- A stage supplies the list of signaling requirements in priority order.
    Retirement is the only information inherited by the next stage. -/
def winner (retired : Nat → Bool) (lo : Nat) : List Nat → Option Nat
  | [] => none
  | e :: rest =>
    if retired e = false ∧ lo ≤ e then some e else winner retired lo rest

theorem skip (retired : Nat → Bool) (lo : Nat) (signals : List Nat)
    (safe : ∀ e, winner retired 0 signals = some e → lo ≤ e) :
    winner retired lo signals = winner retired 0 signals := by
  induction signals with
  | nil => rfl
  | cons e rest ih =>
    by_cases active : retired e = false
    · have first : winner retired 0 (e :: rest) = some e := by simp [winner, active]
      have high := safe e first
      simp [winner, active, high]
    · simp [winner, active] at safe ⊢
      exact ih safe

def retire (old : Nat → Bool) : Option Nat → Nat → Bool
  | none => old
  | some e => fun i => decide (i = e) || old i

def trace (lo : Nat) (old : Nat → Bool) : List (List Nat) → List (Option Nat)
  | [] => []
  | signals :: tail =>
    let w := winner old lo signals
    w :: trace lo (retire old w) tail

/-- Folding stages under the cutoff produces the complete true winner sequence,
    including all intervening no-winner stages and both possible colors. -/
theorem same_window (lo : Nat) (old : Nat → Bool) (stages : List (List Nat))
    (safe : ∀ e, some e ∈ trace 0 old stages → lo ≤ e) :
    trace lo old stages = trace 0 old stages := by
  induction stages generalizing old with
  | nil => rfl
  | cons signals tail ih =>
    have headSafe : ∀ e, winner old 0 signals = some e → lo ≤ e := by
      intro e win
      exact safe e (by simp [trace, win])
    have tailSafe : ∀ e, some e ∈ trace 0 (retire old (winner old 0 signals)) tail → lo ≤ e := by
      intro e present
      exact safe e (List.mem_cons_of_mem _ present)
    simp only [trace, skip old lo signals headSafe, ih _ tailSafe]

end RetirementCutoff
