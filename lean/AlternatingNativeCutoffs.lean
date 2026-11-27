import Std

namespace AlternatingNativeCutoffs

inductive Player where
  | existential
  | universal

/-- Each internal node has its own finite set of available choices. -/
inductive Game where
  | terminal (answer : Bool)
  | move (player : Player) (arity : Nat) (child : Fin arity → Game)

def combine {n : Nat} (q : Player) (f : Fin n → Bool) : Bool :=
  match q with
  | .existential => (List.finRange n).any f
  | .universal => (List.finRange n).all f

/-- A universal node can be refuted by an existential choice of a false child. -/
theorem universal_refutation {n : Nat} (f : Fin n → Bool) :
    (!combine .universal f) = combine .existential (fun i => !f i) :=
  List.not_all_eq_any_not

private theorem combine_mono {n : Nat} (q : Player) {f g : Fin n → Bool}
    (h : ∀ i, f i = true → g i = true) :
    combine q f = true → combine q g = true := by
  cases q with
  | existential =>
    simp only [combine, List.any_eq_true]
    rintro ⟨i, hi, hf⟩
    exact ⟨i, hi, h i hf⟩
  | universal =>
    simp only [combine, List.all_eq_true]
    intro hf i hi
    exact h i (hf i hi)

def verdict : Game → Bool
  | .terminal b => b
  | .move q _ child => combine q fun i => verdict (child i)

/-- Histories list the most recent choice first. Stopping at a node skips all
    its descendants, so the explored domain is prefix-closed for any predicate.
    A reached terminal keeps its actual answer. -/
def truncated (stop : List Nat → Bool) (d : Bool) (history : List Nat) : Game → Bool
  | .terminal b => b
  | .move q _ child =>
    if stop history then d else
      combine q fun i => truncated stop d (i.val :: history) (child i)

theorem cutoff_bounds (g : Game) (stop : List Nat → Bool) (history : List Nat) :
    (truncated stop false history g = true → verdict g = true) ∧
    (verdict g = true → truncated stop true history g = true) := by
  induction g generalizing history with
  | terminal b => simp [truncated, verdict]
  | move q n child ih =>
    by_cases cut : stop history = true
    · simp [truncated, cut]
    · simp only [truncated, verdict, if_neg cut]
      exact ⟨combine_mono q (fun i => (ih i (i.val :: history)).1),
             combine_mono q (fun i => (ih i (i.val :: history)).2)⟩

/-- Agreement of both trials gives the untruncated root verdict. -/
theorem agreement_decides (g : Game) (stop : List Nat → Bool)
    (agree : truncated stop false [] g = truncated stop true [] g) :
    truncated stop false [] g = verdict g := by
  obtain ⟨lower, upper⟩ := cutoff_bounds g stop []
  rw [← agree] at upper
  cases lo : truncated stop false [] g <;> cases v : verdict g <;>
    simp_all

end AlternatingNativeCutoffs
