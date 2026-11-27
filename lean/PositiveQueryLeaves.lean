import Std

namespace PositiveQueryLeaves

/-- Entries are ordered from highest to lowest priority; none represents a
    leaf whose positive observations failed on this row. -/
def update (w z : Int) : Option Bool → Int
  | none => z
  | some false => z-w
  | some true => z+w

def tally : List (Option Bool) → Int
  | [] => 0
  | x::xs => update ((2:Int)^xs.length) (tally xs) x

/-- In the representation above the head has priority over the entire tail. -/
def winner : List (Option Bool) → Option Bool
  | [] => none
  | x::xs => x.orElse (fun _ => winner xs)

theorem bounded (xs : List (Option Bool)) :
    -((2:Int)^xs.length) < tally xs ∧ tally xs < (2:Int)^xs.length := by
  induction xs with
  | nil => decide
  | cons a xs ih =>
    simp only [List.length_cons, Int.pow_succ, tally]
    cases a with
    | none => simp [update]; omega
    | some b => cases b <;> simp [update] <;> omega

theorem correct_sign (xs : List (Option Bool)) :
    (winner xs = some true → 0 < tally xs) ∧
    (winner xs = some false → tally xs < 0) := by
  induction xs with
  | nil => simp [winner]
  | cons a xs ih =>
    have h := bounded xs
    cases a with
    | none => simpa [winner,tally,update] using ih
    | some b => cases b <;> simp [winner,tally,update, Option.orElse] <;> omega

/-- At the first differing observation, a candidate above the actual leaf
    necessarily contains a nonzero condition violated on that actual row. -/
theorem contradicted_positive {actual candidate : Nat} (higher : actual < candidate) :
    candidate ≠ 0 ∧ actual ≠ candidate := by omega

end PositiveQueryLeaves
