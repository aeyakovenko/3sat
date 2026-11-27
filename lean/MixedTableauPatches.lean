import Std

namespace MixedTableauPatches

def restrict (region : Int → Bool) : Option Int → Option Int
  | none => none
  | some x => if region x then some x else none

-- A head outside a patch cannot move directly to a site in its interior.
theorem interior_move (region interior : Int → Bool) (d : Int) (head : Option Int)
    (predecessor : ∀ x, interior (x + d) = true → region x = true) :
    restrict interior ((restrict region head).map (· + d)) =
      restrict interior (head.map (· + d)) := by
  cases head with
  | none => rfl
  | some x =>
    cases h : region x with
    | true => simp [restrict, h]
    | false =>
      have blocked : interior (x + d) = false := by
        cases candidate : interior (x + d) with
        | false => rfl
        | true =>
          have reachable := predecessor x candidate
          simp [h] at reachable
      simp [restrict, h, blocked]

def write (head : Option Int) (value : α) (tape : Int → α) (x : Int) : α :=
  if head = some x then value else tape x

theorem restrict_hit (region : Int → Bool) (head : Option Int) (x : Int)
    (inside : region x = true) :
    restrict region head = some x ↔ head = some x := by
  cases head with
  | none => simp [restrict]
  | some y =>
    by_cases equal : y = x
    · subst y; simp [restrict, inside]
    · cases region y <;> simp [restrict, *, equal]

def replay (region : Int → Bool) (tape : Int → α) :
    List (Option Int × α) → Int → α
  | [] => tape
  | (head, value) :: later => replay region (write (restrict region head) value tape) later

-- A local word and its chronological head/write log recover the correct word
-- at every epoch. Other positions in the initial tape can be arbitrary.
theorem replay_agrees (region : Int → Bool) (localTape globalTape : Int → α)
    (same : ∀ x, region x = true → localTape x = globalTape x)
    (log : List (Option Int × α)) :
    ∀ x, region x = true →
      replay region localTape log x = replay (fun _ => true) globalTape log x := by
  induction log generalizing localTape globalTape with
  | nil => exact same
  | cons event later ih =>
    obtain ⟨head, value⟩ := event
    apply ih
    intro x inside
    simp [write, restrict_hit region head x inside,
      restrict_hit (fun _ => true) head x rfl, same x inside]

end MixedTableauPatches
