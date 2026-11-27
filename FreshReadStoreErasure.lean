import Std

namespace FreshReadStoreErasure

universe u v w
variable {Address : Type u} {Word : Type v} {State : Type w}

/-- A fixed control path. A read may select its address from the current state. -/
inductive Step (Address : Type u) (Word : Type v) (State : Type w) where
  | compute (next : State → State)
  | read (address : State → Address) (next : State → Word → State)

/-- Preserve both the final state and every physical address in execution order. -/
def run (memory : Address → Word) :
    List (Step Address Word State) → State → State × List Address
  | [], state => (state, [])
  | .compute next :: rest, state => run memory rest (next state)
  | .read address next :: rest, state =>
    let a := address state
    let tail := run memory rest (next state (memory a))
    (tail.1, a :: tail.2)

/-- Agreement away from one cell suffices when the first execution avoids it. -/
theorem agree_on_avoided_cell (left right : Address → Word) (cell : Address)
    (agree : ∀ a, a ≠ cell → left a = right a)
    (program : List (Step Address Word State)) (state : State)
    (avoids : cell ∉ (run left program state).2) :
    run left program state = run right program state := by
  induction program generalizing state with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | compute next =>
      exact ih (next state) avoids
    | read address next =>
      have ne : address state ≠ cell := by
        intro eq
        apply avoids
        simp [run, eq]
      have tail : cell ∉ (run left rest (next state (left (address state)))).2 := by
        intro member
        exact avoids (List.mem_cons_of_mem _ member)
      have same := ih (next state (left (address state))) tail
      simp only [run, ← agree _ ne, same]

def write [DecidableEq Address] (memory : Address → Word) (cell : Address)
    (value : Word) : Address → Word :=
  fun a => if a = cell then value else memory a

/-- The initial store can be dropped on the asserted no-hit subdomain.
    Either execution may be used to establish that the cell is avoided. -/
theorem erase_if_either_avoids [DecidableEq Address] (memory : Address → Word)
    (cell : Address) (value : Word) (program : List (Step Address Word State))
    (state : State)
    (avoids : cell ∉ (run memory program state).2 ∨
      cell ∉ (run (write memory cell value) program state).2) :
    run memory program state = run (write memory cell value) program state := by
  rcases avoids with baseline | stored
  · exact agree_on_avoided_cell _ _ cell
      (fun a ne => by simp [write, ne]) _ _ baseline
  · exact (agree_on_avoided_cell _ _ cell
      (fun a ne => by simp [write, ne]) _ _ stored).symm

/-- A sound test after a store remains sound in the guarded, store-free run. -/
theorem guarded_acceptance [DecidableEq Address] (memory : Address → Word)
    (cell : Address) (value : Word) (program : List (Step Address Word State))
    (state : State) (accept : State → Prop) (answer : Prop)
    (sound : accept (run (write memory cell value) program state).1 → answer)
    (nohit : cell ∉ (run memory program state).2)
    (passed : accept (run memory program state).1) : answer := by
  have eq := erase_if_either_avoids memory cell value program state (Or.inl nohit)
  exact sound (eq ▸ passed)

/-- An accepted execution whose later reads are fresh survives the guarded test. -/
theorem retained_acceptance [DecidableEq Address] (memory : Address → Word)
    (cell : Address) (value : Word) (program : List (Step Address Word State))
    (state : State) (accept : State → Prop)
    (nohit : cell ∉ (run (write memory cell value) program state).2)
    (passed : accept (run (write memory cell value) program state).1) :
    cell ∉ (run memory program state).2 ∧ accept (run memory program state).1 := by
  rw [erase_if_either_avoids memory cell value program state (Or.inr nohit)]
  exact ⟨nohit, passed⟩

end FreshReadStoreErasure
