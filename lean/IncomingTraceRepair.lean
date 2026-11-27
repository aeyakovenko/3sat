import Std

/-! A locally feasible trace has a unique smallest set of entry-memory coordinates
that must be changed from a given reference memory in order to realize it. -/
namespace IncomingTraceRepair

inductive Event (A V : Type) where
  | read (address : A) (value : V)
  | store (address : A) (value : V)

variable {A V : Type} [DecidableEq A]

def put (m : A → V) (a : A) (v : V) (b : A) : V :=
  if b = a then v else m b

def feasible : List (Event A V) → (A → V) → Prop
  | [], _ => True
  | .read a v :: xs, m => m a = v ∧ feasible xs m
  | .store a v :: xs, m => feasible xs (put m a v)

/-- Whether the first access to b in the given interval is a read. -/
def incoming : List (Event A V) → A → Bool
  | [], _ => false
  | .read a _ :: xs, b => if b = a then true else incoming xs b
  | .store a _ :: xs, b => if b = a then false else incoming xs b

theorem feasible_iff_entry_agrees (xs : List (Event A V)) (base witness : A → V)
    (ok : feasible xs witness) :
    feasible xs base ↔ ∀ b, incoming xs b = true → base b = witness b := by
  induction xs generalizing base witness with
  | nil => simp [feasible, incoming]
  | cons u xs ih =>
    cases u with
    | read a v =>
      obtain ⟨head, tail⟩ := ok
      constructor
      · rintro ⟨same, rest⟩ b hb
        by_cases eq : b = a
        · subst b
          exact same.trans head.symm
        · exact ((ih base witness tail).mp rest) b (by simpa [incoming, eq] using hb)
      · intro agrees
        refine ⟨(agrees a (by simp [incoming])).trans head, (ih base witness tail).mpr ?_⟩
        intro b hb
        apply agrees b
        by_cases eq : b = a <;> simp_all [incoming]
    | store a v =>
      have next := ih (put base a v) (put witness a v) ok
      constructor
      · intro rest b hb
        by_cases eq : b = a
        · simp [incoming, eq] at hb
        · have same := next.mp rest b (by simpa [incoming, eq] using hb)
          simpa [put, eq] using same
      · intro agrees
        apply next.mpr
        intro b hb
        by_cases eq : b = a
        · simp [put, eq]
        · simpa [put, eq] using agrees b (by simpa [incoming, eq] using hb)

def patch (xs : List (Event A V)) (base witness : A → V) (b : A) : V :=
  if incoming xs b then witness b else base b

theorem patch_realizes (xs : List (Event A V)) (base witness : A → V)
    (ok : feasible xs witness) : feasible xs (patch xs base witness) := by
  apply (feasible_iff_entry_agrees xs _ witness ok).mpr
  intro b hb
  simp [patch, hb]

theorem patch_changes_only_forced (xs : List (Event A V)) (base witness other : A → V)
    (ok : feasible xs witness) (otherOk : feasible xs other) (b : A)
    (change : patch xs base witness b ≠ base b) : other b ≠ base b := by
  cases hb : incoming xs b with
  | false => simp [patch, hb] at change
  | true =>
    have same := (feasible_iff_entry_agrees xs other witness ok).mp otherOk b hb
    simpa [patch, hb, same] using change

end IncomingTraceRepair
