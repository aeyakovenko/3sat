import Std

namespace BlockAddressCertificates

/-- Store and reported load projected onto one particular work address. -/
inductive Access (Word : Type) where
  | load (word : Word)
  | store (word : Word)

/-- Every consistent one-address block either needs an incoming word or can
    start with any word, and it optionally installs a final word. -/
structure Effect (Word : Type) where
  incoming : Option Word
  outgoing : Option Word

variable {Word : Type} [DecidableEq Word]

def needs (requirement : Option Word) (word : Word) : Bool :=
  match requirement with
  | none => true
  | some v => decide (v = word)

@[simp] theorem needs_none (w : Word) : needs none w = true := rfl
@[simp] theorem needs_some (v w : Word) : needs (some v) w = decide (v = w) := rfl

def runEffect (e : Option (Effect Word)) (word : Word) : Option Word :=
  match e with
  | none => none
  | some s => if needs s.incoming word then some (s.outgoing.getD word) else none

def run : List (Access Word) → Word → Option Word
  | [], w => some w
  | .store v :: xs, _ => run xs v
  | .load v :: xs, w => if v = w then run xs w else none

def prepend (a : Access Word) (tail : Option (Effect Word)) : Option (Effect Word) :=
  match a, tail with
  | _, none => none
  | .load v, some s =>
    if needs s.incoming v then some ⟨some v, s.outgoing⟩ else none
  | .store v, some s =>
    if needs s.incoming v then some ⟨none, some (s.outgoing.getD v)⟩ else none

def summarize : List (Access Word) → Option (Effect Word)
  | [] => some ⟨none, none⟩
  | h :: t => prepend h (summarize t)

/-- Exact simultaneously for every incoming memory value, including rejected
    traces, a read before the first store, and blocks without any stores. -/
theorem summarize_exact (events : List (Access Word)) (w : Word) :
    runEffect (summarize events) w = run events w := by
  induction events generalizing w with
  | nil => rfl
  | cons a tail ih =>
    cases a with
    | store v =>
      simp only [summarize, run, ← ih]
      cases h : summarize tail with
      | none => rfl
      | some s =>
        by_cases b : needs s.incoming v <;> simp [prepend, runEffect, b]
    | load v =>
      simp only [summarize, run, ← ih]
      cases h : summarize tail with
      | none => simp [prepend, runEffect]
      | some s =>
        by_cases equal : v = w
        · subst w
          by_cases b : needs s.incoming v <;> simp [prepend, runEffect, b]
        · by_cases b : needs s.incoming v <;> simp [prepend, runEffect, b, equal]

private theorem run_append (a b : List (Access Word)) (w : Word) :
    run (a ++ b) w = (run a w).bind (run b) := by
  induction a generalizing w with
  | nil => rfl
  | cons h t ih =>
    cases h with
    | store v => simpa [run] using ih v
    | load v => by_cases e : v = w <;> simp [run, e, ih]

/-- Consecutive exact summaries can be merged while keeping only the current
    word, regardless of which address hashes isolated it in each block. -/
theorem two_blocks (a b : List (Access Word)) (w : Word) :
    (runEffect (summarize a) w).bind (runEffect (summarize b)) = run (a ++ b) w := by
  simpa only [summarize_exact, funext (summarize_exact b)] using (run_append a b w).symm

/-- Isolation at the chosen address makes its entire chronological bucket
    projection exactly its true address projection. Other buckets may collide. -/
theorem isolated_bucket {Row Address Bucket : Type} [DecidableEq Address] [DecidableEq Bucket]
    (rows : List Row) (address : Row → Address) (hash : Address → Bucket) (z : Address)
    (isolated : ∀ r ∈ rows, hash (address r) = hash z → address r = z) :
    rows.filter (fun r => decide (hash (address r) = hash z)) =
    rows.filter (fun r => decide (address r = z)) := by
  apply List.filter_congr
  intro r member
  by_cases e : address r = z
  · simp [e]
  · have different : hash (address r) ≠ hash z := fun eq => e (isolated r member eq)
    simp [e, different]

end BlockAddressCertificates
