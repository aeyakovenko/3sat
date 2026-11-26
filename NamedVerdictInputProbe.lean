import Std

namespace NamedVerdictInputProbe

abbrev Clause := Int × Int × Int

/-- The first seven clauses forbid every valuation on (3,4,5) except (1,0,0). -/
def clauses (digit : Int) : List Clause :=
  [(3,4,5), (3,4,-5), (3,-4,5), (3,-4,-5),
   (-3,4,-5), (-3,-4,5), (-3,-4,-5),
   (-1,4,5), (-2,4,5), (digit,4,5)]

def truth (x : Fin 32) (lit : Int) : Bool :=
  let val := x.val.testBit (lit.natAbs - 1)
  if lit < 0 then !val else val

def satisfies (x : Fin 32) (digit : Int) : Bool :=
  (clauses digit).all fun (a,b,c) => truth x a || truth x b || truth x c

def proper (digit : Int) : Bool :=
  (clauses digit).all fun (a,b,c) =>
    [a,b,c].all (fun lit => decide (1 ≤ lit.natAbs ∧ lit.natAbs ≤ 5)) &&
    a.natAbs != b.natAbs && a.natAbs != c.natAbs && b.natAbs != c.natAbs

theorem proper_both : proper 2 = true ∧ proper 3 = true := by decide

theorem digit_two_unsat : ∀ x : Fin 32, satisfies x 2 = false := by decide

theorem digit_three_unique : ∀ x : Fin 32, satisfies x 3 = true ↔ x.val = 4 := by decide

def fileBytes (digit : Int) : List Nat :=
  let body := (clauses digit).map fun (a,b,c) =>
    toString a ++ " " ++ toString b ++ " " ++ toString c ++ " 0\n"
  ("p cnf 5 10\n" ++ String.join body).toList.map Char.toNat

theorem same_length_one_bit :
    (fileBytes 2).length = (fileBytes 3).length ∧
    ((fileBytes 2).zip (fileBytes 3)).filter (fun (a,b) => a != b) = [(50,51)] ∧
    (50 : Nat) ^^^ 51 = 1 := by decide

/-- A finite deterministic word-read computation. Intermediate computation before
the next read has been incorporated into the branch function. -/
inductive ReadTree (Word Answer : Type) where
  | done (answer : Answer)
  | read (address : Nat) (next : Word → ReadTree Word Answer)

def run (input : Nat → Word) : ReadTree Word Answer → Answer
  | .done answer => answer
  | .read a next => run input (next (input a))

def sees (target : Nat) (input : Nat → Word) : ReadTree Word Answer → Prop
  | .done _ => False
  | .read a next => target = a ∨ sees target input (next (input a))

theorem required_read (tree : ReadTree Word Answer) (first second : Nat → Word)
    (target : Nat) (equalElsewhere : ∀ a, target ≠ a → first a = second a)
    (distinguished : run first tree ≠ run second tree) : sees target first tree := by
  induction tree with
  | done _ => exact False.elim (distinguished rfl)
  | read a next ih =>
    by_cases same : target = a
    · exact Or.inl same
    · apply Or.inr
      apply ih (first a)
      simpa only [run, ← equalElsewhere a same] using distinguished

def replay (view : Nat → Option Word) : ReadTree Word Answer → Option Answer
  | .done answer => some answer
  | .read a next => (view a).bind fun word => replay view (next word)

/-- A successful partial replay uses only defined words. -/
theorem replay_sound (tree : ReadTree Word Answer) (input : Nat → Word)
    (view : Nat → Option Word) (agrees : ∀ a w, view a = some w → input a = w)
    (answer : Answer) (completed : replay view tree = some answer) :
    run input tree = answer := by
  induction tree with
  | done _ => exact Option.some.inj completed
  | read a next ih =>
    cases word : view a with
    | none => simp [replay, word] at completed
    | some w =>
      simp only [run, agrees a w word]
      exact ih w (by simpa [replay, word] using completed)

/-- The replay clock uses the full padded receipt length. -/
theorem padding_dichotomy (b q fixedPart work : Nat) (accepted : Nat → Prop)
    (pad : ∀ length, fixedPart ≤ length → work ≤ length ^ q → accepted length)
    (excluded : ¬ accepted b) : b < fixedPart ∨ b ^ q < work := by
  by_cases fits : fixedPart ≤ b
  · exact Or.inr (Nat.lt_of_not_ge fun enough => excluded (pad b fits enough))
  · exact Or.inl (Nat.lt_of_not_ge fits)

end NamedVerdictInputProbe
