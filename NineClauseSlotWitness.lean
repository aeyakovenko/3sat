import Std

namespace NineClauseSlotWitness

structure Setting where
  a : Bool
  b : Bool
  c : Bool
deriving Repr, DecidableEq

def signed (positive x : Bool) : Bool := positive == x

/-- A changed mark turns a negative literal positive. The final physical
    row starts with variable 2 and has the same semantics as its sorted row. -/
def eval (p : Setting) (x y z : Bool) : Bool :=
  (x || y || !z) && (x || !y || !z) && (!x || y || !z) &&
  (!x || !y || z) && (signed p.a x || y || z) && (x || !y || z) &&
  (signed p.b x || y || z) && (!x || !y || !z) && (signed p.c y || x || z)

def sat (p : Setting) : Bool :=
  [false, true].any fun x => [false, true].any fun y => [false, true].any fun z =>
    eval p x y z

def center : Setting := ⟨false, false, false⟩
def oneA : Setting := ⟨true, false, false⟩
def oneB : Setting := ⟨false, true, false⟩
def oneC : Setting := ⟨false, false, true⟩
def both : Setting := ⟨true, true, false⟩
def suite : List Setting := [center, oneA, oneB, oneC, both]

theorem labels : suite.map sat = [true, false, false, false, true] := by decide

def bytes (p : Setting) : List Nat :=
  let s (changed : Bool) := if changed then " " else "-"
  ("p cnf 3 9\n1 2 -3 0\n1 -2 -3 0\n-1 2 -3 0\n-1 -2 3 0\n" ++
    s p.a ++ "1 2 3 0\n1 -2 3 0\n" ++ s p.b ++ "1 2 3 0\n-1 -2 -3 0\n" ++
    s p.c ++ "2 1 3 0").toList.map Char.toNat

def memory (p : Setting) (j : Nat) :=
  ((bytes p)[2*j]?).getD 0 + 256 * ((bytes p)[2*j+1]?).getD 0

theorem byte_length (a b c : Bool) : (bytes ⟨a,b,c⟩).length = 95 := by
  cases a <;> cases b <;> cases c <;> decide

def signWord (edit : Bool) : Nat := if edit then 0x200a else 0x2d0a

theorem word_layout (a b c : Bool) (j : Fin 48) :
    memory ⟨a,b,c⟩ j = (if j.val = 24 then signWord a else
      if j.val = 33 then signWord b else if j.val = 43 then signWord c else memory center j) := by
  have finite : ∀ u v t : Bool, ∀ i : Fin 48,
      memory ⟨u,v,t⟩ i = (if i.val = 24 then signWord u else
      if i.val = 33 then signWord v else if i.val = 43 then signWord t else memory center i) := by
    decide
  exact finite a b c j

theorem no_raw_private_address : ∀ j : Fin 48, memory center j > 43 := by decide

/-- Two register-indirect values at a sole final comparison cannot cover
    all three independently sensitive coordinates on a three-LOAD prefix. -/
inductive Source where | constant | first | second | third
deriving DecidableEq

def observed (s : Source) (p : Setting) :=
  match s with
  | .constant => false
  | .first => p.a
  | .second => p.b
  | .third => p.c

theorem two_sources_miss (i j : Source) :
    ∃ p ∈ suite, sat p ≠ sat center ∧
      observed i p = observed i center ∧ observed j p = observed j center := by
  cases i <;> cases j <;> first
    | exact ⟨oneA, by decide⟩
    | exact ⟨oneB, by decide⟩
    | exact ⟨oneC, by decide⟩

/-- The promise includes exactly the center, its single edits and the
    double edit in the first two sites. -/
def fiveSlot (p : Setting) :=
  if memory p 24 != memory p 33 then false else memory p 43 == 0x2d0a

theorem five_correct : ∀ p ∈ suite, fiveSlot p = sat p := by decide

end NineClauseSlotWitness
