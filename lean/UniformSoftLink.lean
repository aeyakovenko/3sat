import Std

namespace UniformSoftLink

structure Aux where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  e : Bool
  f : Bool
deriving DecidableEq

/-- A physical ternary clause prohibiting one specified triple. -/
def disj (x y z px py pz : Bool) : Bool :=
  (x != px) || (y != py) || (z != pz)

def evenRows (x y z : Bool) : Bool :=
  disj x y z true false false && disj x y z false true false &&
  disj x y z false false true && disj x y z true true true

/-- Two clauses for the hard edge, twelve for the three XORs, and two
    groups of three clauses each permitting one extra odd pattern. -/
def holds (lit y z : Bool) (u : Aux) : Bool :=
  disj lit y z false true false && disj lit y z false false true &&
  evenRows lit u.e u.f && evenRows y u.b u.d && evenRows z u.c u.d &&
  disj u.a u.b u.f false true false && disj u.a u.b u.f false false true &&
  disj u.a u.b u.f true true true &&
  disj u.a u.c u.e true false false && disj u.a u.c u.e false false true &&
  disj u.a u.c u.e true true true

def good (lit y b e : Bool) : Aux :=
  ⟨b ^^ e ^^ lit, b, b ^^ lit, b ^^ y, e, e ^^ lit⟩

def missed (y alternate : Bool) : Aux :=
  ⟨!alternate, alternate, alternate, y ^^ alternate, !alternate, alternate⟩

/-- Exact fiber, with the free bits read back from the extension itself. -/
theorem support : ∀ lit y z a b c d e f : Bool,
    holds lit y z ⟨a,b,c,d,e,f⟩ = true ↔
      if lit = (y ^^ z) then (⟨a,b,c,d,e,f⟩ : Aux) = good lit y b e
      else lit = true ∧ (⟨a,b,c,d,e,f⟩ : Aux) = missed y b := by
  decide

def coord (u : Aux) (i : Fin 6) : Bool :=
  [u.a, u.b, u.c, u.d, u.e, u.f][i.val]?.getD false

def goodFiber (lit y : Bool) : List Aux :=
  [good lit y false false, good lit y false true,
   good lit y true false, good lit y true true]

def missedFiber (y : Bool) : List Aux := [missed y false, missed y true]

theorem balanced_good : ∀ (lit y : Bool) (i : Fin 6),
    ((goodFiber lit y).filter (fun u => coord u i)).length = 2 := by decide

theorem balanced_missed : ∀ (y : Bool) (i : Fin 6),
    ((missedFiber y).filter (fun u => coord u i)).length = 1 := by decide

def pairSum (lit y : Bool) (i j : Fin 6) : Int :=
  ((goodFiber lit y).map
    (fun u => if coord u i = coord u j then (1 : Int) else -1)).sum

def char4 (b : Bool) : Int := if b then -4 else 4

/-- The choice of boundary character is fixed by the coordinate pair, before
    the boundary bits are supplied. On a matched edge z equals lit XOR y. -/
theorem good_pair_character : ∀ (i j : Fin 6), i ≠ j →
    (∀ lit y, pairSum lit y i j = 0) ∨
    (∀ lit y, pairSum lit y i j = char4 lit) ∨
    (∀ lit y, pairSum lit y i j = char4 y) ∨
    (∀ lit y, pairSum lit y i j = char4 (lit ^^ y)) := by decide

end UniformSoftLink
