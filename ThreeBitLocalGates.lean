import Std

namespace ThreeBitLocalGates

abbrev V := Fin 8

def dot (x y : V) : Bool :=
  (x.val.testBit 0 && y.val.testBit 0) ^^
  (x.val.testBit 1 && y.val.testBit 1) ^^
  (x.val.testBit 2 && y.val.testBit 2)

def gate (a b n : V) : Bool :=
  decide (n ≠ 0 ∧ (a = 0 ∨ a = n)) && dot n b

def recover (a b : V) : Bool :=
  (List.finRange 8).foldl (fun parity n => parity ^^ gate a b n) false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem local_recovery : ∀ (a b : V), recover a b = dot a b := by decide

/-- Equality of the observable left parities at two inputs. -/
def seesSame (n a a' : V) : Prop := ∀ u : V, dot u n = false → dot u a = dot u a'

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem zero_lookup_is_local : ∀ (n a : V), n ≠ 0 →
    (seesSame n a 0 ↔ a = 0 ∨ a = n) := by
  unfold seesSame
  decide

theorem independent_blocks (xs : List (V × V)) :
    xs.foldr (fun p acc => recover p.1 p.2 ^^ acc) false =
    xs.foldr (fun p acc => dot p.1 p.2 ^^ acc) false := by
  simp only [local_recovery]

end ThreeBitLocalGates
