import Std

/-! Exact transition counts of the finite signed-interval tiles, with three
colors modulo three and first base color zero. -/
namespace SignedIntervalCountTiles

def sign (bits i : Nat) : Nat := if bits.testBit i then 2 else 1

def bases (n bits : Nat) : List Nat :=
  (List.range n).foldl (fun acc i => ((acc.head! + sign bits i) % 3) :: acc) [0] |>.reverse

def tips (n bits : Nat) : List Nat :=
  let y := bases n bits
  (List.range n).map fun i => (y[i]! + 3 - sign bits i) % 3

def accepted (p : List Nat) (bits : Nat) : Bool :=
  let z := tips p.length bits
  (p.zip p.tail).all fun (i,j) => z[i]! != z[j]!

def entry (p : List Nat) (incoming : Nat) (different : Bool) : Nat :=
  ((List.range (2 ^ p.length)).filter fun bits =>
    let z := tips p.length bits
    let y := bases p.length bits
    accepted p bits && (z[p.head!]! != incoming) &&
    ((z[p.getLast!]! != y.getLast!) == different)).length

structure Matrix where
  ee : Nat
  ed : Nat
  de : Nat
  dd : Nat
  deriving DecidableEq

def transfer (p : List Nat) : Matrix :=
  ⟨entry p 0 false, entry p 0 true, entry p 1 false, entry p 1 true⟩

def A := [1,2,0,4,5,3]
def B := [1,5,3,4,2,0]
def P := [0,2,1,3,5,4]
def reset := [1,2,0,3]
def tile := [1,4,3,5,6,0,2]

theorem small_transfers :
    transfer A = ⟨4,0,4,4⟩ ∧ transfer B = ⟨4,0,4,8⟩ ∧
    transfer P = ⟨16,0,8,0⟩ ∧ transfer reset = ⟨0,4,0,4⟩ ∧
    transfer tile = ⟨0,0,0,4⟩ := by native_decide

/-- Multiplication of a transfer with a column of suffix counts. -/
def applyM (m : Matrix) (s : Nat × Nat) : Nat × Nat :=
  (m.ee * s.1 + m.ed * s.2, m.de * s.1 + m.dd * s.2)

def word : List Bool → Nat × Nat
  | [] => (1, 1)
  | digit :: rest => applyM (transfer (if digit then B else A)) (word rest)

def decoded : List Bool → Nat
  | [] => 1
  | false :: rest => decoded rest + 1
  | true :: rest => 2 * decoded rest + 1

theorem code_value (bits : List Bool) :
    word bits = (4^bits.length, 4^bits.length * decoded bits) := by
  induction bits with
  | nil => rfl
  | cons h rest ih =>
    cases h <;>
      simp [word, decoded, ih, small_transfers.1, small_transfers.2.1,
        applyM, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    rw [show (8 : Nat) = 2*4 by decide]
    ac_rfl

/-- For either incoming state, appending reset and then a word multiplies
the number of realizations by the same positive integer. -/
theorem reset_multiplier (bits : List Bool) :
    applyM (transfer reset) (word bits) =
    (4^(bits.length+1) * decoded bits, 4^(bits.length+1) * decoded bits) := by
  rw [code_value, small_transfers.2.2.2.1]
  simp [applyM, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- The first sign freely chooses one of the two completions at each prescribed
terminal color. The sixth sign determines which of the two terminal colors it is. -/
theorem tile_refinement :
    ((List.range 128).filter fun b => accepted tile b) = [4,27,100,123] ∧
    ((List.range 128).filter fun b => accepted tile b).all (fun b =>
      (tips 7 b)[1]! == 0 && (tips 7 b)[2]! == 0 &&
      (bases 7 b).getLast! == ((3 - sign b 5) % 3)) = true := by
  native_decide

end SignedIntervalCountTiles
