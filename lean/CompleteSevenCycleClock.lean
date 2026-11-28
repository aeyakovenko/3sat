import Std

namespace CompleteSevenCycleClock

inductive Arg where
  | imm (value : Fin 8)
  | reg (index : Fin 3)

inductive Cmp where | eq | ult | slt

inductive Program where
  | yes | no
  | ld (dst : Fin 3) (address : Arg) (next : Program)
  | br (op : Cmp) (left right : Arg) (onTrue onFalse : Program)

abbrev Registers := Fin 3 → Option Nat

def value (regs : Registers) : Arg → Option Nat
  | .imm v => some v.val
  | .reg i => regs i

def compareWord : Cmp → Nat → Nat → Bool
  | .eq, a, b => a == b
  | .ult, a, b => decide (a < b)
  | .slt, a, b => decide ((a ^^^ 4) < (b ^^^ 4))

/-- Cells 0, 1, 2 contain the packed input. All other three-bit addresses read zero. -/
def memory (mask addr : Nat) : Nat := (mask >>> (3 * addr)) % 8

/-- Terminals are free, and every comparison and every load, including an
indirect load, spends one tick. Uninitialized registers cannot be read. -/
def run (mask : Nat) : Program → Registers → Nat → Option Bool
  | .yes, _, _ => some true
  | .no, _, _ => some false
  | .ld _ _ _, _, 0 | .br _ _ _ _ _, _, 0 => none
  | .ld dst arg next, regs, t+1 => do
    let addr ← value regs arg
    run mask next (fun i => if i = dst then some (memory mask addr) else regs i) t
  | .br op a b onTrue onFalse, regs, t+1 => do
    let u ← value regs a
    let v ← value regs b
    if compareWord op u v then run mask onTrue regs t else run mask onFalse regs t

open Program Arg

private def x : Arg := reg 0
private def y : Arg := reg 1
private def z : Arg := reg 2

/-- The last input word is the bit at position six. -/
private def requireZ : Program := ld 2 (imm 2) (br .eq z (imm 0) no yes)

private def lowX : Program :=
  br .eq x (imm 3)
    (ld 1 (imm 1) (br .eq y (imm 3) requireZ
      (br .ult (imm 4) y (br .eq y (imm 6) no yes) no)))
    (ld 1 x (ld 2 y (br .ult (imm 4) z
      (br .eq z (imm 6) no yes) (br .eq z (imm 3) yes no))))

private def highX : Program :=
  ld 1 (imm 1) (br .ult (imm 4) y
    (br .eq x (imm 6) requireZ yes)
    (br .slt y (imm 2) no requireZ))

def program : Program := ld 0 (imm 0) (br .ult x (imm 5) lowX highX)

def cover (mask : Nat) : Bool :=
  (List.range 7).all fun i => mask.testBit i || mask.testBit ((i+1)%7)

theorem seven_steps_on_the_complete_catalog : ∀ mask : Fin 128,
    run mask.val program (fun _ => none) 7 = some (cover mask.val) := by
  native_decide

/-- This tree actually uses its seventh instruction on some inputs. The lower
bound for *every* tree comes separately from the exhaustive XOR gap-zero suite. -/
theorem this_program_needs_its_seventh_step :
    ∃ mask : Fin 128, run mask.val program (fun _ => none) 6 = none := by
  exact ⟨0, by native_decide⟩

end CompleteSevenCycleClock

namespace CompleteSevenCycleClock.FixedSixteen

/-- Coefficients are packed output words in increasing multilinear monomial-mask order. -/
private def first : Array Nat := #[9,14,26,30,16,10,6,0,7,12,3,0,12,0,0,0]
private def second : Array Nat :=
  #[60,48,50,34,44,47,6,0,46,52,51,0,10,0,0,0,31,25,51,0,55,0,0,0,21,0,0,0,0,0,0,0]
def cubic : Array Nat := #[49,93,88,14,118,57,120,49,21,80,78,1,114,30,71,0,32,12,93,108,96,90,108,0,48,102,38,0,29,0,0,0,97,15,78,35,52,99,52,0,103,22,47,0,20,0,0,0,124,27,63,0,16,0,0,0,38,0,0,0,0,0,0,0]

def polynomial (a : Array Nat) (x : Nat) : Nat := (List.range a.size).foldl
  (fun acc s => if (s &&& x) == s then acc ^^^ a[s]! else acc) 0

def weight (s : Nat) := ((List.range 6).filter (fun j => s.testBit j)).length
private def coverBits (n x : Nat) : Bool :=
  (List.range n).all fun j => x.testBit j || x.testBit ((j+1)%n)

def image : List Nat := [22,29,35,53,54,59,62,70,77,83,85,86,93,123,124,126]

theorem exact_degree_three :
    (∀ s : Fin 64, 3 < weight s → cubic[s.val]! = 0) ∧
      weight 7 = 3 ∧ cubic[7]! ≠ 0 := by native_decide

/-- The successor is defined and injective on every six-bit selector, independent
of the subsequent restriction to the sixteen original inputs. -/
theorem global_cubic_successor :
    (∀ x : Fin 64, polynomial cubic x < 128 ∧
      coverBits 6 x = coverBits 7 (polynomial cubic x)) ∧
    (∀ x y : Fin 64, polynomial cubic x = polynomial cubic y → x = y) := by
  native_decide

/-- These are the earlier two *global* quadratic maps and the current cubic,
composed on all sixteen four-bit ancestors. `image` is precisely the row list
in SevenImageSearch.compact_exclude_six. -/
def sortedAncestralOutputs : List Nat :=
  ((List.range 16).map (fun x => polynomial cubic
    (polynomial second (polynomial first x)))).mergeSort

theorem composed_image : sortedAncestralOutputs = image := by native_decide

end CompleteSevenCycleClock.FixedSixteen
