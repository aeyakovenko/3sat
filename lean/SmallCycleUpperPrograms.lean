import Std

namespace SmallCycleUpperPrograms

def cover (length mask : Nat) : Bool :=
  (List.range length).all fun i =>
    mask.testBit i || mask.testBit ((i + 1) % length)

def insertXor (mask gap : Nat) : Nat :=
  let cut := 2 ^ (gap + 1)
  let z := mask.testBit gap != mask.testBit ((gap + 1) % 4)
  mask % cut + (if z then cut else 0) + 2 * cut * (mask / cut)

def signedLess (a b : Nat) : Bool := decide ((a ^^^ 4) < (b ^^^ 4))

-- Three instructions when the second word is loaded first.
def twoBits (mask : Nat) : Bool :=
  let x := mask % 2
  let y := mask / 2
  let loaded := if y == 0 then x else y
  loaded != 0

def threeBits (mask : Nat) : Bool :=
  let x := mask % 4
  let y := mask / 4
  if y == 0 then x == 3 else x != 0

def fourBitsWidthTwo (mask : Nat) : Bool :=
  ((mask % 4) &&& (mask / 4)) != 0

def fourBitsWidthThree (mask : Nat) : Bool :=
  let x := mask % 8
  let y := mask / 8
  let r := (x*x) % 8
  if signedLess r x then y != 0 else decide (5 ≤ x)

def fiveBits (mask : Nat) : Bool :=
  let x := mask % 8
  let y := mask / 8
  if x == y then decide (2 < x)
  else if y < 2 then (x &&& y) != 0
  else if x < y then x == 2
  else decide (5 ≤ x)

def sixBits (mask : Nat) : Bool :=
  let x := mask % 8
  let y := mask / 8
  if x < y then
    if signedLess x 2 then decide (5 ≤ x) else (y &&& 5) == 5
  else
    if x < 5 then (x &&& y) == 3
    else if signedLess y 2 then decide (5 ≤ y) else x != 6

def imageProgram (gap mask : Nat) : Bool :=
  let x := mask % 8
  let y := mask / 8
  if gap == 0 then
    let r := x &&& y
    if y == 2 then signedLess x 0 else r != 0
  else if gap == 1 then (x &&& y) != 0
  else if gap == 2 then
    let r := x*x % 8
    if signedLess r x then decide (2 ≤ y) else decide (5 ≤ x)
  else
    if x < y then x == 2 else decide (1 < x / y)

theorem twoBits_spec : ∀ v : Fin 4, twoBits v.val = cover 2 v.val := by native_decide
theorem threeBits_spec : ∀ v : Fin 8, threeBits v.val = cover 3 v.val := by native_decide
theorem fourBitsWidthTwo_spec : ∀ v : Fin 16, fourBitsWidthTwo v.val = cover 4 v.val := by native_decide
theorem fourBitsWidthThree_spec : ∀ v : Fin 16, fourBitsWidthThree v.val = cover 4 v.val := by native_decide
theorem fiveBits_spec : ∀ v : Fin 32, fiveBits v.val = cover 5 v.val := by native_decide

theorem sixBits_spec : ∀ v : Fin 64, sixBits v.val = cover 6 v.val := by native_decide

theorem imagePrograms_spec : ∀ gap : Fin 4, ∀ v : Fin 16,
    let out := insertXor v.val gap.val
    out < 32 ∧ imageProgram gap.val out = cover 5 out ∧ cover 5 out = cover 4 v.val := by
  native_decide

end SmallCycleUpperPrograms
