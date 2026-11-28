import Std

namespace CycleImageClock

-- Sixteen source inputs, one lane per raw four-bit selector array. Each
-- column stores the bits of one register, grouped by significance.
abbrev Col := UInt64
abbrev Cut := UInt64
def allRows : Cut := 65535
def lanes (a : Col) (k : Nat) : Cut := (a >>> (16*k).toUInt64) &&& allRows
def getLane (v : Col) (i w : Nat) : Nat := Id.run do
  let mut r := 0
  for k in [:w] do
    r := r ||| (((v >>> (16*k+i).toUInt64) &&& 1).toNat <<< k)
  return r

def encode (w : Nat) (f : Nat → Nat) : Col := Id.run do
  let mut col : Col := 0
  for i in [:16] do
    let v := f i
    for k in [:w] do
      if v.testBit k then col := col ||| (1 <<< (16*k+i).toUInt64)
  return col

def ops (w k a b : Nat) : Nat :=
  let K := 1 <<< w
  let m := K-1
  let lowShift := b % w
  let arithmetic := fun s =>
    if a < K/2 then a >>> s else ((a >>> (min s w)) ||| (m <<< (w - min s w))) &&& m
  let pred := fun p : Bool => if p then 1 else 0
  match k with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ b
  | 3 => (a+b) &&& m
  | 4 => (K+a-b) &&& m
  | 5 => (a*b) &&& m
  | 6 => (a <<< b) &&& m
  | 7 => a >>> b
  | 8 => arithmetic b
  | 9 => (a <<< lowShift) &&& m
  | 10 => a >>> lowShift
  | 11 => arithmetic lowShift
  | 12 => ((a <<< lowShift) ||| (a >>> (w-lowShift))) &&& m
  | 13 => ((a >>> lowShift) ||| (a <<< (w-lowShift))) &&& m
  | 14 => pred (a == b)
  | 15 => pred (a < b)
  | 16 => pred ((a ^^^ (K/2)) < (b ^^^ (K/2)))
  | 17 => pred (a != b)
  | 18 => pred (a ≥ b)
  | 19 => pred ((a ^^^ (K/2)) ≥ (b ^^^ (K/2)))
  | 20 => if b == 0 then 0 else a / b
  | 21 => if b == 0 then m else a / b
  | 22 => if b == 0 then 0 else a % b
  | _ => if b == 0 then a else a % b

def pairMasks (w : Nat) (a b : Col) : Array Cut := Id.run do
  let mut eq := allRows
  let mut lt : Cut := 0
  for k in [:w] do
    let x := lanes a k
    let y := lanes b k
    let same := allRows ^^^ (x ^^^ y)
    eq := eq &&& same
    lt := ((allRows ^^^ x) &&& y) ||| (lt &&& same)
  let signDiff := lanes a (w-1) ^^^ lanes b (w-1)
  let slt := lt ^^^ signDiff
  return #[eq, lt, allRows ^^^ (eq ||| lt), slt, allRows ^^^ (eq ||| slt)]

def readMem (w : Nat) (mem : Array Col) (addr : Col) : Col :=
  encode w (fun i => getLane (mem[getLane addr i w]!) i w)

def writeMem (w : Nat) (mem : Array Col) (addr val : Col) : Array Col := Id.run do
  let mut result := mem
  for j in [:mem.size] do
    let select := (pairMasks w addr (encode w (fun _ => j)))[0]!
    let mut bits := select
    for k in [1:w] do bits := bits ||| (select <<< (16*k).toUInt64)
    result := result.set! j ((bits &&& val) ||| ((~~~bits) &&& mem[j]!))
  return result

structure Cache where
  values : Std.HashMap (Col × Col) (Array Col) := {}
  cuts : Std.HashMap (Array Col) (Array Cut) := {}
deriving Inhabited

def resultVals (w : Nat) (a b : Col) : StateM Cache (Array Col) := do
  if let some vals := (← get).values[(a,b)]? then return vals
  let mut out : Std.HashSet Col := {}
  for k in [:24] do
    out := out.insert (encode w (fun i => ops w k (getLane a i w) (getLane b i w)))
  let vals := out.toArray
  modify fun c => {c with values := c.values.insert (a,b) vals}
  return vals

def allCuts (w : Nat) (constants regs : Array Col) : StateM Cache (Array Cut) := do
  if let some cs := (← get).cuts[regs]? then return cs
  let mut cs : Std.HashSet Cut := {}
  let all := constants ++ regs
  for a in regs do for b in all do for c in pairMasks w a b do cs := cs.insert c
  let result := cs.toArray
  modify fun c => {c with cuts := c.cuts.insert regs result}
  return result

/-- Existence of a complete decision tree within the current fuel on the
    selected lanes. Registers hold every distinct previously computed nonliteral
    column, and memory holds one column per writable address. A branch may
    choose independent programs on its two nonempty fibers. -/
def synth (w : Nat) (constants : Array Col) (target : Cut) :
    Nat → Cut → Array Col → Array Col → StateM Cache Bool
  | 0, area, _, _ => pure ((target &&& area) == 0 || (target &&& area) == area)
  | fuel+1, area, regs, memory => do
    let goal := target &&& area
    if goal == 0 || goal == area then return true
    let cs ← allCuts w constants regs
    if cs.any (fun c => (c &&& area) == goal || (c &&& area) == (area ^^^ goal)) then return true
    if fuel == 0 then return false
    for c in cs do
      let l := area &&& c
      if l != 0 && l != area then
        if ← synth w constants target fuel l regs memory then
          if ← synth w constants target fuel (area ^^^ l) regs memory then return true
    let operands := constants ++ regs
    -- Constant/constant arithmetic returns an available literal. Registers
    -- are unbounded, so appending a duplicate column adds no new behavior.
    let mut values : Std.HashSet Col := {}
    for a in regs do for b in operands do
      for z in ← resultVals w a b do values := values.insert z
      for z in ← resultVals w b a do values := values.insert z
    for a in operands do values := values.insert (readMem w memory a)
    for v in values.toArray do
      if !operands.contains v then
        if ← synth w constants target fuel area (regs.push v) memory then return true
    -- A store can affect a terminal label only via a later load and branch.
    if fuel ≥ 2 then
      for a in operands do for v in operands do
        let m := writeMem w memory a v
        if m != memory then
          if ← synth w constants target fuel area regs m then return true
    return false

def insertBit (v g : Nat) : Nat :=
  let tail := g + 1
  let x := (v.testBit g) != (v.testBit (tail%4))
  (v % (1 <<< tail)) ||| ((if x then 1 else 0) <<< tail) |||
    ((v >>> tail) <<< (tail+1))

def cover (n v : Nat) : Bool :=
  (List.range n).all fun j => v.testBit j || v.testBit ((j+1)%n)

def canDecide (gap : Option Nat) (fuel : Nat) : Bool := Id.run do
  let w := if gap.isSome then 3 else 2
  let n := if gap.isSome then 5 else 4
  let raw := fun i => gap.elim i (insertBit i)
  let K := 1 <<< w
  let constants := (List.range K).toArray.map fun c => encode w (fun _ => c)
  let memory := (List.range K).toArray.map fun j => encode w (fun i => (raw i >>> (w*j)) % K)
  let mut target : Cut := 0
  for i in [:16] do if cover n (raw i) then target := target ||| (1 <<< i.toUInt64)
  return ((synth w constants target fuel allRows #[] memory).run {}).1

/-- Two native low/high word loads and an AND/guard for the four-cycle.
    The fifth-bit gap-zero construction uses the full width-three word
    subtraction 0-x, followed by AND with the high word y and a guard. -/
theorem upper_identities (v : Fin 16) :
    (cover 4 v.val = (((v.val % 4) &&& (v.val / 4)) != 0)) ∧
    (let z := insertBit v.val 0
     cover 5 z = ((((8-(z%8))%8) &&& (z/8)) != 0)) := by
  revert v; decide +kernel

theorem subdivision_preserves (g : Fin 4) (v : Fin 16) :
    cover 5 (insertBit v.val g.val) = cover 4 v.val := by
  revert g v; decide +kernel

theorem before_subdivision : canDecide none 3 = false := by native_decide

theorem after_subdivision_gap0 : canDecide (some 0) 4 = false := by native_decide

theorem after_subdivision_gap1 : canDecide (some 1) 4 = true := by native_decide

theorem after_subdivision_gap2 : canDecide (some 2) 4 = false := by native_decide

theorem after_subdivision_gap3 : canDecide (some 3) 4 = false := by native_decide

end CycleImageClock
