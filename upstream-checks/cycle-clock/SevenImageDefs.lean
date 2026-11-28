import CycleImageClock

namespace SevenImageSearch

-- Three 21-lane bit planes fit in a UInt64. Each lane is one input.
abbrev Col := UInt64
abbrev Cut := UInt64
def allRows : Cut := 2097151
def lanes (a : Col) (k : Nat) : Cut := (a >>> (21*k).toUInt64) &&& allRows
def getLane (v : Col) (i w : Nat) : Nat := Id.run do
  let mut r := 0
  for k in [:w] do
    r := r ||| (((v >>> (21*k+i).toUInt64) &&& 1).toNat <<< k)
  return r

def encode (w : Nat) (f : Nat → Nat) : Col := Id.run do
  let mut col : Col := 0
  for i in [:21] do
    let v := f i
    for k in [:w] do
      if v.testBit k then col := col ||| (1 <<< (21*k+i).toUInt64)
  return col

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
    for k in [1:w] do bits := bits ||| (select <<< (21*k).toUInt64)
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
    out := out.insert (encode w (fun i => CycleImageClock.ops w k (getLane a i w) (getLane b i w)))
  let vals := out.toArray
  modify fun c => {c with values := if c.values.size < 20000 then c.values.insert (a,b) vals else {}}
  return vals

def allCuts (w : Nat) (constants regs : Array Col) : StateM Cache (Array Cut) := do
  if let some cs := (← get).cuts[regs]? then return cs
  let mut cs : Std.HashSet Cut := {}
  let all := constants ++ regs
  for a in regs do for b in all do for c in pairMasks w a b do cs := cs.insert c
  let result := cs.toArray
  modify fun c => {c with cuts := if c.cuts.size < 22000 then c.cuts.insert regs result else {}}
  return result

@[inline] def splits (area goal c : UInt64) : Bool :=
  let h := area &&& c
  h == goal || h == (area ^^^ goal)

-- All possible nonconstant equality/unsigned-order/signed-order partitions
-- using either operand order, computed in parallel on 21 packed lanes.
@[inline] def finalPair (a b area goal : UInt64) : Bool := Id.run do
  let a0 := lanes a 0
  let a1 := lanes a 1
  let a2 := lanes a 2
  let b0 := lanes b 0
  let b1 := lanes b 1
  let b2 := lanes b 2
  let d0 := a0 ^^^ b0
  let d1 := a1 ^^^ b1
  let d2 := a2 ^^^ b2
  let eq := (~~~(d0 ||| d1 ||| d2)) &&& allRows
  if splits area goal eq then return true
  let lt := ((~~~a2) &&& b2) ||| ((~~~d2) &&& (((~~~a1) &&& b1) |||
     ((~~~d1) &&& ((~~~a0) &&& b0))))
  if splits area goal lt || splits area goal (eq ||| lt) then return true
  let slt := lt ^^^ d2
  return splits area goal slt || splits area goal (eq ||| slt)

def needsRead (regs : Array Col) (area goal : Cut) : Bool := Id.run do
  let wrong := area ^^^ goal
  for i in [:21] do
    if (goal &&& (1 <<< i.toUInt64)) != 0 then
      let mut rivals := wrong
      for col in regs do
        for k in [:3] do
          let b := lanes col k
          rivals := rivals &&& (if (b &&& (1 <<< i.toUInt64)) != 0 then b else ~~~b)
      if rivals != 0 then return true
  return false


structure Accumulator extends Cache where
  answers : Std.HashMap (Nat × Cut × Array Col × Array Col) Bool := {}
deriving Inhabited

def base (eval : StateM Cache α) : StateM Accumulator α := do
  let c ← get
  let (answer, data) := eval c.toCache
  set {c with toCache := data}
  return answer

def read3 (mem : Array Col) (addr : Col) : Col := Id.run do
  let a := lanes addr 0
  let b := lanes addr 1
  let c := lanes addr 2
  let mut out : Col := 0
  for j in [:8] do
    let pick := (if j.testBit 0 then a else ~~~a) &&&
      (if j.testBit 1 then b else ~~~b) &&& (if j.testBit 2 then c else ~~~c) &&& allRows
    out := out ||| (mem[j]! &&& (pick ||| (pick <<< 21) ||| (pick <<< 42)))
  return out

-- Fold identical columns on the current domain, mapping constant functions to
-- literal columns. The program may be specialized independently on each side.
def normal (area : Cut) (col : Col) : Col := Id.run do
  let l := lanes col 0 &&& area
  let m := lanes col 1 &&& area
  let h := lanes col 2 &&& area
  if (l == 0 || l == area) && (m == 0 || m == area) && (h == 0 || h == area) then
    return (if l == 0 then 0 else allRows) |||
      ((if m == 0 then 0 else allRows) <<< 21) |||
      ((if h == 0 then 0 else allRows) <<< 42)
  return l ||| (m <<< 21) ||| (h <<< 42)

def registersOn (constants regs : Array Col) (area : Cut) : Array Col := Id.run do
  let mut rs : Std.HashSet Col := {}
  for v in regs do
    let u := normal area v
    if !constants.contains u then rs := rs.insert u
  return rs.toArray.qsort (· < ·)

/-- If a row has an opposite-label rival after any k chosen current
    memory probes, that path needs k+1 loads followed by a branch. -/
def saturated (fuel : Nat) (regs mem : Array Col) (area goal : Cut) : Bool := Id.run do
  if fuel != 3 && fuel != 4 then return false
  let rivalsAt := fun (i : UInt64) (col : Col) =>
    let x := (1 : UInt64) <<< i
    let mask := fun (p : UInt64) => if (p &&& x) != 0 then p else ~~~p
    mask (lanes col 0) &&& mask (lanes col 1) &&& mask (lanes col 2)
  for i in [:21] do
    let bit := (1:UInt64) <<< i.toUInt64
    if (area &&& bit) != 0 then
      let mut opp := if (goal &&& bit) == 0 then goal else area ^^^ goal
      for v in regs do opp := opp &&& rivalsAt i.toUInt64 v
      if opp != 0 then
        let mut parts : Array Cut := #[]
        let mut allRivals := true
        for u in mem do
          let side := opp &&& rivalsAt i.toUInt64 u
          if side == 0 || (fuel == 4 && parts.any (fun old => (old &&& side) == 0)) then
            allRivals := false
            break
          parts := parts.push side
        if allRivals then return true
  return false

def two (constants regs mem : Array Col) (goal area : Cut) (cuts : Array Cut) (need : Bool) :
    StateM Accumulator Bool := do
  let all := constants ++ regs
  let finalValue := fun z => all.any fun v => finalPair z v area goal
  for addr in all do if finalValue (read3 mem addr) then return true
  if need then return false
  for c in cuts do
    let ls := area &&& c
    if ls != 0 && ls != area then
      let rs := area ^^^ ls
      let solved := fun side => (goal &&& side) == 0 || (goal &&& side) == side ||
        cuts.any fun t => splits side (goal &&& side) t
      if solved ls && solved rs then return true
  for a in regs do for b in all do
    if (← base (resultVals 3 a b)).any finalValue then return true
    if (← base (resultVals 3 b a)).any finalValue then return true
  return false

def search (constants : Array Col) (target : Cut) :
    Nat → Cut → Array Col → Array Col → StateM Accumulator Bool
  | 0, area, _, _ => pure ((target &&& area) == 0 || (target &&& area) == area)
  | fuel+1, area, regs, mem => do
    let key := (fuel, area, regs, mem)
    if let some cached := (← get).answers[key]? then return cached
    let worker : StateM Accumulator Bool := do
      let goal := target &&& area
      if goal == 0 || goal == area then return true
      let cuts ← base (allCuts 3 constants regs)
      if cuts.any (splits area goal) then return true
      if fuel == 0 then return false
      if fuel == 1 then return ← two constants regs mem goal area cuts (needsRead regs area goal)
      let vs := constants ++ regs
      let mut results : Std.HashSet Col := {}
      for x in vs do results := results.insert (normal area (read3 mem x))
      if saturated (fuel+1) regs mem area goal then
        for v in results.toArray do
          if !vs.contains v then
            if ← search constants target fuel area ((regs.push v).qsort (· < ·)) mem then return true
        return false
      for c in cuts do
        let l := area &&& c
        if l != 0 && l != area then
          let r := area ^^^ l
          if ← search constants target fuel l (registersOn constants regs l) (mem.map (normal l)) then
            if ← search constants target fuel r (registersOn constants regs r) (mem.map (normal r)) then return true
      for x in regs do for y in vs do
        for v in ← base (resultVals 3 x y) do results := results.insert (normal area v)
        for v in ← base (resultVals 3 y x) do results := results.insert (normal area v)
      for v in results.toArray do
        if !vs.contains v then
          if ← search constants target fuel area ((regs.push v).qsort (· < ·)) mem then return true
      for addr in vs do for val in vs do
        let m := (writeMem 3 mem addr val).map (normal area)
        if m != mem then if ← search constants target fuel area regs m then return true
      return false

    let answer ← worker
    if fuel >= 2 then
      modify fun c => {c with answers := if c.answers.size < 80000 then c.answers.insert key answer else {} }
    return answer


def cover (v : Nat) := CycleImageClock.cover 7 v

def suite : Array Nat := #[22,29,35,48,53,54,62,70,77,80,83,85,86,93,115,120,123,126]

def inXorImage (v : Nat) := v < 128 && (v.testBit 1 == (v.testBit 0 != v.testBit 2))
theorem in_image : suite.all inXorImage = true := by decide +kernel

def atDepth (fuel : Nat) : Bool := Id.run do
  let rows := fun i => suite[i]?.getD 22
  let constants := (List.range 8).toArray.map fun k => encode 3 (fun _ => k)
  let mem := (List.range 8).toArray.map fun j => encode 3 (fun i => ((rows i) >>> (3*j)) % 8)
  let mut target : Cut := 0
  for i in [:21] do if cover (rows i) then target := target ||| (1 <<< i.toUInt64)
  return ((search constants target fuel allRows #[] mem).run {}).1

end SevenImageSearch
