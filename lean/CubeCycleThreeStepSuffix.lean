import Std

namespace CubeCycleLastFresh

abbrev W := BitVec 4
def words : List W := (List.range 16).map (BitVec.ofNat 4)
abbrev Unary := W → W
abbrev Mask := Nat

def p (x : W) : Bool := [5,7,11,13,15].contains x.toNat

def mask (f : W → Bool) : Mask :=
  words.foldl (fun m x => if f x then m ||| (1 <<< x.toNat) else m) 0

def test (i : Nat) (x y : W) : Bool :=
  match i with
  | 0 => x == y
  | 1 => x.ult y
  | _ => x.slt y

def bit (b : Bool) : W := if b then 1 else 0

def alu (i : Nat) (x y : W) : W :=
  let s := y.toNat
  match i with
  | 0 => x &&& y
  | 1 => x ||| y
  | 2 => x ^^^ y
  | 3 => x + y
  | 4 => x - y
  | 5 => x * y
  | 6 => x <<< s
  | 7 => x >>> s
  | 8 => x.sshiftRight s
  | 9 => x <<< (s%4)
  | 10 => x >>> (s%4)
  | 11 => x.sshiftRight (s%4)
  | 12 => x.rotateLeft s
  | 13 => x.rotateRight s
  | 14 => bit (x == y)
  | 15 => bit (x.ult y)
  | 16 => bit (x.slt y)
  | 17 => bit (x != y)
  | 18 => bit (!(x.ult y))
  | 19 => bit (!(x.slt y))
  | 20 => if y == 0 then 0 else BitVec.ofNat 4 (x.toNat / y.toNat)
  | 21 => if y == 0 then 15 else BitVec.ofNat 4 (x.toNat / y.toNat)
  | 22 => if y == 0 then 0 else BitVec.ofNat 4 (x.toNat % y.toNat)
  | _ => if y == 0 then x else BitVec.ofNat 4 (x.toNat % y.toNat)

def publicArgs : List Unary := id :: words.map (fun k _ => k)

def guardMasks (u : Unary) : List Mask := Id.run do
  let mut out := []
  for v in publicArgs do
    for i in [0:3] do
      let a := mask (fun x => test i (u x) (v x))
      let b := mask (fun x => test i (v x) (u x))
      out := a :: b :: (65535 ^^^ a) :: (65535 ^^^ b) :: out
  return out

def basics : List Mask := (0 :: 65535 :: guardMasks id).eraseDups

def twoGuardsFail (domain : Mask) : Bool := Id.run do
  let target := mask p
  let fits := fun region => basics.any (fun v => ((v ^^^ target) &&& region) == 0)
  return basics.all (fun region => !(fits (domain &&& region) && fits (domain &&& (65535 ^^^ region))))

def oneAluFails (domain : Mask) : Bool := Id.run do
  let target := mask p
  let fitsTarget := fun (m : Mask) => ((m ^^^ target) &&& domain) == 0
  for i in [0:24] do
    for v in publicArgs do
      if (guardMasks (fun x => alu i x (v x))).any fitsTarget then return false
      if (guardMasks (fun x => alu i (v x) x)).any fitsTarget then return false
  return !(basics.any fitsTarget)

def distanceOnHigh (domain predicted : Mask) : Nat :=
  (words.filter (fun x => decide (4 ≤ x.toNat) && domain.testBit x.toNat &&
     (predicted.testBit x.toNat != p x))).length

/-- A sufficient condition on the sixteen-bit set of allowed values at a single
    unknown nibble. The last line excludes a load by that nibble followed by
    a comparison, with at most two earlier fixed writes. -/
def obstruction (domain : Mask) : Bool :=
  domain.testBit 5 && twoGuardsFail domain && oneAluFails domain &&
    [0,65535,0x00f0,0xff00].all (fun m => decide (3 ≤ distanceOnHigh domain m))

theorem all_words : obstruction 65535 = true := by native_decide

theorem eight_points : obstruction 0x7a38 = true := by native_decide

theorem distances_on_eight_points :
    ([0,65535,0x00f0,0xff00].map (distanceOnHigh 0x7a38)) = [3,4,3,4] := by decide

def covered (a b c d : W) : Bool :=
  let mask : BitVec 16 := a.zeroExtend 16 ||| (b.zeroExtend 16 <<< 4) |||
    (c.zeroExtend 16 <<< 8) ||| (d.zeroExtend 16 <<< 12)
  mask ||| mask.rotateLeft 1 == 65535

theorem one_free_nibble (a : W) :
   covered a 5 5 5 = p a ∧ covered 5 a 5 5 = p a ∧
   covered 5 5 a 5 = p a ∧ covered 5 5 5 a = p a := by
  revert a; decide +kernel

def highDomain (a : W) : Bool := [4,5,7,8,9,11,12,13,15].contains a.toNat

theorem two_free_nibbles (a b : W) (ha : highDomain a) (hb : highDomain b) :
   [covered a b 5 5, covered a 5 b 5, covered a 5 5 b, covered 5 a b 5,
    covered 5 a 5 b, covered 5 5 a b].all (· == (p a && p b)) := by
  revert a b; decide +kernel

end CubeCycleLastFresh


namespace CubeCycleThreeSteps
open CubeCycleLastFresh

abbrev Table := Array UInt8
abbrev Cut := UInt64

def constantRow (n : Nat) (x : UInt8) : Table := Array.replicate n x
def range16 := (List.range 16).toArray
def unaryColumns (xs ys : Table) : Array Table :=
  (range16.map fun i => constantRow xs.size i.toUInt8) ++ #[xs,ys]

def selectMask (xs : Table) (p : UInt8 → Bool) : Cut := Id.run do
  let mut result : Cut := 0
  for i in [:xs.size] do
    if p xs[i]! then result := result ||| ((1 : Cut) <<< i.toUInt64)
  return result

def lut (op : Nat) := (List.range 256).toArray.map fun xy =>
  (alu op (BitVec.ofNat 4 (xy/16)) (BitVec.ofNat 4 (xy%16))).toNat.toUInt8

def gate (op : Table) (x y : Table) : Table := Id.run do
  let mut r := Array.emptyWithCapacity x.size
  for i in [:x.size] do
    r := r.push op[(x[i]!.toNat*16 + y[i]!.toNat)]!
  return r

def cmpByte (i : Nat) (x y : UInt8) :=
  if i == 0 then x == y else if i == 1 then x < y else (x ^^^ 8) < (y ^^^ 8)

def cmpMask (i : Nat) (x y : Table) : Cut := Id.run do
  let mut r : Cut := 0
  for k in [:x.size] do
    if cmpByte i x[k]! y[k]! then r := r ||| ((1 : Cut) <<< k.toUInt64)
  return r

def rawCuts (allBits : Cut) (regs : Array Table) : Array Cut := Id.run do
  let mut results : Std.HashSet Cut := {}
  for u in regs do for v in regs do for i in [:3] do
    let c := cmpMask i u v
    results := (results.insert c).insert (c ^^^ allBits)
  return results.toList.toArray

def hits (target region : Cut) (cuts : Array Cut) :=
  cuts.any fun c => ((c ^^^ target) &&& region) == 0

def twoGuards (target region : Cut) (cuts : Array Cut) :=
  cuts.any fun c => hits target (region &&& c) cuts && hits target (region &&& ~~~c) cuts

def planted (addr : Table) (cell : UInt8) (val : UInt8) :=
  addr.map fun a => if a == cell then val else 0

def selectStore (addr dest value old : Table) : Table := Id.run do
  let mut r := Array.emptyWithCapacity addr.size
  for i in [:addr.size] do
    r := r.push (if addr[i]! == dest[i]! then value[i]! else old[i]!)
  return r

/-- Check all final guards involving the most recently computed value, in both polarities. -/
def finalFits (v : Table) (regs : Array Table) (labels : Array Bool) : Bool := Id.run do
  let mut pos : UInt32 := 0
  let mut neg : UInt32 := 0
  for i in [:v.size] do
    let bit := (1 : UInt32) <<< v[i]!.toUInt32
    if labels[i]! then pos := pos ||| bit else neg := neg ||| bit
    if (pos &&& neg) != 0 then break
  if (pos &&& neg) == 0 then
    for i in [:3] do for c in range16 do for swapped in #[false,true] do
      let mut mask : UInt32 := 0
      for a in range16 do
        let b := if swapped then cmpByte i c.toUInt8 a.toUInt8 else cmpByte i a.toUInt8 c.toUInt8
        if b then mask := mask ||| ((1 : UInt32) <<< a.toUInt32)
      if ((pos &&& ~~~mask) == 0 && (neg &&& mask) == 0) ||
          ((neg &&& ~~~mask) == 0 && (pos &&& mask) == 0) then return true
  for r in regs do
    let mut yes : UInt8 := 31
    let mut no : UInt8 := 31
    for k in [:v.size] do
      let a := v[k]!
      let b := r[k]!
      let mut observed : UInt8 := 0
      if a == b then observed := observed ||| 1
      if a < b then observed := observed ||| 2
      if b < a then observed := observed ||| 4
      if (a ^^^ 8) < (b ^^^ 8) then observed := observed ||| 8
      if (b ^^^ 8) < (a ^^^ 8) then observed := observed ||| 16
      if labels[k]! then
        yes := yes &&& observed
        no := no &&& ~~~observed
      else
        yes := yes &&& ~~~observed
        no := no &&& observed
      if (yes ||| no) == 0 then break
    if (yes ||| no) != 0 then return true
  return false

/-- Constant or variable-address first reads, with a known one-cell override. -/
def firstResults (xs ys : Table) (regs ops : Array Table) : Array Table := Id.run do
  let mut result : Std.HashSet Table := {}
  for x in regs do for y in regs do for op in ops do
    result := result.insert (gate op x y)
  for x in #[xs,ys] do for a in range16 do for c in range16 do
    result := result.insert (planted x a.toUInt8 c.toUInt8)
  return result.toList.toArray

def initialRead (xs ys ix : Table) (j k : Nat) : Table := Id.run do
  let mut r := Array.emptyWithCapacity xs.size
  for i in [:xs.size] do
    let a := ix[i]!.toNat
    r := r.push (if a == j then xs[i]! else if a == k then ys[i]! else if a < 4 then 5 else 0)
  return r

/-- True if an enlarged three-instruction model has a classifier on these rows. -/
def fitsThree (rows : Array (UInt8 × UInt8)) : Bool := Id.run do
  let xs := rows.map Prod.fst
  let ys := rows.map Prod.snd
  let labels := rows.map (fun (a,b) => p (BitVec.ofNat 4 a.toNat) && p (BitVec.ofNat 4 b.toNat))
  let target := selectMask (labels.map fun b => if b then 1 else 0) (· == 1)
  let allBits := ((1 : Cut) <<< rows.size.toUInt64) - 1
  let regs := unaryColumns xs ys
  let ops := (List.range 24).toArray.map lut
  let first := firstResults xs ys regs ops
  let basic := rawCuts allBits regs
  let mut afterOne : Std.HashSet Cut := {}
  for z in first do
    let cuts := rawCuts allBits (regs.push z)
    if twoGuards target allBits cuts then return true
    for c in cuts do afterOne := afterOne.insert c
  let allCuts := afterOne.toList.toArray
  let branchFits := fun region => hits target region allCuts || twoGuards target region basic
  for c in basic do
    if branchFits c && branchFits (allBits ^^^ c) then return true
  for z in first do
    let wires := #[xs,ys,z]
    for r in first do
      if finalFits r wires labels then return true
    for a in regs.push z do for op in ops do
      if finalFits (gate op a z) wires labels || finalFits (gate op z a) wires labels then return true
    for j in [:4] do for k in [:4] do
      if j != k then
        let original := initialRead xs ys z j k
        if finalFits original wires labels then return true
        for a in range16 do
          if z.contains a.toUInt8 then
            for b in range16 do
              let r := z.zipWith (fun addr old => if addr == a.toUInt8 then b.toUInt8 else old) original
              if finalFits r wires labels then return true
  for address in regs do
    let mut prior : Std.HashSet Table := {}
    if address == xs || address == ys then
      for a in range16 do for c in range16 do
        prior := prior.insert (planted address a.toUInt8 c.toUInt8)
    else
      for r in regs do prior := prior.insert r
    for dest in regs do for value in regs do for old in prior do
      if finalFits (selectStore address dest value old) #[xs,ys] labels then return true
  return false

def suffixCodes : List Nat :=
  [0x44,0x45,0x4b,0x54,0x55,0x59,0x5b,0x5c,0x7b,0x94,0x95,0xb4,0xb5,0xb7,0xbb,0xbc,0xc9,0xcb]

def pairRows : Array (UInt8 × UInt8) :=
  (suffixCodes.map fun n => ((n/16).toUInt8,(n%16).toUInt8)).toArray

theorem no_three_steps_on_eighteen_pairs : fitsThree pairRows = false := by native_decide

def replaceDigit (num i val : Nat) : Nat :=
  (num &&& (65535 ^^^ (15 <<< (4*i)))) ||| (val <<< (4*i))

def witnessSuite : List Nat := Id.run do
  let mut files := [0x5555]
  for i in [:4] do
    for a in [:16] do
      if Nat.testBit 0x7a38 a then files := replaceDigit 0x5555 i a :: files
    for j in [i+1:4] do
      for code in suffixCodes do
        files := replaceDigit (replaceDigit 0x5555 i (code/16)) j (code%16) :: files
  return files.eraseDups

theorem suite_size : witnessSuite.length = 89 := by native_decide

def isCover (n : Nat) : Bool :=
  let bits := BitVec.ofNat 16 n
  bits ||| bits.rotateLeft 1 == 65535

theorem suite_verdicts :
    (witnessSuite.filter isCover).length = 27 ∧
    (witnessSuite.filter (fun n => !(isCover n))).length = 62 := by native_decide

theorem pairs_in_high_domain :
    suffixCodes.all (fun code => highDomain (BitVec.ofNat 4 (code/16)) &&
         highDomain (BitVec.ofNat 4 (code%16))) = true := by decide +kernel

end CubeCycleThreeSteps

namespace CubeCycleSubdivision
def hole (u v : Bool) := !u && !v

theorem split (u v : Bool) :
    hole u (xor u v) = hole u v ∧ hole (xor u v) v = hole u v := by
  cases u <;> cases v <;> decide

theorem every_local_operation (f : Bool → Bool → Bool) :
    (∀ u v, hole u (f u v) = hole u v ∧ hole (f u v) v = hole u v) ↔
    (f false false = false ∧ f false true = true ∧ f true false = true) := by
  constructor
  · intro h
    have a := (h false false).1
    have b := (h false true).1
    have c := (h true false).2
    simpa [hole] using And.intro a (And.intro b c)
  · rintro ⟨a,b,c⟩ u v
    cases u <;> cases v <;> simp [hole,a,b,c]

end CubeCycleSubdivision

namespace CubeCycleWideLookup

def good (x : Nat) := [5,7,11].contains x
def alphabet : List Nat := [4,5,7,9,11,12]
def seed : Nat := [25,35,49,55,77,121].foldl (fun x i => x ||| (1 <<< (i-1))) 0

theorem bounded_products :
    alphabet.all (fun x => alphabet.all fun y =>
      decide (0 < x*y ∧ x*y ≤ 144) && (seed.testBit (x*y-1) == (good x && good y))) = true := by
  decide +kernel

theorem sign_source (w j : Nat) (pos : 0 < j) (hw : j ≤ w) :
    (w-1+j)%w = j-1 := by
  have eq : w-1+j = (j-1)+w := by omega
  rw [eq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

end CubeCycleWideLookup
