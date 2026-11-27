import Std

namespace GrayCycleBankClosure

-- Full assignments are the 16 bit positions, and the four arrays of rows
-- are cylindrical along the coordinates missing from their three-name scopes.
abbrev Rows := UInt16

def full : Rows := 65535

def stride (i : Nat) : Rows := (1 : Rows) <<< i.toUInt16

def lower : Nat → Rows
  | 0 => 0x5555
  | 1 => 0x3333
  | 2 => 0x0f0f
  | _ => 0x00ff

def existsBit (i : Nat) (r : Rows) : Rows :=
  r ||| ((r &&& lower i) <<< stride i) ||| ((r &&& (~~~lower i)) >>> stride i)

def ownHull (j : Nat) (r : Rows) : Rows := Id.run do
  let mut out := full
  for i in [0:4] do
    if i != j then out := out &&& existsBit i r
  return out

def step (original localBanRows : Array Rows) : Array Rows := Id.run do
  let mut result := localBanRows
  for j in [0:4] do
    let old := original[j]!
    if old != full then
      let r := old &&& localBanRows[j]!
      for i in [0:4] do
        let image := if i == j then ownHull j r else existsBit i r
        result := result.set! i (result[i]! &&& image)
  return result

def reaches (original : Array Rows) : Bool := Id.run do
  let mut localBanRows := #[full, full, full, full]
  for _ in [0:6] do
    localBanRows := step original localBanRows
  return (List.range 4).all fun i => (localBanRows[i]! &&& (~~~original[i]!)) == 0

def axis : Nat → Nat
  | 1 => 0
  | 2 => 1
  | 4 => 2
  | _ => 3

def tables (cycle : Array Nat) (missing : Nat) : Array Rows := Id.run do
  let mut out := #[full, full, full, full]
  for i in [0:16] do
    if !missing.testBit i then
      let u := cycle[i]!
      let v := cycle[(i+1)%16]!
      let j := axis (u ^^^ v)
      let e := (1 : Rows) <<< u.toUInt16 ||| (1 : Rows) <<< v.toUInt16
      out := out.set! j (out[j]! &&& (~~~e))
  return out

-- Representatives with fixed orientation and a vertex at the origin.
def representatives : List (Array Nat) := [
  #[0,1,3,2,6,4,5,7,15,11,9,13,12,14,10,8],
  #[0,1,3,2,6,4,5,7,15,11,10,14,12,13,9,8],
  #[0,1,3,2,6,4,5,7,15,13,12,14,10,11,9,8],
  #[0,1,3,2,6,4,5,7,15,14,12,13,9,11,10,8],
  #[0,1,3,2,6,4,12,13,5,7,15,14,10,11,9,8],
  #[0,1,3,2,6,4,12,14,10,11,15,7,5,13,9,8],
  #[0,1,3,2,6,7,5,4,12,13,15,14,10,11,9,8],
  #[0,1,3,2,6,7,5,13,9,8,10,11,15,14,12,4],
  #[0,1,3,2,6,7,5,13,15,14,10,11,9,8,12,4]]

def permutations4 : List (List Nat) := Id.run do
  let mut out := []
  for i in [0:4] do
    for j in [0:4] do
      for k in [0:4] do
        for l in [0:4] do
          let p := [i,j,k,l]
          if p.eraseDups.length == 4 then out := p :: out
  return out

def permuteBits (p : List Nat) (x : Nat) : Nat :=
  ((List.range 4).zip p).foldl
    (fun acc ij => if x.testBit ij.1 then acc + 2^ij.2 else acc) 0

def appendVertex (code : UInt64) (vertex : Nat) : UInt64 :=
  (code <<< 4) ||| vertex.toUInt64

def transformed : Std.HashSet UInt64 := Id.run do
  let mut found : Std.HashSet UInt64 := {}
  for c in representatives do
    for p in permutations4 do
      for j in [0:16] do
        for rev in [false,true] do
          let mut code : UInt64 := 0
          for i in [0:16] do
            let dist := if rev then 16-i else i
            let v := c[(j+dist)%16]! ^^^ c[j]!
            code := appendVertex code (permuteBits p v)
          found := found.insert code
  return found

def coverPaths (found : Std.HashSet UInt64) (current seen : Nat) (code : UInt64) : Nat → Bool
  | 0 => !([1,2,4,8].contains current) || found.contains code
  | gas+1 => [1,2,4,8].all fun dir =>
      let v := current ^^^ dir
      seen.testBit v || coverPaths found v (seen ||| 2^v) (appendVertex code v) gas

theorem allHamiltonCyclesCovered :
    transformed.size = 2688 ∧ coverPaths transformed 0 1 0 15 = true := by
  native_decide

def masks : Nat → Nat → List Nat
  | 0, _ => [0]
  | _+1, 0 => [0]
  | n+1, b+1 => masks n (b+1) ++ (masks n b).map (· + 2^n)

def exactModels (raw : Array Rows) : Rows := raw.foldl (· &&& ·) full

def globalHull (r : Rows) : Rows := Id.run do
  let mut out := full
  for i in [0:4] do
    for j in [0:i] do
      out := out &&& existsBit i (existsBit j r)
  return out

def atMostOne (r : Rows) : Bool := (r &&& (r-1)) == 0

theorem sixMissingHasAtMostOneHole :
    representatives.all (fun c => (masks 16 6).all (fun m =>
      let r := exactModels (tables c m)
      atMostOne (globalHull r &&& (~~~r)))) = true := by
  native_decide

theorem coverageOfRepresentatives :
    representatives.all (fun c => (masks 16 5).all (fun m => reaches (tables c m))) = true := by
  native_decide

abbrev one (a b c : Bool) := [a,b,c].count true = 1

theorem uniqueAnchor (t u v w : Bool) :
    (one t u v ∧ one t u w ∧ one t v w) ↔
    (t = true ∧ u = false ∧ v = false ∧ w = false) := by
  cases t <;> cases u <;> cases v <;> cases w <;> decide

theorem clauseOutputs (x y l z a b c d : Bool) :
    (one z x a ∧ one z y b ∧ one a b c ∧ one z (!l) d) ↔
    ((x || y || l) = true ∧ z = (!x && !y) ∧ a = (!x && y) ∧
      b = (x && !y) ∧ c = (x == y) ∧ d = ((!z) && l)) := by
  cases x <;> cases y <;> cases l <;> cases z <;> cases a <;> cases b <;> cases c <;> cases d <;> decide

def reflected : Array Nat := ((List.range 16).map (fun i => i ^^^ (i / 2))).toArray

def omitted (edges : List Nat) : Nat := edges.foldl (fun acc i => acc ||| 2^i) 0

theorem physicalMasks :
    exactModels (tables reflected (omitted [2,3,6,7,14,15])) = 276 ∧
    exactModels (tables reflected (omitted [0,3,6,9,10,15])) = 32769 ∧
    exactModels (tables reflected (omitted [0,1,3,4,7,8])) = 4162 := by
  native_decide

abbrev dup (x twin y z : Bool) := x = twin ∧ one x y z

theorem pinTriangle (p a b c d u v s t : Bool) :
    (dup p a b c ∧ dup (!a) (!d) u v ∧ dup (!d) (!b) s t) ↔
    (p=false ∧ a=false ∧ b=false ∧ c=true ∧ d=false ∧
     u=false ∧ v=false ∧ s=false ∧ t=false) := by
  cases p <;> cases a <;> cases b <;> cases c <;> cases d <;> cases u <;>
    cases v <;> cases s <;> cases t <;> decide

end GrayCycleBankClosure
