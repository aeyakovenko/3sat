import CycleImageClock

namespace CycleImageQuadratic
open CycleImageClock

def imageWords : Array Nat :=
  #[9,7,19,3,25,29,5,31,14,12,23,11,18,26,13,27]

def coefficients : Array Nat :=
  #[9,14,26,30,16,10,6,0,7,12,3,0,12,0,0,0]

def degree (i : Nat) := ((List.range 4).filter (fun j => i.testBit j)).length

def polynomial (x : Nat) : Nat := (List.range 16).foldl
  (fun acc s => if (s &&& x) == s then acc ^^^ coefficients[s]! else acc) 0

theorem polynomial_table : ∀ x : Fin 16, polynomial x = imageWords[x.val]! := by decide +kernel

theorem quadratic : ∀ s : Fin 16, 2 < degree s → coefficients[s.val]! = 0 := by decide +kernel

theorem degree_two : degree 3 = 2 ∧ coefficients[3]! ≠ 0 := by decide +kernel

theorem preserves : ∀ x : Fin 16, cover 4 x = cover 5 (polynomial x) := by decide +kernel

theorem injective : ∀ x y : Fin 16, polynomial x = polynomial y → x = y := by decide +kernel

def parity (a : Nat) : Bool := (List.range 5).foldl (fun c j => c != a.testBit j) false

/-- The xor of all seven cover rows commutes with affine maps, because
    their number is odd. Both count and status of this xor survive injection. -/
def admissible (normal constant : Nat) : Bool := Id.run do
  let yes := (List.range 32).filter fun x =>
    (parity (x &&& normal) == (constant == 1)) && cover 5 x
  return yes.length == 7 && cover 5 (yes.foldl (· ^^^ ·) 0)

theorem source_centroid :
    let xs := (List.range 16).filter (cover 4)
    xs.length = 7 ∧ xs.foldl (· ^^^ ·) 0 = 15 ∧ cover 4 15 = true := by decide +kernel

theorem affine_planes : ∀ n : Fin 31, ∀ c : Fin 2,
    admissible (n.val+1) c.val =
       (c.val == 0 && [7,14,19,25,28].contains (n.val+1)) := by native_decide


/-- Upper programs for the surviving five normals after the two native
    loads x and y. Each executes at most three further instructions. -/
def affineUpper (normal bits : Nat) : Bool :=
  let x := bits % 8
  let y := bits / 8
  match normal with
  | 7 => ((((8-x)%8) &&& y) != 0)
  | 14 => ((x &&& y) != 0)
  | 19 => if (x ^^^ y) < x then x != y else x == 5
  | 25 => if x < y then x == 2 else decide (1 < x/y)
  | _ =>
      let sq := (x*x)%8
      if (sq ^^^ 4) < (x ^^^ 4) then decide (2 ≤ y) else decide (5 ≤ x)

theorem five_affine_uppers : ∀ n : Fin 32, ∀ x : Fin 32,
    [7,14,19,25,28].contains n.val = true → parity (x.val &&& n.val) = false →
      affineUpper n.val x.val = cover 5 x.val := by decide +kernel

/-- Complete five-bit catalog upper after two native loads, with at most
    four remaining instructions on either branch. -/
def sixUpper (bits : Nat) : Bool :=
  let x := bits % 8
  let y := bits / 8
  if x == y then decide (2 < x) else if y < 2 then (x &&& y) != 0
  else if x < y then x == 2 else decide (5 ≤ x)

theorem six_upper : ∀ x : Fin 32, sixUpper x.val = cover 5 x.val := by decide +kernel

@[inline] def splits (area goal c : UInt64) : Bool :=
  let h := area &&& c
  h == goal || h == (area ^^^ goal)

-- All possible nonconstant equality/unsigned-order/signed-order partitions
-- using either operand order, computed in parallel on 16 packed rows.
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
  for i in [:16] do
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
    out := out ||| (mem[j]! &&& (pick ||| (pick <<< 16) ||| (pick <<< 32)))
  return out

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
      for c in cuts do
        let l := area &&& c
        if l != 0 && l != area then
          if ← search constants target fuel l regs mem then
            if ← search constants target fuel (area ^^^ l) regs mem then return true
      let vs := constants ++ regs
      let mut results : Std.HashSet Col := {}
      for x in vs do results := results.insert (read3 mem x)
      for x in regs do for y in vs do
        for v in ← base (resultVals 3 x y) do results := results.insert v
        for v in ← base (resultVals 3 y x) do results := results.insert v
      for v in results.toArray do
        if !vs.contains v then
          if ← search constants target fuel area ((regs.push v).qsort (· < ·)) mem then return true
      for addr in vs do for val in vs do
        let m := writeMem 3 mem addr val
        if m != mem then if ← search constants target fuel area regs m then return true
      return false

    let answer ← worker
    modify fun c => {c with answers := c.answers.insert key answer}
    return answer

def atDepth (image : Array Nat) (fuel : Nat) (length : Nat := 5) : Bool := Id.run do
  let constants := (List.range 8).toArray.map fun k => encode 3 (fun _ => k)
  let mem := (List.range 8).toArray.map fun j => encode 3 (fun i => (image[i]! >>> (3*j)) % 8)
  let mut target : Cut := 0
  for i in [:16] do if cover length (image[i]!) then target := target ||| (1 <<< i.toUInt64)
  return ((search constants target fuel allRows #[] mem).run {}).1


def twoImage : Array Nat := #[8,16,1,2,9,31,0,13,25,10,22,30,18,15,29,27]
def threeImage : Array Nat := #[20,25,10,9,28,30,1,13,0,24,29,11,8,31,22,15]

/-- Swap coordinates 0 and 2 if coordinate 1 is set. -/
def twist (v : Nat) : Nat :=
  if v.testBit 1 && (v.testBit 0 != v.testBit 2) then v ^^^ 5 else v

theorem twist_spec : ∀ v : Fin 16, twist v < 16 ∧ twist (twist v) = v.val ∧
    cover 4 (twist v) = cover 4 v := by decide +kernel

/-- Ordered by desired exact worst-case clock 2,3,4,5,6. -/
def encoding (index input : Nat) : Nat :=
  match index with
  | 0 => twoImage[input]!
  | 1 => threeImage[input]!
  | 2 => insertBit (twist input) 1
  | 3 => insertBit (twist input) 0
  | _ => imageWords[input]!

def coefficient (index support : Nat) : Nat := (List.range 16).foldl
  (fun val x => if (x &&& support) == x then val ^^^ encoding index x else val) 0

theorem spectrum_maps : ∀ k : Fin 5,
    (∀ x : Fin 16, encoding k x < 32 ∧ cover 5 (encoding k x) = cover 4 x) ∧
    (∀ x y : Fin 16, encoding k x = encoding k y → x = y) ∧
    (∀ s : Fin 16, degree s > 2 → coefficient k s = 0) ∧
    ((List.range 16).any (fun s => degree s == 2 && coefficient k s != 0) = true) := by native_decide

theorem cheap_uppers : ∀ v : Fin 16,
    (decide (2 < twoImage[v.val]! % 8) = cover 4 v) ∧
    (((decide (4 < threeImage[v.val]! % 8)) || (threeImage[v.val]! % 8 == 3)) = cover 4 v) := by
  decide +kernel

def plane (n : Nat) : Array Nat :=
  ((List.range 32).filter (fun v => !(parity (n &&& v)))).toArray

theorem easy_plane_lower : atDepth (plane 14) 3 = false := by native_decide
theorem last_plane_lower : atDepth (plane 19) 4 = false := by native_decide

theorem two_lower : atDepth twoImage 1 = false := by native_decide
theorem three_lower : atDepth threeImage 2 = false := by native_decide


end CycleImageQuadratic
