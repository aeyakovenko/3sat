import Std

namespace TernaryDensityGapAtFiveEdits

/-- An edge is a bit mask. The vertices are numbered consecutively from zero. -/
structure Graph where
  vertices : Nat
  edges : List Nat
  deriving Repr

private def names (mask n : Nat) := (List.range n).filter (fun i => mask.testBit i)

/-- Every next edge must meet the union of its predecessors. Choose any nonempty
subset of old names of size at most three and number fresh names consecutively
in order of appearance. The construction keeps all ordered histories. -/
def extensions (g : Graph) : List Graph := Id.run do
  let mut next := []
  for old in [1:2^g.vertices] do
    let count := (names old g.vertices).length
    if count ≤ 3 then
      let fresh := 3 - count
      let edge := old ||| (((2^fresh - 1) <<< g.vertices))
      if !g.edges.contains edge then
        next := ⟨g.vertices + fresh, (edge :: g.edges).mergeSort⟩ :: next
  return next

/-- The root fixes the three names on the first edge. -/
def histories : Nat → List Graph
  | 0 => []
  | 1 => [⟨3, [7]⟩]
  | k+2 => (histories (k+1)).flatMap extensions

private abbrev Cache := Std.HashMap (Nat × List Nat) Nat

/-- Numerator of the optimal exposure bound with denominator 14^fuel. Fixing
a tested vertex deletes it from the live names on both branches. Vacuous
names may remain in fuel, and are paid for by the terminal power of 14. -/
private def score (fuel : Nat) (rows : List Nat) : StateM Cache Nat := do
  if rows.isEmpty then return 14^fuel
  if rows.contains 0 then return 0
  match fuel with
  | 0 => return 0  -- unreachable for the histories above or their residuals
  | k+1 =>
    let key := (k+1, rows)
    if let some value := (← get).get? key then return value
    let used := rows.foldl (· ||| ·) 0
    let mut best := 15^(k+1)
    for v in names used (used.log2+1) do
      let bit := 2^v
      let discard := rows.filter (fun e => !(e.testBit v))
      let shorten := ((rows.map (fun e => e - (e &&& bit))).mergeSort).eraseDups
      let left ← score k discard
      let right ← score k shorten
      best := min best (8*left + 7*right)
    modify (·.insert key best)
    return best

private def oneHit (g : Graph) : Bool :=
  (List.range g.vertices).any (fun u => g.edges.all (fun e => e.testBit u))

private def twoHit (g : Graph) : Bool :=
  (List.range g.vertices).any (fun u =>
    (List.range g.vertices).any (fun v =>
      g.edges.all (fun e => e.testBit u || e.testBit v)))

/-- The normalization to denominator 343 is exact on the two high values.
The other entries impose only upper bounds. -/
private def accepted (k : Nat) (g : Graph) (s : Nat) : Bool :=
  let den := 14^g.vertices
  let scaled := 343*s
  match k with
  | 1 => scaled == 343*den && twoHit g
  | 2 => scaled == 322*den && oneHit g && g.vertices ≤ 5
  | 3 => (scaled == 322*den && twoHit g && !oneHit g && g.vertices ≤ 6) || scaled ≤ 316*den
  | 4 => scaled ≤ 316*den
  | _ => false

private def census (k : Nat) : Nat × Nat × Bool := Id.run do
  let gs := histories k
  let report : StateM Cache (Nat × Bool) := do
    let mut high := 0
    let mut passed := true
    for g in gs do
      let s ← score g.vertices g.edges
      if 100*s ≥ 93*14^g.vertices then high := high+1
      passed := passed && accepted k g s
    return (high, passed)
  let (high, passed) := report.run' {}
  return (gs.length, high, passed)

/-- The gap (316/343, 46/49) straddles 320/343. Every surviving ordered
history has at most three edges and admits a transversal of size at most
two. All four-edge connected extensions are tested, including extensions of
three-edge histories whose score already fell below the cutoff. -/
theorem connected_census :
    census 1 = (1, 1, true) ∧
    census 2 = (6, 6, true) ∧
    census 3 = (105, 27, true) ∧
    census 4 = (3486, 0, true) := by
  native_decide

end TernaryDensityGapAtFiveEdits
