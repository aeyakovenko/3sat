import Std

namespace FourSharedGuardBoxes

/-- Literal 2v+s uses variable v. The two parities give complementary signs. -/
private structure Row where
  a : Nat
  b : Nat
  c : Nat
  deriving Inhabited

private def entries (r : Row) : List Nat := [r.a, r.b, r.c]
private def contradict (s t : Row) : Bool :=
  (entries s).any fun l => (entries t).contains (l ^^^ 1)

private def signs (v old : Nat) : List Nat := if v < old then [2*v, 2*v+1] else [2*v]

/-- Enumerate increasing variable triples. Old variable names are below n.
    At least one must be old (the box must conflict with all earlier boxes).
    New variable names are taken consecutively in order of first use, and
    their first signs may be taken positive by global polarity symmetry. -/
private def extensions (prev : List Row) (n : Nat) : List (Row × Nat) := Id.run do
  let mut rows := []
  for x in [:n] do
    for y in [x+1:n+1] do
      for z in [y+1:(max n (y+1))+1] do
        for a in signs x n do
          for b in signs y n do
            for c in signs z n do
              let r : Row := ⟨a,b,c⟩
              if prev.all (contradict r) then
                rows := (r, max n (z+1)) :: rows
  return rows

/-- With the guard false, an inactive box must satisfy one of the two shared
    literals of the new clause. They negate the other two pins of its active box. -/
private def admits (r : Row) (others : List Row) : Bool :=
  (entries r).any fun change => others.all fun s =>
    (entries r).any fun l => l != change && (entries s).contains (l ^^^ 1)

private def roles (a b c d : Row) : Bool :=
  admits a [b,c,d] && admits b [a,c,d] && admits c [a,b,d] && admits d [a,b,c]

/-- A single clause true throughout each free box must contain one pin per box.\n    Their union has at most three literals and has consistent signs. -/
private def supports (a b c d : Row) : List Nat := Id.run do
  let mut result := []
  for i in entries a do
    for j in entries b do
      for k in entries c do
        for l in entries d do
          let hits := [i,j,k,l].eraseDups
          if hits.length ≤ 3 && hits.all (fun p => !(hits.contains (p ^^^ 1))) then
            let mask := hits.foldl (fun m p => m ||| (1 <<< (p/2))) 0
            if !result.contains mask then result := mask :: result
  return result

private def hasPair (n : Nat) (s : List Nat) : Bool := Id.run do
  for i in [:n] do
    for j in [i+1:n] do
      if s.all (fun m => m.testBit i || m.testBit j) then return true
  return false

def census : Nat × Nat × Nat × Nat := Id.run do
  let a : Row := ⟨0,2,4⟩
  let mut total := 0
  let mut eligible := 0
  let mut failures := 0
  let mut rawFailures := 0
  for (b,nb) in extensions [a] 3 do
    for (c,nc) in extensions [a,b] nb do
      for (d,nd) in extensions [a,b,c] nc do
        total := total+1
        let pair := hasPair nd (supports a b c d)
        if !pair then rawFailures := rawFailures+1
        if roles a b c d then
          eligible := eligible+1
          if !pair then failures := failures+1
  return (total, eligible, failures, rawFailures)

theorem shared_guard_census : census = (9039,4980,0,72) := by native_decide

/-- Independent, variable-arity enumeration of the signed pin subsets. -/
private def allHits : List Row → List (List Nat)
  | [] => [[]]
  | row :: rest => (allHits rest).flatMap fun tail => (entries row).map (fun l => l :: tail)

private def pinClauses (rows : List Row) : List (List Nat) := Id.run do
  let mut out := []
  for selected in allHits rows do
    let hits := selected.eraseDups
    if hits.length ≤ 3 && hits.all (fun p => !(hits.contains (p ^^^ 1))) then
      out := hits :: out
  return out

private def projection (hit : List Nat) : Nat :=
  hit.foldl (fun m p => m ||| (1 <<< (p/2))) 0

/-- A fifth geometrically disjoint box cannot remove a transversal that
    already meets all common clauses. Only the 72 raw exceptions require
    inspecting extensions. This check imposes no choice of edited literal. -/
def fiveCensus : Nat × Nat × Nat × Nat := Id.run do
  let a : Row := ⟨0,2,4⟩
  let mut rawExceptions := 0
  let mut withShort := 0
  let mut tested := 0
  let mut failed := 0
  for (b,nb) in extensions [a] 3 do
    for (c,nc) in extensions [a,b] nb do
      for (d,nd) in extensions [a,b,c] nc do
        if !(hasPair nd (supports a b c d)) then
          rawExceptions := rawExceptions+1
          if (pinClauses [a,b,c,d]).any (fun c => c.length ≤ 2) then
            withShort := withShort+1
          for (e,ne) in extensions [a,b,c,d] nd do
            tested := tested+1
            let signs := pinClauses [a,b,c,d,e]
            if !(hasPair ne (signs.map projection)) then failed := failed+1
  return (rawExceptions, withShort, tested, failed)

theorem five_boxes_have_a_pair : fiveCensus = (72, 0, 720, 0) := by native_decide

end FourSharedGuardBoxes
