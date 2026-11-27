import Std

namespace LocalFourPortOrientation

private def block : List (Nat × Nat) :=
  [(0,1),(0,4),(0,6),(0,9),(1,2),(1,5),(1,7),(2,6),(2,8),(3,4),(3,7),
   (4,5),(4,8),(5,10),(5,11),(6,10),(6,11),(7,8),(7,11),(8,10),(9,11)]

private def secondName (v : Nat) : Nat := if v = 3 then 9 else 12 + v

private def edges := block ++ block.map (fun (u,v) => (secondName u, secondName v))

/-- All possible incoming/outgoing external counts for a two-slot terminal. -/
private def profiles : List (Nat × Nat) := [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0)]

/-- One bit per edge selects the second endpoint as head. -/
private def masks : List (List Nat) :=
  [[2846582074538,686200941738,2043754540202,2846582074538,2846582074538,2703056515884],
   [2846582189466,686201056666,2043754655130,2846582189466,2846582189466,2703056645530],
   [2837455405525,2703036350933,1961410003413,2845495886293,2837455405525,2703056634188],
   [2846582603434,686201470634,2043755069098,2846582603434,2846582603434,2703056515884],
   [2846582074538,686200941738,2043754540202,2846582074538,2846582074538,2703056515884],
   [2086995816236,2086995816236,2086976941868,2086995816236,2086995816236,3639119113829]]

private def checkPair (i j : Nat) : Bool :=
  let mask := ((masks.getD i []).getD j 0)
  let heads := edges.zipIdx.map (fun ((u,v),k) => if mask.testBit k then v else u)
  let tails := edges.zipIdx.map (fun ((u,v),k) => if mask.testBit k then u else v)
  (List.range 24).all fun v =>
    let ext := if v = 3 then profiles.getD i (0,0) else
               if v = 21 then profiles.getD j (0,0) else (0,0)
    let a := heads.count v + ext.1
    let b := tails.count v + ext.2
    decide (a ≤ b + 1 ∧ b ≤ a + 1 ∧ a + b ≤ 4)

/-- Check the actual assigned heads, for every pair of terminal profiles. -/
theorem orientation_table :
    (List.range 6).all (fun i => (List.range 6).all (checkPair i)) = true := by decide +kernel

/-- No possible terminal profile is missing. -/
theorem profile_coverage (a b : Nat) (h : a+b ≤ 2) : (a,b) ∈ profiles := by
  simp [profiles]
  omega

end LocalFourPortOrientation
