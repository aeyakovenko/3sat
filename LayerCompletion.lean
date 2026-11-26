import Std

/-! Finite four-port completion lemma for the two-path coloring gadget. A suffix
is a list of four-bit site masks. Its relation is computed by coloring the selected
vertices of one layer and passing the resulting four endpoints to the next layer. -/
namespace LayerCompletion

abbrev Mask := Fin 16

private def representatives : List (List Nat) := [
  [0,0,0,0], [0,0,0,1], [0,0,1,0], [0,0,1,1], [0,0,1,2], [0,1,0,0],
  [0,1,0,1], [0,1,0,2], [0,1,1,0], [0,1,1,1], [0,1,1,2], [0,1,2,0],
  [0,1,2,1], [0,1,2,2]]

private def typeIndex (row : List Nat) : Nat :=
  representatives.idxOf (row.map row.eraseDups.idxOf)

private def pathsProper : List Nat → Bool
  | a :: (b :: rest) => a != b && pathsProper (b :: rest)
  | _ => true

private def siteColors (mask colors : Nat) (sites : List Nat) : List Nat :=
  (sites.filter mask.testBit).map fun j => (colors / 3^j) % 3

private def allowed (mask : Nat) (row : List Nat) : Nat :=
  let x := row[0]!
  let u := row[1]!
  let v := row[2]!
  let h := row[3]!
  (List.range 81).foldl (fun bits colors =>
    let red := x :: siteColors mask colors [0,1,2,3]
    let left := u :: siteColors mask colors [2,0]
    let right := siteColors mask colors [3] ++ [v]
    let front := siteColors mask colors [1] ++ [h]
    if [red,left,right,front].all pathsProper then
      let ports := [red.getLast!,left.getLast!,right.head!,front.head!]
      bits ||| (2 ^ typeIndex ports)
    else bits) 0

private def transfers : List (List Nat) :=
  (List.range 16).map fun mask => representatives.map (allowed mask)

def prepend (m : Mask) (suffix : Nat) : Nat :=
  ((transfers[m.val]!).zipIdx.map fun (targets, i) =>
    if targets &&& suffix == 0 then 0 else 2^i).sum

def emptySuffix : Nat :=
  (representatives.zipIdx.map fun (s,i) => if s[1]! != s[2]! then 2^i else 0).sum

def relation : List Mask → Nat
  | [] => emptySuffix
  | m :: rest => prepend m (relation rest)

def eligible (r : Nat) : Bool := !r.testBit 1 && r.testBit 5

def known : List Nat := [
  0,879,2047,7039,8191,11247,12287,14588,15359,15838,15866,15868,16063,16119,
  16311,16367,16375,16376,16378,16380,16382,16383]

private theorem finite_closure :
    known.all (fun r => (List.finRange 16).all (fun m => known.contains (prepend m r))) = true := by
  native_decide

private theorem every_sixteen : ∀ (i : Fin 16), i ∈ List.finRange 16 := by decide
private theorem every_four : ∀ (i : Fin 4), i ∈ List.finRange 4 := by decide

theorem relation_mem (masks : List Mask) : relation masks ∈ known := by
  induction masks with
  | nil => native_decide
  | cons m rest ih =>
    apply List.contains_iff_mem.mp
    exact List.all_eq_true.mp (List.all_eq_true.mp finite_closure _ ih) _ (every_sixteen m)

def almost (i : Fin 4) : Mask := ⟨15 - 2^i.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

private theorem finite_completion :
    known.all (fun r => (List.finRange 4).all fun i =>
      !(eligible (prepend 15 r) && eligible (prepend (almost i) r)) || i.val == 1) = true := by
  native_decide

/-- For an arbitrary suffix of partial layers, only a final insertion of b
can leave both adjacent phases negative with their inherited repair coloring. -/
theorem last_site (suffix : List Mask) (i : Fin 4)
    (before : eligible (relation (almost i :: suffix)) = true)
    (after : eligible (relation (15 :: suffix)) = true) : i.val = 1 := by
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp finite_completion _ (relation_mem suffix)) i (every_four i)
  change eligible (prepend (almost i) (relation suffix)) = true at before
  change eligible (prepend 15 (relation suffix)) = true at after
  simpa [before, after] using h

end LayerCompletion
