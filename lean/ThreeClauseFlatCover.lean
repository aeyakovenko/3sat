import Std

namespace ThreeClauseFlatCover

/-- A mask in {1,...,7} represents a nonzero vector in the binary three-cube. -/
def dot (a x : Nat) : Bool :=
  ((a.testBit 0 && x.testBit 0) ^^ (a.testBit 1 && x.testBit 1)) ^^
    (a.testBit 2 && x.testBit 2)

abbrev Box := Nat × Nat × Nat

def boxes : List Box :=
  [(1,6,6), (2,7,7), (6,5,3), (5,6,7), (2,5,2), (5,4,6),
   (1,3,4), (3,3,3), (4,2,1), (7,1,5), (6,7,2), (3,4,4)]

def contains (b : Box) (x y z : Fin 7) : Bool :=
  dot b.1 (x.val + 1) && dot b.2.1 (y.val + 1) && dot b.2.2 (z.val + 1)

theorem twelve_boxes : boxes.length = 12 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
/-- Each of the 343 nonzero-triple words lies in one of these twelve product flats. -/
theorem cover : ∀ x y z : Fin 7, boxes.any (fun b => contains b x y z) = true := by decide

end ThreeClauseFlatCover
