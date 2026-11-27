import Std

/-! Integer certificates for the 18-position adjacent time-cut packing.
All weights and pair masses are scaled by three. -/
namespace TimeCutPacking

def packing : List (Nat × Nat × Nat × Nat) := [
  (0, 1, 2, 3),
  (0, 2, 4, 3),
  (2, 3, 4, 3),
  (3, 4, 5, 1),
  (0, 4, 8, 2),
  (4, 5, 6, 2),
  (0, 5, 10, 1),
  (5, 6, 7, 1),
  (4, 6, 8, 2),
  (6, 7, 8, 2),
  (5, 7, 9, 1),
  (7, 8, 9, 1),
  (6, 8, 10, 1),
  (0, 8, 16, 1),
  (16, 17, 18, 3),
  (14, 16, 18, 3),
  (14, 15, 16, 3),
  (13, 14, 15, 1),
  (10, 14, 18, 2),
  (12, 13, 14, 2),
  (8, 13, 18, 1),
  (11, 12, 13, 1),
  (10, 12, 14, 2),
  (10, 11, 12, 2),
  (9, 11, 13, 1),
  (9, 10, 11, 1),
  (8, 10, 12, 1),
  (2, 10, 18, 1),
  (8, 9, 10, 2),
  (0, 9, 18, 1)
]

def dual : List (Nat × Nat × Nat) := [
  (0, 1, 3),
  (0, 6, 1),
  (0, 9, 1),
  (1, 2, 3),
  (1, 3, 3),
  (2, 3, 3),
  (2, 5, 3),
  (2, 7, 2),
  (2, 10, 1),
  (3, 4, 3),
  (3, 6, 3),
  (4, 5, 3),
  (4, 7, 1),
  (4, 9, 1),
  (4, 10, 3),
  (5, 6, 3),
  (5, 7, 2),
  (5, 12, 5),
  (6, 7, 3),
  (6, 8, 1),
  (6, 9, 1),
  (6, 13, 2),
  (7, 8, 3),
  (7, 9, 1),
  (7, 10, 3),
  (7, 14, 2),
  (8, 9, 3),
  (8, 11, 2),
  (8, 13, 1),
  (8, 15, 1),
  (9, 10, 3),
  (9, 11, 1),
  (10, 11, 3),
  (10, 12, 2),
  (10, 14, 1),
  (10, 15, 2),
  (11, 12, 3),
  (11, 13, 1),
  (11, 14, 2),
  (11, 15, 1),
  (12, 13, 3),
  (12, 15, 3),
  (13, 14, 3),
  (14, 15, 3),
  (14, 16, 3),
  (15, 16, 3),
  (16, 17, 3)
]

def pairLoad (i j : Nat) : Nat :=
  (packing.map fun (l, c, r, w) => if l ≤ i ∧ i < c ∧ c ≤ j ∧ j < r then w else 0).sum

def rectangleMass (l c r : Nat) : Nat :=
  (dual.map fun (i, j, w) => if l ≤ i ∧ i < c ∧ c ≤ j ∧ j < r then w else 0).sum

/-- Every primal rectangle consists of two adjacent nonempty intervals. -/
theorem packing_valid :
    packing.all (fun (l, c, r, _) => decide (l < c ∧ c < r ∧ r ≤ 18)) = true := by
  decide

/-- Every nonzero dual mass belongs to a valid ordered pair. -/
theorem dual_valid :
    dual.all (fun (i, j, _) => decide (i < j ∧ j < 18)) = true := by
  decide

/-- Dividing the primal weights by three gives congestion at most one. -/
theorem pair_load : ∀ i j : Fin 18, i < j → pairLoad i.val j.val ≤ 3 := by
  decide

/-- This checks all adjacent rectangles, including unequal interval lengths. -/
theorem rectangle_mass : ∀ l c r : Fin 19, l < c → c < r →
    3 * min (c.val - l.val) (r.val - c.val) ≤ rectangleMass l.val c.val r.val := by
  decide

/-- The feasible primal and dual certificates have the same scaled objective. -/
theorem objectives :
    (packing.map (fun (l, c, r, w) => min (c-l) (r-c) * w)).sum = 107 ∧
      (dual.map (fun (_, _, w) => w)).sum = 107 := by
  decide

#print axioms packing_valid
#print axioms dual_valid
#print axioms pair_load
#print axioms rectangle_mass
#print axioms objectives

end TimeCutPacking
