import Std

namespace FourCubicEdits

/-- The assignment is a six-bit integer in lexicographic edge order. -/
def edgeBit (x e : Nat) : Nat := (x / 2^e) % 2

def incident : List (List Nat) := [[0,1,2], [0,3,4], [1,3,5], [2,4,5]]

def pattern (x v : Nat) : Nat :=
  (incident[v]!).zipIdx.foldl (fun acc p => acc + edgeBit x p.1 * 2^p.2) 0

/-- The four local forbidden rows at each vertex after the single sign edit. -/
def groups : List (List Nat) :=
  [[1,3,5,6], [0,2,4,7], [1,2,5,7], [1,2,6,7]]

def rows : List (Nat × Nat) :=
  groups.zipIdx.flatMap (fun p => p.1.map (Prod.mk p.2))

def passes (x : Nat) (clauses : List (Nat × Nat)) : Bool :=
  clauses.all (fun row => pattern x row.1 != row.2)

theorem four_edits_unsatisfiable : (List.range 64).any (fun x => passes x rows) = false := by
  decide +kernel

/-- Position j of this list gives a satisfying assignment with clause j removed. -/
def witnesses : List Nat := [1,11,21,30,0,10,20,31,23,28,39,47,15,26,56,60]

theorem all_clauses_essential :
    (List.range rows.length).all
      (fun j => witnesses[j]! < 64 && passes witnesses[j]! (rows.eraseIdx j)) = true := by
  decide +kernel

/-- The triangle case cannot have opposite excluded edge values at both of
    u's internal ports if its edit changes only one literal. -/
theorem triangle_conflict {leftA rightA leftB rightB fromLeft fromRight : Bool}
    (leftMatch : fromLeft = leftB) (rightMatch : fromRight = rightB)
    (leftApart : leftA ≠ fromLeft) (rightApart : rightA ≠ fromRight)
    (oneChange : leftA = leftB ∨ rightA = rightB) : False := by
  rcases oneChange with h | h
  · exact leftApart (h.trans leftMatch.symm)
  · exact rightApart (h.trans rightMatch.symm)

end FourCubicEdits
