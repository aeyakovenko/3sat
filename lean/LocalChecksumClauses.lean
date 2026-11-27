import Std

namespace LocalChecksumClauses

structure Literal where
  variableId : Nat
  value : Bool

def satisfies (x : Nat → Bool) (lit : Literal) : Prop := x lit.variableId = lit.value

def flipped (x : Nat → Bool) (slot : Nat) (i : Nat) : Bool :=
  if i = slot then !(x i) else x i

/-- At a true assignment a fixed disjunctive clause cannot be falsified
by flipping either of two distinct coordinates. The number of literals
and their possible repetitions are unrestricted. -/
theorem unique_critical_coordinate (clause : List Literal) (x : Nat → Bool) (i j : Nat)
    (true_at : ∃ l ∈ clause, satisfies x l)
    (fail_i : ∀ l ∈ clause, ¬satisfies (flipped x i) l)
    (fail_j : ∀ l ∈ clause, ¬satisfies (flipped x j) l) : i = j := by
  obtain ⟨l, mem, val⟩ := true_at
  have same (a : Nat) (fail : ∀ u ∈ clause, ¬satisfies (flipped x a) u) :
      l.variableId = a := by
    by_cases eq : l.variableId = a
    · exact eq
    · have unchanged : satisfies (flipped x a) l := by
        simpa [satisfies, flipped, eq] using val
      exact False.elim ((fail l mem) unchanged)
  exact (same i fail_i).symm.trans (same j fail_j)

/-- Counts of length-s products in a finite group omitting its identity.
Given the previous product, each nonidentity value has precisely one
allowed multiplier that returns it to the identity. This recurrence
checks its immediate integer consequence for the deviation from uniform. -/
theorem count_deviation (groupSize total hits : Int)
    (nextTotal nextHits : Int)
    (stepTotal : nextTotal = (groupSize - 1) * total)
    (stepHits : nextHits = total - hits) :
    groupSize * nextHits - nextTotal = -(groupSize * hits - total) := by
  rw [stepTotal, stepHits]
  simp only [Int.mul_sub, Int.sub_mul, Int.one_mul]
  omega

end LocalChecksumClauses
