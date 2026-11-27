import Std

namespace StackVisit

/-- A block schedule built from waits, consecutive phases, and nested pushes.
    In a matching phase, the order-preserving pairing becomes nested when the
    second side is read in reverse. -/
inductive Schedule where
  | empty
  | waitHere
  | append (first second : Schedule)
  | pushPop (inside : Schedule)

/-- A push occupies its base slot and moves up. The matching pop returns to
    that base only after all slots of the nested schedule. -/
def slots : Schedule → Nat → List Nat
  | .empty, _ => []
  | .waitHere, base => [base, base]
  | .append first second, base => slots first base ++ slots second base
  | .pushPop inside, base =>
      [base, base+1] ++ slots inside (base+1) ++ [base+1, base]

theorem above_base (s : Schedule) (base pos : Nat) (seen : pos ∈ slots s base) :
    base ≤ pos := by
  induction s generalizing base with
  | empty => simp [slots] at seen
  | waitHere =>
    simp [slots] at seen
    omega
  | append first second ih₁ ih₂ =>
    simp only [slots, List.mem_append] at seen
    rcases seen with h | h
    · exact ih₁ base h
    · exact ih₂ base h
  | pushPop inside ih =>
    simp only [slots, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at seen
    rcases seen with ((h | h) | h) | (h | h)
    · omega
    · omega
    · have hb := ih (base+1) h
      omega
    · omega
    · omega

/-- An edge joining the endpoint slots is present in the consecutive-visit
    graph. Surrounding slots outside this segment cannot remove that edge. -/
theorem direct_visit (inside : Schedule) (base : Nat) :
    ∃ middle : List Nat,
      slots (.pushPop inside) base = base :: (middle ++ [base]) ∧ base ∉ middle := by
  refine ⟨[base+1] ++ slots inside (base+1) ++ [base+1], ?_, ?_⟩
  · simp [slots, List.append_assoc]
  · intro h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with (bad | hit) | bad
    · omega
    · have impossible := above_base inside (base+1) base hit
      omega
    · omega

end StackVisit
