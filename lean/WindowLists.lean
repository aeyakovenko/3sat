import Std

namespace WindowLists

/-- A short verified list is recovered from d alone. -/
theorem sound_list_code {m j b d tag gamma : Nat} (offsetOK : d ≤ b)
    (fits : b ≤ j) (room : j ≤ m) (save : tag + gamma + 1 < d) :
    tag + gamma + (b-d) + (j-b+1) + (m-j) < m := by omega

/-- Payload prefix length after a previously consumed halting program. -/
theorem tail_code {m j b d tag gamma program : Nat} (offsetOK : program+d ≤ b)
    (fits : b ≤ j) (room : j ≤ m) (save : tag + gamma + 1 < d) :
    tag + gamma + program + (b-program-d) + (j-b+1) + (m-j) < m := by omega

theorem lifted_name {newLen oldLen j h d code tag gamma program : Nat}
    (short : program < oldLen) (format : j ≤ oldLen)
    (room : oldLen+h ≤ newLen) (fields : code+d ≤ h) (paid : tag+gamma ≤ d) :
    tag+gamma+code+program+(h-code-d)+(newLen-(j+h)-(oldLen-j)) < newLen := by omega

/-- Descendants sent to different suffix-code cells cannot overlap.
    This is the concatenation fact used when charging the convolution. -/
theorem distinct_suffixes {tags : List Bool → Prop}
    (suffixFree : ∀ a b, tags a → tags b → a <:+ b → a = b)
    {p q a b : List Bool} (ha : tags a) (hb : tags b)
    (overlap : p++a = q++b) : a = b := by
  rcases List.append_eq_append_iff.mp overlap with
    ⟨w, _, tail⟩ | ⟨w, _, tail⟩
  · exact (suffixFree _ _ hb ha ⟨w,tail.symm⟩).symm
  · exact suffixFree _ _ ha hb ⟨w,tail.symm⟩

/-- At a common dyadic denominator, a failed mask charges its entire size
    to true bad indices.  Successful stages have a separate budget. -/
theorem split_cost (offered failed successful : List Nat)
    (partition : offered.sum = failed.sum + successful.sum)
    {badBudget goodBudget : Nat}
    (bad : failed.sum ≤ badBudget) (good : successful.sum ≤ goodBudget) :
    offered.sum ≤ badBudget + goodBudget := by omega

def charge (depth : Nat) (stages : List (Nat × Nat)) : Nat :=
  (stages.map (fun entry => entry.2 * 2^(depth-entry.1))).sum

/-- Earlier, coarser dyadic requests finish on the current grid.  Each
    pair specifies a prefix length and the number of requests there. -/
theorem earlier_aligned {depth level : Nat} (stages : List (Nat × Nat))
    (fits : level ≤ depth) (order : ∀ t ∈ stages, t.1 ≤ level) :
    ∃ q, charge depth stages = q * 2^(depth-level) := by
  induction stages with
  | nil => exact ⟨0, by simp [charge]⟩
  | cons t ts ih =>
    have ht := order t (by simp)
    obtain ⟨q,hq⟩ := ih (fun u hu => order u (by simp [hu]))
    have exp : depth-t.1 = level-t.1 + (depth-level) := by omega
    refine ⟨t.2*2^(level-t.1) + q, ?_⟩
    change t.2*2^(depth-t.1) + charge depth ts = _
    rw [exp, Nat.pow_add, hq, Nat.add_mul, Nat.mul_assoc]

/-- Every requested member gets an aligned complete cell before the end
    of the binary code space whenever this finite prefix fits its budget. -/
theorem allocate_stage {depth level count : Nat} (stages : List (Nat × Nat))
    (fits : level ≤ depth) (order : ∀ t ∈ stages, t.1 ≤ level)
    (budget : charge depth stages + count*2^(depth-level) ≤ 2^depth) :
    ∃ start, charge depth stages = start * 2^(depth-level) ∧
      ∀ i < count, start+i < 2^level := by
  obtain ⟨start,hstart⟩ := earlier_aligned stages fits order
  refine ⟨start,hstart,?_⟩
  rw [hstart, ← Nat.add_mul] at budget
  have d : 2^depth = 2^level * 2^(depth-level) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [d] at budget
  have pos : 0 < 2^(depth-level) := Nat.two_pow_pos _
  have enough := Nat.le_of_mul_le_mul_right budget pos
  intro i hi
  omega

end WindowLists
