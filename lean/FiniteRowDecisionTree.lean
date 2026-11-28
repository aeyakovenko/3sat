import Std

namespace FiniteRowDecisionTree

inductive Tree (Q : Type u) where
  | leaf (label : Bool)
  | split (query : Q) (orientation : Bool) (yes no : Tree Q)

def Tree.height : Tree Q → Nat
  | .leaf _ => 0
  | .split _ _ yes no => 1 + max yes.height no.height

def Tree.run (test : Q → A → Bool) (input : A) : Tree Q → Bool
  | .leaf label => label
  | .split q orientation yes no =>
    if test q input == orientation then yes.run test input else no.run test input

/-- For any two distinct verdicts it suffices that one admissible Boolean
    probe distinguishes the two rows. The code tree is chosen separately for
    the supplied finite list of possible rows. -/
theorem finite_image (label : A → Bool) (test : Q → A → Bool)
    (separates : ∀ a b, label a ≠ label b → ∃ q, test q a ≠ test q b)
    (rows : List A) :
    ∃ t : Tree Q, t.height ≤ rows.length - 1 ∧
      ∀ v ∈ rows, t.run test v = label v := by
  classical
  by_cases mixed : ∃ a ∈ rows, ∃ b ∈ rows, label a ≠ label b
  · obtain ⟨a,ha,b,hb,hab⟩ := mixed
    obtain ⟨q,hq⟩ := separates a b hab
    let p := fun v => test q v == test q a
    have pa : p a = true := by simp [p]
    have pb : p b = false := by simp [p, Ne.symm hq]
    have left_lt : (rows.filter p).length < rows.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨b,hb,by simp [pb]⟩
    have right_lt : (rows.filter fun v => !(p v)).length < rows.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨a,ha,by simp [pa]⟩
    have left_pos : 0 < (rows.filter p).length :=
      List.length_pos_iff_exists_mem.mpr ⟨a, List.mem_filter.mpr ⟨ha,pa⟩⟩
    have right_pos : 0 < (rows.filter fun v => !(p v)).length :=
      List.length_pos_iff_exists_mem.mpr ⟨b, List.mem_filter.mpr ⟨hb,by simp [pb]⟩⟩
    obtain ⟨yes,hyh,hyr⟩ := finite_image label test separates (rows.filter p)
    obtain ⟨no,hnh,hnr⟩ := finite_image label test separates
      (rows.filter (fun v => !(p v)))
    refine ⟨.split q (test q a) yes no, ?_, ?_⟩
    · simp only [Tree.height]
      omega
    · intro v hv
      cases e : p v with
      | false =>
        have h := hnr v (List.mem_filter.mpr ⟨hv,by simp [e]⟩)
        simpa [Tree.run, ← show p v = (test q v == test q a) from rfl, e] using h
      | true =>
        have h := hyr v (List.mem_filter.mpr ⟨hv,e⟩)
        simpa [Tree.run, ← show p v = (test q v == test q a) from rfl, e] using h
  · cases rows with
    | nil => exact ⟨.leaf false, Nat.zero_le _, by simp⟩
    | cons a tail =>
      refine ⟨.leaf (label a), Nat.zero_le _, ?_⟩
      intro v hv
      apply Classical.byContradiction
      intro h
      exact mixed ⟨a, by simp, v, hv, h⟩
termination_by rows.length
decreasing_by
  first | exact left_lt | exact right_lt
  first | exact left_lt | exact right_lt

end FiniteRowDecisionTree
