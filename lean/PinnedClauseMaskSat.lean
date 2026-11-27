import Std

namespace PinnedClauseMaskSat

abbrev Mask := BitVec 3

/-- Bit i of the mask negates the literal on variable i. -/
def rowValue (mask assignment : Mask) : Bool :=
  (assignment.getLsbD 0 ^^ mask.getLsbD 0) ||
  (assignment.getLsbD 1 ^^ mask.getLsbD 1) ||
  (assignment.getLsbD 2 ^^ mask.getLsbD 2)

theorem false_iff_matches : ∀ m a : Mask, rowValue m a = false ↔ a = m := by decide

def pins : List Mask := [1, 2, 3, 4, 5, 6, 7]

theorem pins_are_all_nonzero :
    pins.length = 7 ∧ pins.Nodup ∧ ∀ m : Mask, m ∈ pins ↔ m ≠ 0 := by decide

def satisfies (rows : List Mask) (a : Mask) : Bool :=
  rows.all (fun m => rowValue m a)

theorem pins_force_zero : ∀ a : Mask, satisfies pins a = true ↔ a = 0 := by decide

def good (rows : List Mask) : Bool := rows.all (fun m => m != 0)

theorem good_iff (rows : List Mask) : good rows = true ↔ ∀ m ∈ rows, m ≠ 0 := by
  simp [good, List.all_eq_true]

theorem row_at_zero : ∀ m : Mask, rowValue m 0 = (m != 0) := by decide

/-- Exact witness characterization for all additional rows, including repetitions. -/
theorem pinned_model_iff (rows : List Mask) (a : Mask) :
    satisfies (pins ++ rows) a = true ↔ a = 0 ∧ good rows = true := by
  change (pins ++ rows).all _ = true ↔ _
  rw [List.all_append, Bool.and_eq_true]
  change satisfies pins a = true ∧ satisfies rows a = true ↔ _
  rw [pins_force_zero]
  have same : satisfies rows 0 = good rows := by
    simp only [satisfies,good,row_at_zero]
  constructor
  · rintro ⟨rfl,hr⟩
    exact ⟨rfl, same.symm.trans hr⟩
  · rintro ⟨rfl,hr⟩
    exact ⟨rfl, same.trans hr⟩

theorem sat_iff_no_zero_row (rows : List Mask) :
    (∃ a, satisfies (pins ++ rows) a = true) ↔ ∀ m ∈ rows, m ≠ 0 := by
  constructor
  · rintro ⟨a,ha⟩
    exact (good_iff rows).mp ((pinned_model_iff rows a).mp ha).2
  · intro h
    exact ⟨0, (pinned_model_iff rows 0).mpr ⟨rfl,(good_iff rows).mpr h⟩⟩

theorem unique_model_when_sat (rows : List Mask) (h : ∀ m ∈ rows, m ≠ 0) :
    ∃ a, satisfies (pins ++ rows) a = true ∧
      ∀ b, satisfies (pins ++ rows) b = true → b = a := by
  exact ⟨0, (pinned_model_iff rows 0).mpr ⟨rfl,(good_iff rows).mpr h⟩,
    fun b hb => ((pinned_model_iff rows b).mp hb).1⟩

def masks : List Mask := 0 :: pins

theorem masks_enumerate : masks.Nodup ∧ ∀ m : Mask, m ∈ masks := by decide

/-- Enumerate all physical sign sequences of a fixed row count. -/
def words : Nat → List (List Mask)
  | 0 => [[]]
  | n+1 => (words n).flatMap (fun r => masks.map (fun m => m :: r))

theorem words_complete (n : Nat) (r : List Mask) : r ∈ words n ↔ r.length = n := by
  induction n generalizing r with
  | zero => simp [words]
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨tail,ht,hmem⟩ := List.mem_flatMap.mp h
      obtain ⟨m,_,rfl⟩ := List.mem_map.mp hmem
      simp [(ih tail).mp ht]
    · intro h
      cases r with
      | nil => simp at h
      | cons m tail =>
        have ht : tail.length = n := Nat.succ.inj h
        exact List.mem_flatMap.mpr ⟨tail, (ih tail).mpr ht,
          List.mem_map.mpr ⟨m, masks_enumerate.2 m, rfl⟩⟩

theorem words_nodup (n : Nat) : (words n).Nodup := by
  induction n with
  | zero => decide
  | succ n ih =>
    apply List.pairwise_flatMap.mpr
    constructor
    · intro r _
      exact List.Pairwise.map (fun m => m :: r)
        (fun _ _ ne eq => ne (List.cons.inj eq).1) masks_enumerate.1
    · apply List.Pairwise.imp _ ih
      intro r s ne u hu v hv eq
      obtain ⟨m,_,rfl⟩ := List.mem_map.mp hu
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp hv
      exact ne (List.cons.inj eq).2

private theorem one_more (r : List Mask) :
    (masks.map (fun m => m :: r)).countP good = if good r then 7 else 0 := by
  have next (m : Mask) : good (m :: r) = ((m != 0) && good r) := rfl
  simp only [masks,pins,List.map_cons,List.map_nil,List.countP_cons,next,List.countP_nil]
  cases good r <;> decide

private theorem count_extend (rs : List (List Mask)) :
    (rs.flatMap (fun r => masks.map (fun m => m :: r))).countP good = rs.countP good * 7 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons, List.countP_append, one_more, ih, List.countP_cons]
    cases good r <;> simp [Nat.add_mul, Nat.add_comm]

private theorem length_extend (rs : List (List Mask)) :
    (rs.flatMap (fun r => masks.map (fun m => m :: r))).length = rs.length * 8 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons]
    change 8 + rs.length * 8 = (rs.length + 1) * 8
    omega

theorem sign_sequences (n : Nat) :
    (words n).length = 8^n ∧ (words n).countP good = 7^n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [words,length_extend,count_extend,ih.1,ih.2,Nat.pow_succ,and_self]

theorem rejected_sequences (n : Nat) :
    (words n).countP (fun r => !(good r)) = 8^n - 7^n := by
  have partition (rs : List (List Mask)) :
      rs.countP (fun r => !(good r)) + rs.countP good = rs.length := by
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      simp only [List.countP_cons, List.length_cons]
      cases h : good r <;> simp [h] <;> omega
  have := partition (words n)
  rw [(sign_sequences n).1,(sign_sequences n).2] at this
  omega

end PinnedClauseMaskSat
