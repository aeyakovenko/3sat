import Std

namespace InverseTraceSubcubeOverlap

/-- Binary displacements supported on the true coordinates of a mask. -/
def shifts : List Bool → List (List Bool)
  | [] => [[]]
  | false :: ms => (shifts ms).map (false :: ·)
  | true :: ms => (shifts ms).map (false :: ·) ++ (shifts ms).map (true :: ·)

def weight : List Bool → Nat
  | [] => 0
  | false :: ms => weight ms
  | true :: ms => weight ms + 1

theorem count_shifts (ms : List Bool) : (shifts ms).length = 2 ^ weight ms := by
  induction ms with
  | nil => simp [shifts, weight]
  | cons b ms ih =>
    cases b <;> simp [shifts, weight, ih, Nat.pow_succ, Nat.mul_two]

theorem shifts_distinct (ms : List Bool) : (shifts ms).Nodup := by
  induction ms with
  | nil => simp [shifts]
  | cons b ms ih =>
    have mapped (v : Bool) : ((shifts ms).map (v :: ·)).Nodup := by
      exact List.pairwise_map.2 (ih.imp (fun ne eq => ne (List.cons.inj eq).2))
    cases b with
    | false => exact mapped false
    | true =>
      rw [shifts, List.Nodup, List.pairwise_append]
      refine ⟨mapped false, mapped true, ?_⟩
      intro l left r right
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp left
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp right
      simp

private theorem head_test (b v : Bool) (ms xs : List Bool) :
    v :: xs ∈ shifts (b :: ms) ↔ (v = false ∨ b = true) ∧ xs ∈ shifts ms := by
  cases b <;> cases v <;> simp [shifts]

private theorem nonempty_mask (b : Bool) (ms : List Bool) : [] ∉ shifts (b :: ms) := by
  cases b <;> simp [shifts]

/-- Two coordinate faces through the same point intersect in exactly the
    displacements supported by the coordinatewise intersection of their masks. -/
theorem common_shifts (axes : List (Bool × Bool)) (delta : List Bool) :
    delta ∈ shifts (axes.map (fun ab => ab.1 && ab.2)) ↔
      delta ∈ shifts (axes.map Prod.fst) ∧ delta ∈ shifts (axes.map Prod.snd) := by
  induction axes generalizing delta with
  | nil => simp
  | cons ab rest ih =>
    obtain ⟨a, b⟩ := ab
    cases delta with
    | nil => simp [nonempty_mask]
    | cons v xs =>
      simp only [List.map_cons, head_test, ih]
      cases a <;> cases b <;> cases v <;> simp [and_assoc, and_left_comm]

/-- The checked common face is enumerated exactly once and has 2^ell elements. -/
theorem common_face_size (axes : List (Bool × Bool)) :
    ∃ pts : List (List Bool), pts.Nodup ∧
      pts.length = 2 ^ weight (axes.map (fun ab => ab.1 && ab.2)) ∧
      ∀ delta, delta ∈ pts ↔
        delta ∈ shifts (axes.map Prod.fst) ∧ delta ∈ shifts (axes.map Prod.snd) :=
  ⟨_, shifts_distinct _, count_shifts _, common_shifts axes⟩

/-- With the root sign fixed, a size-s face imposes s-1 signs. Two faces with
    c common points save c-1 tests relative to counting their costs separately.
    The identity is in integers, with no probability division. -/
theorem overlap_factor (s c : Nat) (nonempty : 1 ≤ c) (contained : c ≤ s) :
    2 ^ (2*s-c-1) * 2 ^ (c-1) = (2 ^ (s-1) : Nat) ^ 2 := by
  rw [← Nat.pow_add, ← Nat.pow_mul]
  congr 1
  omega

end InverseTraceSubcubeOverlap
