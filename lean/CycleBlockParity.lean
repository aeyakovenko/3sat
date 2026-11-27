import Std

namespace CycleBlockParity

/-- For a mark of rank a, count smaller marks to its right. -/
def smaller (a : Nat) : List Nat → Nat
  | [] => 0
  | b :: bs => (if b < a then 1 else 0) + smaller a bs

/-- Count inversions with the left mark in u and the right mark in v. -/
def cross : List Nat → List Nat → Nat
  | [], _ => 0
  | a :: us, v => smaller a v + cross us v

/-- The ordinary strict inversion count of a sequence of ranks. -/
def inversions : List Nat → Nat
  | [] => 0
  | a :: us => smaller a us + inversions us

private theorem smaller_append (a : Nat) (v w : List Nat) :
    smaller a (v ++ w) = smaller a v + smaller a w := by
  induction v with
  | nil => simp [smaller]
  | cons b bs ih => simp [smaller, ih, Nat.add_assoc]

private theorem cross_append_left (u v w : List Nat) :
    cross (u ++ v) w = cross u w + cross v w := by
  induction u with
  | nil => simp [cross]
  | cons a us ih => simp [cross, ih, Nat.add_assoc]

private theorem cross_append_right (u v w : List Nat) :
    cross u (v ++ w) = cross u v + cross u w := by
  induction u with
  | nil => simp [cross]
  | cons a us ih => simp only [cross, smaller_append, ih]; omega

private theorem inversion_append (u v : List Nat) :
    inversions (u ++ v) = inversions u + inversions v + cross u v := by
  induction u with
  | nil => simp [inversions, cross]
  | cons a us ih =>
    simp only [List.cons_append, inversions, smaller_append, cross, ih]
    omega

private theorem one_rank (a : Nat) (v : List Nat) (fresh : ∀ b ∈ v, a ≠ b) :
    smaller a v + cross v [a] = v.length := by
  induction v with
  | nil => simp [smaller, cross]
  | cons b bs ih =>
    have diff := fresh b List.mem_cons_self
    have tail := ih (fun d hd => fresh d (List.mem_cons_of_mem b hd))
    by_cases ba : b < a
    · have ab : ¬a < b := by omega
      simp [smaller, cross, ba, ab]
      omega
    · have ab : a < b := by omega
      simp [smaller, cross, ba, ab]
      omega

/-- Distinct cross-block ranks make exactly one ordering of each pair an inversion.
    Ranks may repeat inside either single block. -/
theorem cross_complement (u v : List Nat) (apart : ∀ a ∈ u, ∀ b ∈ v, a ≠ b) :
    cross u v + cross v u = u.length * v.length := by
  induction u with
  | nil =>
    have empty (l : List Nat) : cross l [] = 0 := by
      induction l with
      | nil => rfl
      | cons a as ih => simp [cross, smaller, ih]
    simp [cross, empty]
  | cons a us ih =>
    have tail := ih (fun d hd => apart d (List.mem_cons_of_mem a hd))
    have head := one_rank a v (apart a List.mem_cons_self)
    have split : cross v (a :: us) = cross v [a] + cross v us :=
      cross_append_right v [a] us
    simp only [cross, split, List.length_cons, Nat.succ_mul]
    omega

/-- Swapping two adjacent blocks adds their length product modulo two.
    No restrictions are needed on the prefix, suffix, or within-block repeats. -/
theorem inversion_parity_swap (pre u v post : List Nat)
    (apart : ∀ a ∈ u, ∀ b ∈ v, a ≠ b) :
    inversions (pre ++ v ++ u ++ post) % 2 =
      (inversions (pre ++ u ++ v ++ post) + u.length * v.length) % 2 := by
  have complements := cross_complement u v apart
  simp only [inversion_append, cross_append_right, cross_append_left]
  omega

/-- Ranks pulled back along an arbitrary map, with disjoint rank images across
    the two blocks. -/
theorem ranked_block_swap (rank : α → Nat) (pre u v post : List α)
    (apart : ∀ x ∈ u, ∀ y ∈ v, rank x ≠ rank y) :
    inversions ((pre ++ v ++ u ++ post).map rank) % 2 =
      (inversions ((pre ++ u ++ v ++ post).map rank) + u.length * v.length) % 2 := by
  have different : ∀ a ∈ u.map rank, ∀ b ∈ v.map rank, a ≠ b := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    exact apart x hx y hy
  simpa only [List.map_append, List.length_map] using
    inversion_parity_swap (pre.map rank) (u.map rank) (v.map rank) (post.map rank) different

end CycleBlockParity
