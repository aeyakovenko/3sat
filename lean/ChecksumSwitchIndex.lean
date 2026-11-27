import Std

namespace ChecksumSwitchIndex

private theorem distinct_values_count {X : Type} (f : X → Nat) (xs : List X)
    (ys : List Nat) (different : xs.Pairwise (fun x y => f x ≠ f y))
    (inside : ∀ x ∈ xs, f x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨apart, tail⟩ := List.pairwise_cons.mp different
    have here : f a ∈ ys := inside a (by simp)
    have smaller := ih (ys.erase (f a)) tail (by
      intro x mem
      exact (List.mem_erase_of_ne (Ne.symm (apart x mem))).mpr
        (inside x (by simp [mem])))
    rw [List.length_erase_of_mem here] at smaller
    have pos := List.length_pos_of_mem here
    simp only [List.length_cons]
    omega

/-- Every digest with M possible integer values collides on r-bit masks
    once there are more masks than values. There is no efficiency assumption. -/
theorem mask_collision (r M : Nat) (f : Nat → Nat)
    (inside : ∀ x, x < 2^r → f x < M) (room : M < 2^r) :
    ∃ x y, x < 2^r ∧ y < 2^r ∧ x ≠ y ∧ f x = f y := by
  classical
  apply Classical.byContradiction
  intro noHit
  have ranks : (List.range (2^r)).Pairwise (fun x y => f x ≠ f y) :=
    (List.nodup_range (n := 2^r)).imp_of_mem (by
      intro x y hx hy ne eq
      exact noHit ⟨x, y, List.mem_range.mp hx, List.mem_range.mp hy, ne, eq⟩)
  have small := distinct_values_count f _ (List.range M) ranks (by
    intro x hx
    exact List.mem_range.mpr (inside x (List.mem_range.mp hx)))
  simp only [List.length_range] at small
  omega

private theorem distinguishing_index {x y r : Nat} (hx : x < 2^r) (hy : y < 2^r)
    (different : x ≠ y) : ∃ i < r, x.testBit i ≠ y.testBit i := by
  classical
  apply Classical.byContradiction
  intro none
  apply different
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases low : i < r
  · apply Classical.byContradiction
    exact fun h => none ⟨i, low, h⟩
  · have large : 2^r ≤ 2^i := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx large),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy large)]

theorem affine_residue {M x y : Nat} (same : x % M = y % M) (s a : Nat) :
    (s*x+a) % M = (s*y+a) % M := by
  rw [Nat.add_mod, Nat.add_mod (s*y), Nat.mul_mod, Nat.mul_mod s y, same]

/-- The digested part may be any integer function of the mask, including
    the weighted sum of its chosen bit positions. The common index may
    multiply and translate this value by any index-dependent amounts. -/
theorem switch_after_collision (r M : Nat) (positive : 0 < M) (room : M < 2^r)
    (digest scale offset : Nat → Nat) :
    ∃ x y i, x < 2^r ∧ y < 2^r ∧ i < r ∧ x.testBit i ≠ y.testBit i ∧
      (∀ p, p ∣ M → (scale i * digest x + offset i) % p =
        (scale i * digest y + offset i) % p) := by
  obtain ⟨x,y,hx,hy,ne,same⟩ := mask_collision r M (fun z => digest z % M)
    (fun z _ => Nat.mod_lt _ positive) room
  obtain ⟨i,hi,disagrees⟩ := distinguishing_index hx hy ne
  refine ⟨x,y,i,hx,hy,hi,disagrees,?_⟩
  intro p divides
  have eq := congrArg (fun z => z % p) (affine_residue same (scale i) (offset i))
  simpa only [Nat.mod_mod_of_dvd _ divides] using eq

end ChecksumSwitchIndex
