import Std

namespace PairedProbeBudget

/-- Multiplicities of this list count assignments of the unqueried control bits. -/
def subsetSums : List Nat → List Nat
  | [] => [0]
  | c :: cs => subsetSums cs ++ (subsetSums cs).map (fun x => c ^^^ x)

private theorem commuteXor (a b x : Nat) : a ^^^ (b ^^^ x) = b ^^^ (a ^^^ x) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

private theorem cancelXor (a x : Nat) : a ^^^ (a ^^^ x) = x := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

private theorem translateHead (c : Nat) (cs : List Nat) :
    ((subsetSums (c :: cs)).map (fun x => c ^^^ x)).Perm (subsetSums (c :: cs)) := by
  simp only [subsetSums, List.map_append, List.map_map, Function.comp_def, cancelXor,
    List.map_id_fun]
  simpa using (List.perm_append_comm (l₁ := (subsetSums cs).map (fun x => c ^^^ x))
    (l₂ := subsetSums cs))

/-- Translation by any possible hash permutes the multiset of hashes.
    In particular all possible hashes have equal mass on a uniform completion. -/
theorem translateSum (cs : List Nat) (h : Nat) (member : h ∈ subsetSums cs) :
    ((subsetSums cs).map (fun x => h ^^^ x)).Perm (subsetSums cs) := by
  induction cs generalizing h with
  | nil =>
    have : h = 0 := by simpa [subsetSums] using member
    simp [this, subsetSums]
  | cons c cs ih =>
    have liftTail (v : Nat) (mem : v ∈ subsetSums cs) :
        ((subsetSums (c :: cs)).map (fun x => v ^^^ x)).Perm (subsetSums (c :: cs)) := by
      have p := ih v mem
      have p' := p.map (fun x => c ^^^ x)
      simp only [List.map_map, Function.comp_def] at p'
      simp only [subsetSums, List.map_append, List.map_map, Function.comp_def]
      exact p.append (by simpa only [commuteXor v c] using p')
    rcases List.mem_append.1 member with mem | mem
    · exact liftTail h mem
    · obtain ⟨v,vmem,rfl⟩ := List.mem_map.1 mem
      have p := (liftTail v vmem).map (fun x => c ^^^ x)
      simp only [List.map_map, Function.comp_def, ← Nat.xor_assoc] at p
      exact p.trans (translateHead c cs)

theorem zero_mem (cs : List Nat) : 0 ∈ subsetSums cs := by
  induction cs with
  | nil => simp [subsetSums]
  | cons c cs ih => exact List.mem_append_left _ ih

theorem each_column_mem (cs : List Nat) (c : Nat) (member : c ∈ cs) :
    c ∈ subsetSums cs := by
  induction cs with
  | nil => simp at member
  | cons a cs ih =>
    rcases List.mem_cons.1 member with rfl | tail
    · exact List.mem_append_right _ (List.mem_map.2 ⟨0, zero_mem _, Nat.xor_zero _⟩)
    · exact List.mem_append_left _ (ih tail)

private theorem card_le (xs ys : List Nat) (nd : xs.Nodup)
    (inside : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp nd
    have mem := inside x (by simp)
    have pos := List.length_pos_of_mem mem
    have rest := ih (ys.erase x) tail (by
      intro a ha
      have ne : a ≠ x := fun h => fresh (h ▸ ha)
      exact (List.mem_erase_of_ne ne).2 (inside a (by simp [ha])))
    rw [List.length_erase_of_mem mem] at rest
    simp; omega

/-- The possible hashes include zero and each distinct remaining column. -/
theorem support_size (cs : List Nat) (nd : cs.Nodup) (nz : 0 ∉ cs)
    (support : List Nat) (contains : ∀ h ∈ subsetSums cs, h ∈ support) :
    cs.length + 1 ≤ support.length := by
  apply card_le (0 :: cs) support (List.nodup_cons.2 ⟨nz,nd⟩)
  intro h mem
  rcases List.mem_cons.1 mem with rfl | rest
  · exact contains 0 (zero_mem _)
  · exact contains h (each_column_mem cs h rest)

/-- Leaf probabilities compare as hits / M ≤ t / B.  The queried controls
    can exclude at most one possible address each. -/
theorem leaf_bound {B M c d hits t : Nat}
    (image : B ≤ M + c) (queried : hits ≤ d) (depth : c + d ≤ t) (short : t ≤ B) :
    hits * B ≤ t * M := by
  have h1 := Nat.mul_le_mul_right B depth
  have h2 := Nat.mul_le_mul_left t image
  have h3 := Nat.mul_le_mul_left c short
  have h4 := Nat.mul_le_mul_right B queried
  rw [Nat.add_mul] at h1
  rw [Nat.mul_add] at h2
  rw [Nat.mul_comm c t] at h3
  omega

end PairedProbeBudget
