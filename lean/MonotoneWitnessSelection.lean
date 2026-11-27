import Std

/-! A selector sees answers to a finite family of predicates monotone in the
hidden support. Its output must belong to every nonempty support in the
given finite universe. Predicates may have arbitrary computation cost. -/
namespace MonotoneWitnessSelection

private theorem strict_count {Q : Type} (qs : List Q) (new old : Q → Bool)
    (mono : ∀ q, new q = true → old q = true)
    (diff : ∃ q ∈ qs, new q ≠ old q) : qs.countP new < qs.countP old := by
  obtain ⟨q, hq, hd⟩ := diff
  have hn : new q = false := by
    cases h : new q with
    | false => rfl
    | true => exact False.elim (hd (h.trans (mono q h).symm))
  have ho : old q = true := by
    cases h : old q with
    | false => exact False.elim (hd (hn.trans h.symm))
    | true => rfl
  obtain ⟨l, r, rfl⟩ := List.append_of_mem hq
  have hl : l.countP new ≤ l.countP old := List.countP_mono_left (fun q _ => mono q)
  have hr : r.countP new ≤ r.countP old := List.countP_mono_left (fun q _ => mono q)
  simp [List.countP_append, List.countP_cons, hn, ho] <;> omega

/-- Deleting the reported witness repeatedly spends one positive answer at
each nonfinal step. Distinctness of the output universe is explicit. -/
theorem selection_bound {α Q : Type} [DecidableEq α] (pool : List α) (nodup : pool.Nodup)
    (qs : List Q) (answer : Q → List α → Bool) (select : List Bool → α)
    (mono : ∀ q (s t : List α), s ⊆ t → answer q s = true → answer q t = true)
    (sound : ∀ s : List α, s ⊆ pool → s ≠ [] → select (qs.map (answer · s)) ∈ s) :
    pool.length ≤ qs.length + 1 := by
  have aux (n : Nat) : ∀ s : List α, s.length = n → s.Nodup → s ⊆ pool →
      s.length ≤ qs.countP (answer · s) + 1 := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro s size unique sub
      by_cases small : s.length ≤ 1
      · omega
      have nonempty : s ≠ [] := by rintro rfl; simp at small
      let x := select (qs.map (answer · s))
      have hx : x ∈ s := sound s sub nonempty
      let t := s.erase x
      have len : t.length = s.length - 1 := List.length_erase_of_mem hx
      have tsub : t ⊆ s := List.erase_subset
      have tpool : t ⊆ pool := fun _ h => sub (tsub h)
      have tne : t ≠ [] := by intro h; rw [h] at len; simp at len; omega
      have hxt : x ∉ t := unique.not_mem_erase
      have diff : ∃ q ∈ qs, answer q t ≠ answer q s := by
        apply Classical.byContradiction
        intro h
        have same : qs.map (answer · t) = qs.map (answer · s) := by
          apply List.map_congr_left
          intro q hq
          apply Classical.byContradiction
          intro neq
          exact h ⟨q, hq, neq⟩
        have valid := sound t tpool tne
        rw [same] at valid
        exact hxt valid
      have drop := strict_count qs (answer · t) (answer · s) (fun q => mono q t s tsub) diff
      have smaller := ih t.length (by omega) t rfl (unique.erase x) tpool
      omega
  have first := aux pool.length pool rfl nodup (fun _ h => h)
  have cap : qs.countP (answer · pool) ≤ qs.length := List.countP_le_length
  omega

/-- Number of internal query nodes in a complete binary decision tree. -/
def binaryNodes : Nat → Nat
  | 0 => 0
  | d + 1 => 1 + 2 * binaryNodes d

theorem binaryNodes_add_one (d : Nat) : binaryNodes d + 1 = 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [binaryNodes, Nat.pow_succ, ← ih]; omega

/-- The supplied list covers the common tree and all the local trees on its
leaves. Depth and node accounting are independent of the predicates. -/
theorem common_local_bound {α Q : Type} [DecidableEq α] (pool : List α) (nodup : pool.Nodup)
    (qs : List Q) (answer : Q → List α → Bool) (select : List Bool → α)
    (mono : ∀ q (s t : List α), s ⊆ t → answer q s = true → answer q t = true)
    (sound : ∀ s : List α, s ⊆ pool → s ≠ [] → select (qs.map (answer · s)) ∈ s)
    (b r q : Nat)
    (nodes : qs.length ≤ binaryNodes r + (2 ^ r) * (b * binaryNodes q)) :
    pool.length ≤ (2 ^ r) * (1 + b * (2 ^ q - 1)) := by
  have bound := selection_bound pool nodup qs answer select mono sound
  have common := binaryNodes_add_one r
  have localSize : 2 ^ q - 1 = binaryNodes q := by have := binaryNodes_add_one q; omega
  rw [localSize, Nat.mul_add, Nat.mul_one]
  omega

end MonotoneWitnessSelection
