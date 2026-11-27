import Std

namespace PermutationWindowRigidity

private theorem countInside {α : Type} [DecidableEq α] {xs ys : List α}
    (distinct : xs.Nodup) (inside : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    have present := inside x (by simp)
    have pos := List.length_pos_of_mem present
    have shorter := ih tail (ys := ys.erase x) (by
      intro y hy
      have ne : y ≠ x := fun eq => fresh (eq ▸ hy)
      exact (List.mem_erase_of_ne ne).mpr (inside y (by simp [hy])))
    rw [List.length_erase_of_mem present] at shorter
    simp
    omega

private theorem ontoPalette {α : Type} [DecidableEq α] {values palette : List α}
    (distinct : values.Nodup) (subset : ∀ x ∈ values, x ∈ palette)
    (size : values.length = palette.length) {y : α} (hy : y ∈ palette) : y ∈ values := by
  apply Classical.byContradiction
  intro absent
  have bound := countInside distinct (ys := palette.erase y) (by
    intro x hx
    have ne : x ≠ y := fun eq => absent (eq ▸ hx)
    exact (List.mem_erase_of_ne ne).mpr (subset x hx))
  rw [List.length_erase_of_mem hy] at bound
  have pos := List.length_pos_of_mem hy
  omega

/-- Two prescribed old replies at different free addresses coexist in a
permitted completion. If every resulting table is injective, different old
values at such addresses have different new values. -/
theorem crossSeparation {Addr Word : Type} {free : Addr → Prop} {unused : Word → Prop}
    {ok : (Addr → Word) → Prop} {h : Addr → Word → Word}
    {out : (Addr → Word) → Addr → Word}
    (two : ∀ i j v w, free i → free j → i ≠ j → unused v → unused w → v ≠ w →
      ∃ p, ok p ∧ p i = v ∧ p j = w)
    (unchanged : ∀ p, ok p → ∀ i, free i → out p i = h i (p i))
    (safe : ∀ p, ok p → ∀ i j, out p i = out p j → i = j)
    {i j v w} (fi : free i) (fj : free j) (ij : i ≠ j)
    (uv : unused v) (uw : unused w) (vw : v ≠ w) : h i v ≠ h j w := by
  obtain ⟨p, hp, hi, hj⟩ := two i j v w fi fj ij uv uw vw
  intro eq
  apply ij (safe p hp i j ?_)
  rw [unchanged p hp i fi, unchanged p hp j fj, hi, hj, eq]

/-- If no allowed completion collides, every free row must use the same
relabeling on the unused values. The palette is the complement of the fixed
final outputs. Its size equals the number of unused values. -/
theorem commonRelabel {Addr Word : Type} [DecidableEq Word] [DecidableEq Addr]
    (free : Addr → Prop) (unused palette : List Word) (h : Addr → Word → Word)
    (size : unused.length = palette.length)
    (distinct : ∀ i, free i → (unused.map (h i)).Nodup)
    (inside : ∀ i, free i → ∀ v ∈ unused, h i v ∈ palette)
    (cross : ∀ i j, free i → free j → i ≠ j →
      ∀ v ∈ unused, ∀ w ∈ unused, v ≠ w → h i v ≠ h j w)
    {i j} (fi : free i) (fj : free j) {v} (hv : v ∈ unused) :
    h i v = h j v := by
  by_cases ij : i = j
  · rw [ij]
  have onto := ontoPalette (values := unused.map (h j)) (palette := palette)
    (distinct j fj) (by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact inside j fj w hw) (by simpa using size) (inside i fi v hv)
  obtain ⟨w, hw, heq⟩ := List.mem_map.mp onto
  by_cases vw : v = w
  · simpa [vw] using heq.symm
  · exact False.elim (cross i j fi fj ij v hv w hw vw heq.symm)

/-- The sign test may use a proxy that is exact only in a collision-free
family. No co-nondeterministic precheck is needed inside the defect test. -/
theorem badCompletion {S : Type} (ok injective correct : S → Prop) (proxy : Prop)
    (feasible : ∃ s, ok s)
    (exactWhenSafe : (∀ s, ok s → injective s) → ∀ s, ok s → (correct s ↔ proxy)) :
    (∃ s, ok s ∧ ¬(injective s ∧ correct s)) ↔
      (∃ s, ok s ∧ ¬injective s) ∨ ¬proxy := by
  classical
  by_cases collision : ∃ s, ok s ∧ ¬injective s
  · obtain ⟨s, hs, bad⟩ := collision
    exact ⟨fun _ => Or.inl ⟨s, hs, bad⟩, fun _ => ⟨s, hs, fun both => bad both.1⟩⟩
  · have safe : ∀ s, ok s → injective s := by
      intro s hs
      apply Classical.byContradiction
      intro bad
      exact collision ⟨s, hs, bad⟩
    constructor
    · rintro ⟨s, hs, bad⟩
      exact Or.inr (fun good => bad ⟨safe s hs, (exactWhenSafe safe s hs).mpr good⟩)
    · rintro (forbidden | bad)
      · exact False.elim (collision forbidden)
      · obtain ⟨s, hs⟩ := feasible
        exact ⟨s, hs, fun both => bad ((exactWhenSafe safe s hs).mp both.2)⟩

end PermutationWindowRigidity
