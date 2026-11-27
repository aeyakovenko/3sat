import Std

namespace StackPacket

abbrev Pair := Int × Int

def errors (bin : List Pair) : Nat :=
  bin.countP (fun p => decide (p.1 ≠ p.2))

def badBins (bins : List (List Pair)) : Nat :=
  bins.countP (fun bin => decide (0 < errors bin))

def balanced (bin : List Pair) : Prop :=
  (bin.map Prod.fst).sum = (bin.map Prod.snd).sum

private theorem sum_mono (xs : List α) (f g : α → Int)
    (all_le : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x more ih =>
    have h := all_le x (by simp)
    have tail := ih (fun y hy => all_le y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem sum_strict (xs : List α) (f g : α → Int)
    (all_le : ∀ x ∈ xs, f x ≤ g x) (some_lt : ∃ x ∈ xs, f x < g x) :
    (xs.map f).sum < (xs.map g).sum := by
  induction xs with
  | nil => simp at some_lt
  | cons x more ih =>
    have tail_le : ∀ y ∈ more, f y ≤ g y := fun y hy => all_le y (by simp [hy])
    obtain ⟨hit,loc,strict⟩ := some_lt
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp loc with eq | inTail
    · subst hit
      have tail := sum_mono more f g tail_le
      omega
    · have head := all_le x (by simp)
      have tail := ih tail_le ⟨hit, inTail, strict⟩
      omega

private theorem needs_less (xs : List α) (f g : α → Int)
    (eq : (xs.map f).sum = (xs.map g).sum) (diff : ∃ x ∈ xs, f x ≠ g x) :
    ∃ x ∈ xs, f x < g x := by
  apply Classical.byContradiction
  intro none
  have all_le : ∀ x ∈ xs, g x ≤ f x := by
    intro x hx
    exact Int.le_of_not_gt (fun lt => none ⟨x, hx, lt⟩)
  obtain ⟨hit,loc,neq⟩ := diff
  have weak := all_le hit loc
  have violation := sum_strict xs g f all_le ⟨hit, loc, by omega⟩
  omega

theorem both_signs (bin : List Pair) (equal_totals : balanced bin)
    (bad : 0 < errors bin) :
    (∃ p ∈ bin, p.1 < p.2) ∧ (∃ p ∈ bin, p.2 < p.1) := by
  obtain ⟨hit,loc,ne⟩ := List.countP_pos_iff.mp bad
  have diff : hit.1 ≠ hit.2 := of_decide_eq_true ne
  exact ⟨needs_less bin Prod.fst Prod.snd equal_totals ⟨hit, loc, diff⟩,
    needs_less bin Prod.snd Prod.fst equal_totals.symm ⟨hit, loc, Ne.symm diff⟩⟩

def opposite (p q : Pair) : Prop :=
  (p.1 < p.2 ∧ q.2 < q.1) ∨ (p.2 < p.1 ∧ q.1 < q.2)

theorem ordered_pair (bin : List Pair) (equal_totals : balanced bin)
    (bad : 0 < errors bin) :
    ∃ i j : Fin bin.length, i < j ∧ opposite (bin.get i) (bin.get j) := by
  obtain ⟨⟨x,hx,neg⟩,⟨y,hy,pos⟩⟩ := both_signs bin equal_totals bad
  obtain ⟨i,hi,at_i⟩ := List.getElem_of_mem hx
  obtain ⟨j,hj,at_j⟩ := List.getElem_of_mem hy
  have distinct : i ≠ j := by
    intro eq
    subst j
    rw [at_i] at at_j
    subst y
    omega
  by_cases order : i < j
  · refine ⟨⟨i, hi⟩, ⟨j, hj⟩, order, Or.inl ?_⟩
    simpa [List.get_eq_getElem, at_i, at_j] using And.intro neg pos
  · refine ⟨⟨j, hj⟩, ⟨i, hi⟩, (by change j < i; omega), Or.inr ?_⟩
    simpa [List.get_eq_getElem, at_i, at_j] using And.intro pos neg

theorem mismatch_count (bins : List (List Pair)) (G : Nat)
    (sizes : ∀ bin ∈ bins, bin.length ≤ G) : errors bins.flatten ≤ G * badBins bins := by
  induction bins with
  | nil => simp [errors, badBins]
  | cons bin rest ih =>
    have tail := ih (fun x hx => sizes x (by simp [hx]))
    have head := sizes bin (by simp)
    have count_le : errors bin ≤ bin.length := List.countP_le_length
    rw [List.flatten_cons, show errors (bin ++ rest.flatten) =
      errors bin + errors rest.flatten from List.countP_append]
    have newBad : badBins (bin :: rest) =
        badBins rest + (if 0 < errors bin then 1 else 0) := by
      simp [badBins, List.countP_cons]
    rw [newBad, Nat.mul_add]
    by_cases faulty : 0 < errors bin <;> simp [faulty] <;> omega

end StackPacket
