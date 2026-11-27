import Std

namespace UnitSATListTransfer

/-- Integer weights of all selector assignments. A selected name contributes
zero on a hit (opposite unit literals), and reverses the sign on a miss. -/
def selectorTerms : List Bool → List Int
  | [] => [1]
  | hit :: hits =>
    let tail := selectorTerms hits
    tail ++ tail.map (fun a => if hit then 0 else -a)

private theorem neg_sum (l : List Int) :
    (l.map (fun a => -a)).sum = -l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

private theorem zero_sum (l : List Int) :
    (l.map (fun _ => (0 : Int))).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem sum_append_int (l r : List Int) :
    (l ++ r).sum = l.sum + r.sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Int.add_assoc]

theorem selector_cancellation (hits : List Bool) :
    (selectorTerms hits).sum = (if hits.all id then (1 : Int) else 0) := by
  induction hits with
  | nil => rfl
  | cons hit hits ih =>
    cases hit with
    | false =>
      change (selectorTerms hits ++ (selectorTerms hits).map (fun a => -a)).sum = 0
      rw [sum_append_int, neg_sum]
      omega
    | true =>
      change (selectorTerms hits ++ (selectorTerms hits).map (fun _ => (0 : Int))).sum = _
      rw [sum_append_int, zero_sum, Int.add_zero]
      exact ih

/-- Distinct guessed values, all present in a source of the same length,
necessarily give a permutation even when the source was untrusted. -/
theorem perm_of_distinct_coverage {ys xs : List Nat} (nd : ys.Nodup)
    (same : ys.length = xs.length) (cover : ys ⊆ xs) : ys.Perm xs := by
  induction ys generalizing xs with
  | nil =>
    cases xs <;> simp_all
  | cons y ys ih =>
    have mem : y ∈ xs := cover (by simp)
    obtain ⟨fresh, nd'⟩ := List.nodup_cons.mp nd
    apply List.cons_perm_iff_perm_erase.mpr
    refine ⟨mem, ih nd' ?_ ?_⟩
    · rw [List.length_erase_of_mem mem]
      simp at same
      omega
    · intro z hz
      have ne : z ≠ y := fun eq => fresh (eq ▸ hz)
      exact (List.mem_erase_of_ne ne).mpr (cover (by simp [hz]))

theorem sorted_guess_unique {ys zs xs : List Nat}
    (sy : ys.Pairwise (· < ·)) (sz : zs.Pairwise (· < ·))
    (ly : ys.length = xs.length) (lz : zs.length = xs.length)
    (hy : ys ⊆ xs) (hz : zs ⊆ xs) : ys = zs ∧ xs.Nodup := by
  have ny : ys.Nodup := sy.imp (fun h => Nat.ne_of_lt h)
  have nz : zs.Nodup := sz.imp (fun h => Nat.ne_of_lt h)
  have py := perm_of_distinct_coverage ny ly hy
  have pz := perm_of_distinct_coverage nz lz hz
  exact ⟨List.Perm.eq_of_sorted (by intros; omega) sy sz (py.trans pz.symm),
    py.nodup_iff.mp ny⟩

/-- If a sorted witness survives, its source-row indices are forced. -/
theorem matching_row_unique {xs : List Nat} (nd : xs.Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length)
    (same : xs[i] = xs[j]) : i = j := by
  by_cases lt : i < j
  · exact False.elim ((List.pairwise_iff_getElem.mp nd i j hi hj lt) same)
  · by_cases gt : j < i
    · exact False.elim ((List.pairwise_iff_getElem.mp nd j i hj hi gt) same.symm)
    · omega

/-- A record is the pair of its high and low words. Selected rows force both
coordinate flags. Each flag bank permits at most one chosen coordinate. -/
theorem two_selected_iff_duplicate {Row High Low : Type}
    (high : Row → High) (low : Row → Low) :
    (∃ (sel : Row → Prop) (flagH : High → Prop) (flagL : Low → Prop),
      (∃ i j, i ≠ j ∧ sel i ∧ sel j) ∧
      (∀ i, sel i → flagH (high i) ∧ flagL (low i)) ∧
      (∀ a b, flagH a → flagH b → a = b) ∧
      (∀ a b, flagL a → flagL b → a = b)) ↔
    ∃ i j, i ≠ j ∧ high i = high j ∧ low i = low j := by
  constructor
  · rintro ⟨_, _, _, ⟨i, j, ne, si, sj⟩, force, onlyH, onlyL⟩
    exact ⟨i, j, ne, onlyH _ _ (force i si).1 (force j sj).1,
                      onlyL _ _ (force i si).2 (force j sj).2⟩
  · rintro ⟨i, j, ne, eqH, eqL⟩
    refine ⟨fun r => r = i ∨ r = j, fun a => a = high i,
            fun b => b = low i, ⟨i, j, ne, Or.inl rfl, Or.inr rfl⟩, ?_, ?_, ?_⟩
    · intro r hr
      rcases hr with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · exact ⟨eqH.symm, eqL.symm⟩
    · exact fun _ _ ha hb => ha.trans hb.symm
    · exact fun _ _ ha hb => ha.trans hb.symm

end UnitSATListTransfer
