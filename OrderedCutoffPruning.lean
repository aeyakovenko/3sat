import Std

namespace OrderedCutoffPruning

/-- Total occurrences of colors strictly below the palette size. -/
private def mass (row : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => mass row k + row.count k

private theorem mass_cons (c : Nat) (row : List Nat) (k : Nat) :
    mass (c :: row) k = mass row k + (if c < k then 1 else 0) := by
  induction k with
  | zero => simp [mass]
  | succ k ih =>
    simp only [mass, ih, List.count_cons]
    by_cases h : c = k
    · subst c
      simp
      omega
    · have hb : (c == k) = false := by simpa using h
      by_cases small : c < k
      · simp [hb, small, Nat.lt_succ_of_lt small]
        omega
      · have big : ¬ c < k+1 := by omega
        simp [hb, small, big]

private theorem mass_eq_length (row : List Nat) (k : Nat)
    (palette : ∀ c ∈ row, c < k) : mass row k = row.length := by
  induction row with
  | nil => induction k <;> simp_all [mass]
  | cons c row ih =>
    rw [mass_cons, if_pos (palette c (by simp)),
      ih (fun a ha => palette a (by simp [ha]))]
    simp

private theorem mass_le (row : List Nat) (k cap : Nat)
    (bounded : ∀ c < k, row.count c ≤ cap) : mass row k ≤ k * cap := by
  induction k with
  | zero => simp [mass]
  | succ k ih =>
    simp only [mass, Nat.succ_mul]
    exact Nat.add_le_add (ih (fun c hc => bounded c (by omega)))
      (bounded k (by omega))

theorem heavy_color (row : List Nat) (k r : Nat)
    (palette : ∀ c ∈ row, c < k) (room : k * (r-1) < row.length) :
    ∃ c < k, r ≤ row.count c := by
  classical
  apply Classical.byContradiction
  intro noColor
  have cap : ∀ c < k, row.count c ≤ r-1 := by
    intro c hc
    have small : ¬ r ≤ row.count c := fun h => noColor ⟨c, hc, h⟩
    omega
  have h := mass_le row k (r-1) cap
  rw [mass_eq_length row k palette] at h
  omega

private theorem distinct_bound (f : Nat → Nat) (xs ys : List Nat)
    (apart : xs.Pairwise (fun x y => f x ≠ f y))
    (inside : ∀ x ∈ xs, f x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨first,tail⟩ := List.pairwise_cons.mp apart
    have here := inside x (by simp)
    have bound := ih (ys.erase (f x)) tail (by
      intro y hy
      exact (List.mem_erase_of_ne (Ne.symm (first y hy))).mpr
        (inside y (by simp [hy])))
    rw [List.length_erase_of_mem here] at bound
    have pos := List.length_pos_of_mem here
    simp only [List.length_cons]
    omega

/-- The i-th row lists the colors of its distinct physical selector positions.
    Different rows may have different lengths. -/
theorem repeated_heavy (k r : Nat) (row : Nat → List Nat)
    (palette : ∀ i ≤ k, ∀ c ∈ row i, c < k)
    (room : ∀ i ≤ k, k * (r-1) < (row i).length) :
    ∃ i j c, i < j ∧ j ≤ k ∧ c < k ∧
      r ≤ (row i).count c ∧ r ≤ (row j).count c := by
  classical
  have choice (i : Nat) (hi : i ≤ k) :=
    heavy_color (row i) k r (palette i hi) (room i hi)
  let f (i : Nat) : Nat := if h : i ≤ k then (choice i h).choose else 0
  have selected (i : Nat) (hi : i ≤ k) :
      f i < k ∧ r ≤ (row i).count (f i) := by
    simpa [f, hi] using (choice i hi).choose_spec
  apply Classical.byContradiction
  intro noPair
  have split (i j : Nat) (hij : i < j) (hj : j ≤ k) : f i ≠ f j := by
    intro same
    have left := selected i (by omega)
    have right := selected j hj
    exact noPair ⟨i,j,f i,hij,hj,left.1,left.2,same ▸ right.2⟩
  have apart : (List.range (k+1)).Pairwise (fun i j => f i ≠ f j) :=
    (List.nodup_range (n := k+1)).imp_of_mem (by
      intro i j hi hj ne
      have hi' := List.mem_range.mp hi
      have hj' := List.mem_range.mp hj
      rcases Nat.lt_or_gt_of_ne ne with lt | gt
      · exact split i j lt (by omega)
      · exact Ne.symm (split j i gt (by omega)))
  have bound := distinct_bound f _ (List.range k) apart (by
    intro i hi
    exact List.mem_range.mpr (selected i (by have := List.mem_range.mp hi; omega)).1)
  simp only [List.length_range] at bound
  omega

abbrev Interval := Nat × Nat

def Contains (I : Interval) (x : Nat) : Prop := I.1 < x ∧ x ≤ I.2

def Covered (live : List Interval) (x : Nat) : Prop := ∃ I ∈ live, Contains I x

/-- The file for endpoint a asks whether a witness is at most a. -/
def Cutoff (W : Nat → Prop) (a : Nat) : Prop := ∃ x, W x ∧ x ≤ a

theorem cutoff_iff (W : Nat → Prop) (mu : Nat) (witness : W mu)
    (least : ∀ x, W x → mu ≤ x) (a : Nat) : Cutoff W a ↔ mu ≤ a := by
  constructor
  · rintro ⟨x,hx,ha⟩
    exact Nat.le_trans (least x hx) ha
  · exact fun ha => ⟨mu,witness,ha⟩

/-- Erasing a candidate loses the least witness only if the cutoffs enclosing
    that candidate have opposite verdicts. Overlapping intervals are allowed. -/
theorem deletion_or_cutoff_jump (W : Nat → Prop) (mu a b : Nat)
    (witness : W mu) (least : ∀ x, W x → mu ≤ x) (live : List Interval)
    (covered : Covered live mu) (drop : Interval)
    (between : ∀ x, Contains drop x → a < x ∧ x ≤ b) :
    Covered (live.erase drop) mu ∨ (¬ Cutoff W a ∧ Cutoff W b) := by
  classical
  by_cases here : Contains drop mu
  · obtain ⟨left,right⟩ := between mu here
    rw [cutoff_iff W mu witness least, cutoff_iff W mu witness least]
    exact Or.inr ⟨by omega,right⟩
  · obtain ⟨I,mem,kept⟩ := covered
    have ne : I ≠ drop := fun eq => here (eq ▸ kept)
    exact Or.inl ⟨I,(List.mem_erase_of_ne ne).mpr mem,kept⟩

/-- K+1 endpoint classes force a usable deletion or a color with at least r
    negative and r positive copies. The victim can be chosen arbitrarily
    between the two endpoints subject to the displayed containment. -/
theorem pruning_or_mixed_color (k r mu : Nat) (W : Nat → Prop)
    (witness : W mu) (least : ∀ x, W x → mu ≤ x)
    (row : Nat → List Nat) (palette : ∀ i ≤ k, ∀ c ∈ row i, c < k)
    (room : ∀ i ≤ k, k * (r-1) < (row i).length)
    (cut : Nat → Nat) (live : List Interval) (covered : Covered live mu)
    (drop : Nat → Nat → Interval)
    (active : ∀ i j, i < j → j ≤ k → drop i j ∈ live)
    (between : ∀ i j, i < j → j ≤ k → ∀ x, Contains (drop i j) x →
      cut i < x ∧ x ≤ cut j) :
    ∃ i j c, i < j ∧ j ≤ k ∧ c < k ∧ r ≤ (row i).count c ∧ r ≤ (row j).count c ∧
      (live.erase (drop i j)).length < live.length ∧
      (Covered (live.erase (drop i j)) mu ∨ (¬ Cutoff W (cut i) ∧ Cutoff W (cut j))) := by
  obtain ⟨i,j,c,hij,hj,hc,ni,nj⟩ := repeated_heavy k r row palette room
  have mem := active i j hij hj
  have len := List.length_erase_of_mem mem
  have pos := List.length_pos_of_mem mem
  exact ⟨i,j,c,hij,hj,hc,ni,nj,by omega,
    deletion_or_cutoff_jump W mu (cut i) (cut j) witness least live covered
      (drop i j) (between i j hij hj)⟩

/-- At one depth retain the earliest interval with each chosen heavy color. -/
def firstColor (pick : Nat → Nat) (j : Nat) : Bool :=
  (List.range j).all fun i => pick i != pick j

def keptIndices (pick : Nat → Nat) (n : Nat) : List Nat :=
  (List.range n).filter (firstColor pick)

private theorem first_iff (pick : Nat → Nat) (j : Nat) :
    firstColor pick j = true ↔ ∀ i < j, pick i ≠ pick j := by
  simp [firstColor, List.all_eq_true]

private theorem kept_iff (pick : Nat → Nat) (n j : Nat) :
    j ∈ keptIndices pick n ↔ j < n ∧ ∀ i < j, pick i ≠ pick j := by
  simp [keptIndices, first_iff]

theorem kept_count (pick : Nat → Nat) (n k : Nat) (colors : ∀ i < n, pick i < k) :
    (keptIndices pick n).length ≤ k := by
  have unique : (keptIndices pick n).Nodup :=
    (List.nodup_range (n := n)).sublist List.filter_sublist
  have apart : (keptIndices pick n).Pairwise (fun i j => pick i ≠ pick j) :=
    unique.imp_of_mem (by
      intro i j hi hj neq
      rcases Nat.lt_or_gt_of_ne neq with lt | gt
      · exact ((kept_iff pick n j).mp hj).2 i lt
      · exact Ne.symm (((kept_iff pick n i).mp hi).2 j gt))
  simpa only [List.length_range] using distinct_bound pick _ (List.range k) apart (by
    intro i hi
    exact List.mem_range.mpr (colors i ((kept_iff pick n i).mp hi).1))

/-- If simultaneously keeping only first representatives loses the least
    witness, an earlier negative and the discarded positive endpoint carry
    the same heavy color. Inclusive lower bounds allow assignment zero. -/
theorem simultaneous_loss (n r mu : Nat) (W : Nat → Prop)
    (witness : W mu) (least : ∀ x, W x → mu ≤ x)
    (low high pick : Nat → Nat) (row : Nat → List Nat)
    (ordered : ∀ i j, i < j → j < n → high i < low j)
    (heavy : ∀ j < n, r ≤ (row j).count (pick j))
    (before : ∃ j < n, low j ≤ mu ∧ mu ≤ high j)
    (after : ∀ j ∈ keptIndices pick n, ¬ (low j ≤ mu ∧ mu ≤ high j)) :
    ∃ i j c, i < j ∧ j < n ∧ r ≤ (row i).count c ∧ r ≤ (row j).count c ∧
      ¬ Cutoff W (high i) ∧ Cutoff W (high j) := by
  classical
  obtain ⟨j,hj,lo,hi⟩ := before
  have lost : j ∉ keptIndices pick n := fun h => after j h ⟨lo,hi⟩
  have earlier : ∃ i < j, pick i = pick j := by
    apply Classical.byContradiction
    intro none
    exact lost ((kept_iff pick n j).mpr ⟨hj,fun i lt eq => none ⟨i,lt,eq⟩⟩)
  obtain ⟨i,hij,same⟩ := earlier
  have cutoff := ordered i j hij hj
  refine ⟨i,j,pick j,hij,hj,same ▸ heavy i (by omega),heavy j hj,?_,?_⟩
  · rw [cutoff_iff W mu witness least]
    omega
  · exact (cutoff_iff W mu witness least _).mpr hi

end OrderedCutoffPruning
