import Std

namespace StaircaseMatchingWeights

abbrev Edge := Nat × Nat

def rows (edges : List Edge) := edges.map Prod.fst
def columns (edges : List Edge) := edges.map Prod.snd

/-- Rows and columns are indexed from 1. A triangular prefix contains
    exactly the edges whose endpoint sum is at most t+1. -/
structure InTriangle (t : Nat) (edges : List Edge) : Prop where
  disjointRows : (rows edges).Nodup
  disjointColumns : (columns edges).Nodup
  onBoard : ∀ e ∈ edges, 0 < e.1 ∧ 0 < e.2 ∧ e.1+e.2 ≤ t+1

def shortfall (t : Nat) (e : Edge) : Nat := t+1-(e.1+e.2)
def totalShortfall (t : Nat) (edges : List Edge) := (edges.map (shortfall t)).sum

private theorem permSum {xs ys : List Nat} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [ih]
  | swap a b rest => simp only [List.sum_cons]; omega
  | trans a b ha hb => exact ha.trans hb

private theorem sortedNat (xs : List Nat) :
    ∃ ys : List Nat, ys.Perm xs ∧ ys.Pairwise (· ≤ ·) := by
  let cmp := fun a b : Nat => decide (a ≤ b)
  refine ⟨xs.mergeSort cmp,List.mergeSort_perm xs cmp,?_⟩
  apply List.Pairwise.imp (fun h => of_decide_eq_true h : ∀ {a b : Nat}, cmp a b = true → a ≤ b)
  apply List.sorted_mergeSort
  · intro a b c ab bc
    exact decide_eq_true (Nat.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc))
  · intro a b
    rcases Nat.le_total a b with ab | ba
    · simp [cmp,ab]
    · simp [cmp,ba]

/-- The i-th positive distinct sorted endpoint is ≥ i, starting i at 1.
    The shift b counts already skipped indices. -/
private theorem sortedEndpointBound (xs : List Nat) (b : Nat)
    (order : xs.Pairwise (· ≤ ·)) (uniq : xs.Nodup) (positive : ∀ v ∈ xs, b < v) :
    xs.length*(2*b+xs.length+1) ≤ 2*xs.sum := by
  induction xs generalizing b with
  | nil => simp
  | cons x tail ih =>
    obtain ⟨xmin,good⟩ := List.pairwise_cons.mp order
    obtain ⟨fresh,nodup⟩ := List.nodup_cons.mp uniq
    have first := positive x (.head _)
    have bound := ih (b+1) good nodup (by
      intro y hy
      have neq : x ≠ y := fun eq => fresh (eq ▸ hy)
      have weak := xmin y hy
      omega)
    simp only [List.length_cons, List.sum_cons, Nat.mul_add, Nat.add_mul, Nat.mul_one,
      Nat.one_mul] at *
    omega

theorem distinctPositiveSum (xs : List Nat) (uniq : xs.Nodup) (positive : ∀ v ∈ xs, 0 < v) :
    xs.length*(xs.length+1) ≤ 2*xs.sum := by
  obtain ⟨ys, perm, order⟩ := sortedNat xs
  have bound := sortedEndpointBound ys 0 order (perm.nodup_iff.mpr uniq)
    (fun x hx => positive x (perm.mem_iff.mp hx))
  simpa [perm.length_eq, permSum perm] using bound

private theorem bookkeeping (edges : List Edge) (t : Nat)
    (within : ∀ e ∈ edges, e.1+e.2 ≤ t+1) :
    totalShortfall t edges + (rows edges).sum + (columns edges).sum = edges.length*(t+1) := by
  induction edges with
  | nil => simp [totalShortfall, rows, columns]
  | cons e tail ih =>
    have fits := within e (.head _)
    have rest := ih (fun v hv => within v (.tail e hv))
    change (t+1-(e.1+e.2) + totalShortfall t tail) + (e.1+(rows tail).sum) +
      (e.2+(columns tail).sum) = (tail.length+1)*(t+1)
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Exact shortfall budget for an arbitrary genuine matching. -/
theorem shortfallBudget (m d t : Nat) (edges : List Edge) (board : InTriangle t edges)
    (count : edges.length = m) (deficit : t = m+d) :
    totalShortfall t edges ≤ m*d := by
  have rowBound := distinctPositiveSum (rows edges) board.disjointRows (by
    intro i hi
    obtain ⟨e, he, val⟩ := List.mem_map.mp hi
    exact val ▸ (board.onBoard e he).1)
  have colBound := distinctPositiveSum (columns edges) board.disjointColumns (by
    intro i hi
    obtain ⟨e, he, val⟩ := List.mem_map.mp hi
    exact val ▸ (board.onBoard e he).2.1)
  simp only [rows, columns, List.length_map, count] at rowBound colBound
  have total := bookkeeping edges t (fun e he => (board.onBoard e he).2.2)
  change totalShortfall t edges + (edges.map Prod.fst).sum + (edges.map Prod.snd).sum = _ at total
  rw [count, deficit] at total
  rw [deficit]
  simp only [Nat.mul_add, Nat.mul_one] at *
  omega

theorem deficitForm (t d : Nat) (edges : List Edge) (board : InTriangle t edges)
    (fits : d ≤ t) (count : edges.length = t-d) :
    totalShortfall t edges ≤ (t-d)*d :=
  shortfallBudget (t-d) d t edges board count (by omega)

private theorem sumZeroMember (xs : List Nat) (zero : xs.sum = 0) (x : Nat) (hx : x ∈ xs) : x = 0 := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
    change a+rest.sum = 0 at zero
    cases hx with
    | head => omega
    | tail _ h => exact ih (by omega) h

theorem fullOnDiagonal (edges : List Edge) (board : InTriangle t edges)
    (full : edges.length = t) (e : Edge) (he : e ∈ edges) : e.1+e.2 = t+1 := by
  have b := shortfallBudget t 0 t edges board full rfl
  have zero : (edges.map (shortfall t)).sum = 0 := Nat.eq_zero_of_le_zero b
  have z := sumZeroMember _ zero (shortfall t e) (List.mem_map_of_mem he)
  have upper := (board.onBoard e he).2.2
  unfold shortfall at z
  omega

private theorem sortedCapacity (xs : List Nat) (b t : Nat)
    (order : xs.Pairwise (· ≤ ·)) (uniq : xs.Nodup) (span : ∀ v ∈ xs, b < v ∧ v ≤ t) :
    xs.length ≤ t-b := by
  induction xs generalizing b with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
    obtain ⟨xmin,sorted⟩ := List.pairwise_cons.mp order
    obtain ⟨fresh,nodup⟩ := List.nodup_cons.mp uniq
    have first := span x (.head _)
    have tail := ih x sorted nodup (by
      intro v hv
      have bound := span v (.tail x hv)
      have order := xmin v hv
      have neq : x ≠ v := fun eq => fresh (eq ▸ hv)
      omega)
    change rest.length+1 ≤ t-b
    omega

private theorem capacity (xs : List Nat) (t : Nat) (uniq : xs.Nodup)
    (span : ∀ v ∈ xs, 0 < v ∧ v ≤ t) : xs.length ≤ t := by
  obtain ⟨ys, perm, order⟩ := sortedNat xs
  have bound := sortedCapacity ys 0 t order (perm.nodup_iff.mpr uniq)
    (fun v hv => span v (perm.mem_iff.mp hv))
  simpa [perm.length_eq] using bound

/-- A full matching contains every anti-diagonal edge, so its labeled edge
    set is uniquely determined, even when its input order can vary. -/
theorem fullEdgeSet (edges : List Edge) (board : InTriangle t edges)
    (full : edges.length = t) (i j : Nat) :
    (i,j) ∈ edges ↔ 0 < i ∧ 0 < j ∧ i+j = t+1 := by
  constructor
  · intro present
    have info := board.onBoard _ present
    exact ⟨info.1, info.2.1, fullOnDiagonal edges board full _ present⟩
  · rintro ⟨hi,hj,diag⟩
    have present : i ∈ rows edges := by
      apply Decidable.byContradiction
      intro missing
      have unique := List.nodup_cons.mpr ⟨missing,board.disjointRows⟩
      have bound := capacity (i :: rows edges) t unique (by
        intro v hv
        cases hv with
        | head => exact ⟨hi,by omega⟩
        | tail _ h =>
          obtain ⟨e,he,val⟩ := List.mem_map.mp h
          have facts := board.onBoard e he
          change e.1 = v at val
          omega)
      simp [rows,full] at bound
      omega
    obtain ⟨⟨k,l⟩,selected,eq⟩ := List.mem_map.mp present
    change k = i at eq
    have w : k+l = t+1 := fullOnDiagonal edges board full _ selected
    have second : l = j := by omega
    exact eq ▸ second ▸ selected

/-- The smaller anti-diagonal already lies in every larger prefix. -/
def diagonal (m : Nat) : List Edge := (List.range' 1 m).map (fun i => (i,m+1-i))

theorem diagonalBoard (m d : Nat) : InTriangle (m+d) (diagonal m) := by
  constructor
  · simpa [rows,diagonal,List.map_map,Function.comp_def] using (List.nodup_range' (s:=1) (n:=m))
  · simp only [columns,diagonal,List.map_map,Function.comp_def]
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ (List.nodup_range' (s:=1) (n:=m))
    intro a b ha hb differ same
    have ba := List.mem_range'_1.mp ha
    have bb := List.mem_range'_1.mp hb
    exact differ (by omega)
  · intro e present
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp present
    have bound := List.mem_range'_1.mp hi
    cases eq
    change 0 < i ∧ 0 < m+1-i ∧ i+(m+1-i) ≤ m+d+1
    omega

/-- Sharpness for every m and d, not just for perfect matchings. -/
theorem sharpShortfall (m d : Nat) :
    ∃ edges, InTriangle (m+d) edges ∧ edges.length = m ∧ totalShortfall (m+d) edges = m*d := by
  refine ⟨diagonal m, diagonalBoard m d, by simp [diagonal], ?_⟩
  unfold totalShortfall diagonal
  rw [List.map_map]
  have constant :
      (List.range' 1 m).map (shortfall (m+d) ∘ fun i => (i,m+1-i)) =
          (List.range' 1 m).map (Function.const Nat d) := by
    apply List.map_congr_left
    intro i hi
    have bound := List.mem_range'_1.mp hi
    change m+d+1-(i+(m+1-i)) = d
    omega
  rw [constant, List.map_const, List.length_range', List.sum_replicate_nat]

/-- Each chosen edge below the most recent w anti-diagonals costs at
    least w units from the same matching's shortfall budget. -/
private theorem farPayment (edges : List Edge) (t w : Nat) :
    (edges.filter (fun e => decide (w ≤ shortfall t e))).length * w ≤ totalShortfall t edges := by
  induction edges with
  | nil => simp [totalShortfall]
  | cons e rest ih =>
    by_cases old : w ≤ shortfall t e
    · simp [List.filter_cons,old,Nat.add_mul]
      change _ ≤ shortfall t e + totalShortfall t rest
      omega
    · simp [List.filter_cons,old]
      change _ ≤ shortfall t e + totalShortfall t rest
      omega

theorem outsideWindowBound (edges : List Edge) (board : InTriangle (m+d) edges)
    (count : edges.length = m) (w : Nat) :
    (edges.filter (fun e => decide (w ≤ shortfall (m+d) e))).length * w ≤ m*d :=
  Nat.le_trans (farPayment edges (m+d) w) (shortfallBudget m d (m+d) edges board count rfl)

/-- If thresholds are at least w apart, no edge from the earlier prefix
    can contribute to the most recent w anti-diagonals of the later one. -/
theorem disjointRecentWindows (earlier later w : Nat) (e : Edge)
    (separated : earlier+w ≤ later) (present : e.1+e.2 ≤ earlier+1) :
    w ≤ shortfall later e := by
  unfold shortfall
  omega

end StaircaseMatchingWeights
