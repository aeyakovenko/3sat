import Std

/-! A full-length certificate consists only of in-range indices. The
verifier requires their looked-up values to increase strictly. No ordering
of the index numbers themselves, coverage check, or value-universe scan
is part of the verifier. -/
namespace UniqueIndexOrder

private theorem full_perm {α : Type} [DecidableEq α] (xs base : List α)
    (distinct : xs.Nodup) (inside : ∀ i ∈ xs, i ∈ base) (len : xs.length = base.length) :
    xs.Perm base := by
  induction xs generalizing base with
  | nil =>
    have : base = [] := List.length_eq_zero_iff.mp (by simpa using len.symm)
    simp [this]
  | cons x xs ih =>
    have hx := inside x List.mem_cons_self
    obtain ⟨notIn, distinctTail⟩ := List.nodup_cons.mp distinct
    have sub (i : α) (hi : i ∈ xs) : i ∈ base.erase x :=
      (List.mem_erase_of_ne (a := i) (b := x) (fun h => notIn (h ▸ hi))).mpr
        (inside i (List.mem_cons_of_mem _ hi))
    have lengthTail : xs.length = (base.erase x).length := by
      rw [List.length_erase_of_mem hx]
      simp at len
      omega
    exact ((ih _ distinctTail sub lengthTail).cons x).trans (List.perm_cons_erase hx).symm

def Valid {m : Nat} (lookup : Fin m → Nat) (xs : List (Fin m)) : Prop :=
  xs.length = m ∧ (xs.map lookup).Pairwise (· < ·)

def checkFrom {ι : Type} (lookup : ι → Nat) (previous : Nat) : List ι → Bool
  | [] => true
  | i :: xs =>
    let current := lookup i
    decide (previous < current) && checkFrom lookup current xs

def check {m : Nat} (lookup : Fin m → Nat) (xs : List (Fin m)) : Bool :=
  (xs.length == m) && match xs with
    | [] => true
    | i :: rest => checkFrom lookup (lookup i) rest

private theorem check_from_ok {ι : Type} (lookup : ι → Nat) (previous : Nat) (xs : List ι) :
    checkFrom lookup previous xs = true ↔ (previous :: xs.map lookup).Pairwise (· < ·) := by
  induction xs generalizing previous with
  | nil => simp [checkFrom]
  | cons i xs ih =>
    rw [checkFrom, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons]
    constructor
    · rintro ⟨h, tailSorted⟩
      refine List.pairwise_cons.mpr ⟨?_, tailSorted⟩
      intro n hn
      rcases List.mem_cons.mp hn with rfl | later
      · exact h
      · exact Nat.lt_trans h ((List.pairwise_cons.mp tailSorted).1 n later)
    · intro sorted
      obtain ⟨all, rest⟩ := List.pairwise_cons.mp sorted
      exact ⟨all _ List.mem_cons_self, rest⟩

theorem check_iff_valid {m : Nat} (lookup : Fin m → Nat) (xs : List (Fin m)) :
    check lookup xs = true ↔ Valid lookup xs := by
  cases xs <;> simp [check, Valid, check_from_ok]

theorem valid_is_permutation {m : Nat} {lookup : Fin m → Nat} {xs : List (Fin m)}
    (h : Valid lookup xs) : xs.Perm (List.finRange m) := by
  have pw := List.pairwise_map.mp h.2
  apply full_perm
  · apply pw.imp
    intro a b lt eq
    subst b
    exact Nat.lt_irrefl _ lt
  · intro i _
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  · simpa using h.1

theorem valid_requires_distinct {m : Nat} {lookup : Fin m → Nat} {xs : List (Fin m)}
    (h : Valid lookup xs) : ((List.finRange m).map lookup).Nodup := by
  have hn : (xs.map lookup).Nodup := h.2.imp Nat.ne_of_lt
  exact ((valid_is_permutation h).map lookup).nodup hn

theorem certificates_equal {m : Nat} {lookup : Fin m → Nat} {xs ys : List (Fin m)}
    (hx : Valid lookup xs) (hy : Valid lookup ys) : xs = ys := by
  exact List.Perm.eq_of_sorted (le := fun i j => lookup i < lookup j)
    (fun _ _ _ _ hab hba => False.elim (Nat.lt_asymm hab hba))
    (List.pairwise_map.mp hx.2) (List.pairwise_map.mp hy.2)
    ((valid_is_permutation hx).trans (valid_is_permutation hy).symm)

def sortedIndices {m : Nat} (lookup : Fin m → Nat) : List (Fin m) :=
  (List.finRange m).mergeSort fun i j => decide (lookup i ≤ lookup j)

theorem valid_sorted_iff {m : Nat} (lookup : Fin m → Nat) :
    Valid lookup (sortedIndices lookup) ↔ ((List.finRange m).map lookup).Nodup := by
  constructor
  · exact valid_requires_distinct
  · intro distinct
    have sorted : (sortedIndices lookup).Pairwise (fun i j => lookup i ≤ lookup j) := by
      let le (i j : Fin m) := decide (lookup i ≤ lookup j)
      have trans (i j k : Fin m) : le i j → le j k → le i k := by
        simp only [le, decide_eq_true_eq]
        exact Nat.le_trans
      have total (i j : Fin m) : le i j || le j i := by
        simpa [le] using Nat.le_total (lookup i) (lookup j)
      simpa [sortedIndices, le] using List.sorted_mergeSort trans total (List.finRange m)
    have perm := (List.mergeSort_perm (List.finRange m) (fun i j => decide (lookup i ≤ lookup j)))
    have dn : ((sortedIndices lookup).map lookup).Nodup := (perm.map lookup).symm.nodup distinct
    exact ⟨by simp [sortedIndices],
      ((List.pairwise_map.mpr sorted).and dn).imp fun h => Nat.lt_of_le_of_ne h.1 h.2⟩

theorem certificate_classification {m : Nat} (lookup : Fin m → Nat) (xs : List (Fin m)) :
    Valid lookup xs ↔
    ((List.finRange m).map lookup).Nodup ∧ xs = sortedIndices lookup := by
  constructor
  · intro hx
    have distinct := valid_requires_distinct hx
    exact ⟨distinct, certificates_equal hx ((valid_sorted_iff lookup).mpr distinct)⟩
  · rintro ⟨distinct, rfl⟩
    exact (valid_sorted_iff lookup).mpr distinct

private theorem lookup_table (table : List Nat) :
    (List.finRange table.length).map table.get = table := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Thus a list with duplicates has zero certificates. A list with all
distinct entries has exactly one, including the empty list. -/
theorem list_certificate_iff (table : List Nat) (certificate : List (Fin table.length)) :
    Valid table.get certificate ↔ table.Nodup ∧ certificate = sortedIndices table.get := by
  rw [certificate_classification, lookup_table]

theorem checked_list_certificate_iff (table : List Nat) (certificate : List (Fin table.length)) :
    check table.get certificate = true ↔ table.Nodup ∧ certificate = sortedIndices table.get := by
  rw [check_iff_valid, list_certificate_iff]

private theorem singleton_of_only_member {α : Type} {xs : List α} {x : α}
    (hx : x ∈ xs) (single : ∀ y ∈ xs, y = x) (noCopies : xs.Nodup) : xs = [x] := by
  cases xs with
  | nil => simp at hx
  | cons head tail =>
    obtain rfl := single head List.mem_cons_self
    cases tail with
    | nil => rfl
    | cons y rest =>
      have h := single y (List.mem_cons_of_mem _ List.mem_cons_self)
      have hn := (List.nodup_cons.mp noCopies).1
      exact False.elim (hn (List.mem_cons.mpr (Or.inl h.symm)))

/-- Exact count as a natural number for any duplicate-free exhaustive
enumeration of length-m candidate index strings. Extraneous lengths may
also appear in the enumeration and are rejected by the checker. -/
theorem exhaustive_count (table : List Nat) (candidates : List (List (Fin table.length)))
    (cover : ∀ c : List (Fin table.length), c.length = table.length → c ∈ candidates)
    (noCopies : candidates.Nodup) :
    (candidates.filter (check table.get)).length = if table.Nodup then 1 else 0 := by
  by_cases hd : table.Nodup
  · have hs : sortedIndices table.get ∈ candidates.filter (check table.get) :=
      List.mem_filter.mpr ⟨cover _ (by simp [sortedIndices]),
        (checked_list_certificate_iff _ _).mpr ⟨hd, rfl⟩⟩
    have only c (hc : c ∈ candidates.filter (check table.get)) : c = sortedIndices table.get :=
      ((checked_list_certificate_iff _ _).mp (List.mem_filter.mp hc).2).2
    rw [singleton_of_only_member hs only (List.filter_sublist.nodup noCopies)]
    simp [hd]
  · have empty := List.filter_eq_nil_iff.mpr
        (fun c (_ : c ∈ candidates) (hc : check table.get c = true) =>
          hd ((checked_list_certificate_iff _ _).mp hc).1)
    simp [hd, empty]

end UniqueIndexOrder
