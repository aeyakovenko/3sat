import Std

namespace SortedGatherWitness

/-- The first list contains source addresses. The second contains the gathered records. -/
abbrev Witness (x : List Nat) := List (Fin x.length) × List Nat

/-- Length and strict order are imposed on the values. No permutation test is imposed on
the source addresses. The gather equality also forces the address list to have that length. -/
def Valid (x : List Nat) (w : Witness x) : Prop :=
  w.2.length = x.length ∧ w.2.Pairwise (· < ·) ∧ w.1.map x.get = w.2

private theorem perm_of_distinct_subset {values source : List Nat}
    (unique : values.Nodup) (inside : values ⊆ source)
    (lengths : values.length = source.length) : values.Perm source := by
  induction values generalizing source with
  | nil =>
    have h := List.eq_nil_of_length_eq_zero (l := source) lengths.symm
    simp [h]
  | cons a rest ih =>
    obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
    have memSource : a ∈ source := inside List.mem_cons_self
    have perm := List.perm_cons_erase memSource
    have tailInside : rest ⊆ source.erase a := by
      intro v hv
      have ne : v ≠ a := by
        intro eq
        exact absent (eq ▸ hv)
      exact (List.mem_erase_of_ne ne).mpr (inside (List.mem_cons_of_mem a hv))
    have tailLengths : rest.length = (source.erase a).length := by
      have h := perm.length_eq
      simp only [List.length_cons] at h lengths
      omega
    exact (List.Perm.cons a (ih tailUnique tailInside tailLengths)).trans perm.symm

theorem values_perm {x : List Nat} {w : Witness x} (hw : Valid x w) : w.2.Perm x := by
  obtain ⟨lengths, strict, gather⟩ := hw
  apply perm_of_distinct_subset (strict.imp Nat.ne_of_lt) _ lengths
  intro a mem
  rw [← gather, List.mem_map] at mem
  obtain ⟨i, _, rfl⟩ := mem
  exact List.get_mem x i

theorem distinct_of_valid {x : List Nat} {w : Witness x} (hw : Valid x w) : x.Nodup :=
  (values_perm hw).nodup (hw.2.1.imp Nat.ne_of_lt)

private theorem indices_for_subset {x values : List Nat} (inside : values ⊆ x) :
    ∃ q : List (Fin x.length), q.map x.get = values := by
  induction values with
  | nil => exact ⟨[], rfl⟩
  | cons a rest ih =>
    obtain ⟨i, hi⟩ := List.get_of_mem (inside List.mem_cons_self)
    obtain ⟨q, hq⟩ := ih (fun _ hv => inside (List.mem_cons_of_mem a hv))
    exact ⟨i :: q, by rw [List.map_cons, hi, hq]⟩

theorem exists_of_distinct {x : List Nat} (unique : x.Nodup) : ∃ w, Valid x w := by
  let leq := fun a b : Nat => decide (a ≤ b)
  let c := x.mergeSort leq
  have perm : c.Perm x := List.mergeSort_perm x leq
  have sorted : c.Pairwise (· ≤ ·) := by
    have trans : ∀ a b d, leq a b → leq b d → leq a d := by
      simp only [leq, decide_eq_true_eq]
      omega
    have total : ∀ a b, leq a b || leq b a := by
      simp only [leq, Bool.or_eq_true, decide_eq_true_eq]
      omega
    simpa [c, leq] using List.sorted_mergeSort trans total x
  have strict : c.Pairwise (· < ·) :=
    List.Pairwise.imp₂ (fun _ _ h ne => Nat.lt_of_le_of_ne h ne) sorted (perm.symm.nodup unique)
  obtain ⟨q, gather⟩ := indices_for_subset perm.subset
  exact ⟨(q, c), perm.length_eq, strict, gather⟩

private theorem source_address_unique {x : List Nat} (unique : x.Nodup)
    (i j : Fin x.length) (same : x.get i = x.get j) : i = j := by
  have different := List.pairwise_iff_getElem.mp unique
  apply Fin.ext
  by_cases before : i.val < j.val
  · exact False.elim (different i.val j.val i.isLt j.isLt before same)
  by_cases after : j.val < i.val
  · exact False.elim (different j.val i.val j.isLt i.isLt after same.symm)
  omega

theorem valid_unique {x : List Nat} {a b : Witness x} (ha : Valid x a) (hb : Valid x b) :
    a = b := by
  have values : a.2 = b.2 := List.Perm.eq_of_sorted
    (fun _ _ _ _ hab hba => by omega) ha.2.1 hb.2.1 ((values_perm ha).trans (values_perm hb).symm)
  have addresses : a.1 = b.1 := (List.map_inj_right (source_address_unique (distinct_of_valid ha))).mp
    (ha.2.2.trans (values.trans hb.2.2.symm))
  exact Prod.ext addresses values

theorem exists_iff_distinct (x : List Nat) : (∃ w, Valid x w) ↔ x.Nodup :=
  ⟨fun ⟨_, hw⟩ => distinct_of_valid hw, exists_of_distinct⟩

/-- The gather has zero witnesses on a list with a repeated record and exactly one
ordered pair of address and value lists on a distinct input, including the empty list. -/
theorem unique_witness_iff_distinct (x : List Nat) :
    (∃ w, Valid x w ∧ ∀ other, Valid x other → other = w) ↔ x.Nodup := by
  constructor
  · exact fun ⟨_, hw, _⟩ => distinct_of_valid hw
  · intro unique
    obtain ⟨w, hw⟩ := exists_of_distinct unique
    exact ⟨w, hw, fun _ ho => valid_unique ho hw⟩

end SortedGatherWitness
