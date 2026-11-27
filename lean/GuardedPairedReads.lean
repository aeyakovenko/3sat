import Std

namespace GuardedPairedReads

/-- Each row is one candidate continuation. A column contributes one
    mismatch if it contradicts a bit observed in both raw inputs. -/
def totalByRows {R C : Type} (rows : List R) (cols : List C) (cost : R → C → Nat) :=
  (rows.map (fun row => (cols.map (cost row)).sum)).sum

theorem sum_maps_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem swap_sums {R C : Type} (rows : List R) (cols : List C) (cost : R → C → Nat) :
    totalByRows rows cols cost = totalByRows cols rows (fun c r => cost r c) := by
  induction cols with
  | nil =>
    induction rows with
    | nil => rfl
    | cons r rs hr => simpa [totalByRows] using hr
  | cons c cs ih =>
    simp only [totalByRows, List.map_cons, List.sum_cons] at *
    rw [sum_maps_add]
    rw [ih]

theorem double_sum_half {α : Type} (cols : List α) (f : α → Nat) (n : Nat)
    (half : ∀ c ∈ cols, 2 * f c = n) : 2 * (cols.map f).sum = cols.length*n := by
  induction cols with
  | nil => simp
  | cons c cs ih =>
    have hc := half c (by simp)
    have hs := ih (fun a ha => half a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem strict_sum {α : Type} (rows : List α) (f : α → Nat) (k : Nat)
    (hn : rows ≠ []) (large : ∀ r ∈ rows, k < f r) :
    rows.length*k < (rows.map f).sum := by
  have h : ∀ (l : List α), (∀ r ∈ l, k < f r) → l.length*(k+1) ≤ (l.map f).sum := by
    intro l
    induction l with
    | nil => simp
    | cons r l ih =>
      intro hh
      have a := hh r (by simp)
      have b := ih (fun t ht => hh t (List.mem_cons_of_mem _ ht))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  have hprod := h rows large
  rw [Nat.mul_add, Nat.mul_one] at hprod
  cases rows <;> simp_all <;> omega

/-- If every interpolant violates more than the radius while each retained
    column mismatches on exactly half the interpolants, many columns remain. -/
theorem paired_read_bound {R C : Type} (rows : List R) (cols : List C)
    (cost : R → C → Nat) (rad : Nat) (hn : rows ≠ [])
    (half : ∀ c ∈ cols, 2 * (rows.map (fun r => cost r c)).sum = rows.length)
    (rejects : ∀ r ∈ rows, rad < (cols.map (cost r)).sum) :
    2*rad < cols.length := by
  have hlarge := strict_sum rows (fun r => (cols.map (cost r)).sum) rad hn rejects
  have hh := double_sum_half cols (fun c => (rows.map (fun r => cost r c)).sum) rows.length half
  change 2 * totalByRows cols rows (fun c r => cost r c) = _ at hh
  rw [← swap_sums rows cols cost] at hh
  change rows.length*rad < totalByRows rows cols cost at hlarge
  apply Nat.lt_of_not_ge
  intro hsmall
  have hup := Nat.mul_le_mul_right rows.length hsmall
  have hlo := Nat.mul_lt_mul_of_pos_left hlarge (by decide : 0 < 2)
  rw [Nat.mul_comm rows.length rad, ← Nat.mul_assoc] at hlo
  omega

end GuardedPairedReads
