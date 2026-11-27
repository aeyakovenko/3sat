import Std

namespace NoisyDualCuts

/-- Character sum over the span of independent binary basis vectors, given
    the values of their linear functionals at a fixed coordinate or input. -/
def spanSum : List Bool → Int
  | [] => 1
  | a :: as => spanSum as + (if a then -spanSum as else spanSum as)

theorem span_sum_exact (bits : List Bool) :
    spanSum bits = if true ∈ bits then 0 else (2 : Int)^bits.length := by
  induction bits with
  | nil => simp [spanSum]
  | cons bit bs ih =>
    cases bit <;> by_cases h : true ∈ bs <;>
      simp [spanSum, ih, h, Int.pow_succ] <;> omega

def total {α β : Type} (rs : List α) (cs : List β) (f : α → β → Nat) :=
  (rs.map (fun r => (cs.map (f r)).sum)).sum

theorem sum_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun i => f i + g i)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem swap {α β : Type} (rs : List α) (cs : List β) (f : α → β → Nat) :
    total rs cs f = total cs rs (fun c r => f r c) := by
  induction cs with
  | nil =>
    induction rs with
    | nil => rfl
    | cons r rs ih => simpa [total] using ih
  | cons c cs ih =>
    simp only [total, List.map_cons, List.sum_cons] at *
    rw [sum_add, ih]

theorem rows_min {α : Type} (rs : List α) (f : α → Nat) (d : Nat)
    (h : ∀ i ∈ rs, d ≤ f i) : rs.length*d ≤ (rs.map f).sum := by
  induction rs with
  | nil => simp
  | cons a rs ih =>
    have ha := h a (by simp)
    have hr := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem cols_half {β : Type} (cs : List β) (f : β → Nat) (n : Nat)
    (h : ∀ i ∈ cs, 2*f i ≤ n) : 2*(cs.map f).sum ≤ cs.length*n := by
  induction cs with
  | nil => simp
  | cons a cs ih =>
    have ha := h a (by simp)
    have hc := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- Plotkin's counting inequality on the complement of a coordinate set.
    The omitted zero word changes the number of words from rs.length to
    rs.length+1 but contributes no ones to any column. -/
theorem projection_kernel_bound {α β : Type} (rs : List α) (cs : List β)
    (entry : α → β → Nat) (d : Nat)
    (weight : ∀ r ∈ rs, d ≤ (cs.map (entry r)).sum)
    (balance : ∀ c ∈ cs, 2 * (rs.map (fun r => entry r c)).sum ≤ rs.length + 1) :
    2*(rs.length*d) ≤ cs.length*(rs.length+1) := by
  have lo := rows_min rs (fun r => (cs.map (entry r)).sum) d weight
  have hi := cols_half cs (fun c => (rs.map (fun r => entry r c)).sum)
    (rs.length+1) balance
  change rs.length*d ≤ total rs cs entry at lo
  change 2*total cs rs (fun c r => entry r c) ≤ _ at hi
  rw [← swap rs cs entry] at hi
  exact Nat.le_trans (Nat.mul_le_mul_left 2 lo) hi

end NoisyDualCuts
