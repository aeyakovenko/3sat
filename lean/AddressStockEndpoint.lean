import Std

namespace AddressStockEndpoint

/-- The fixed successor among nonbranch slots. A missing successor ends the
    stretch at a conditional branch or at a verdict. Direct jumps are allowed. -/
inductive Stretch {α : Type} (next : α → Option α) : α → List α → Prop where
  | last (x) : next x = none → Stretch next x [x]
  | more (x) {y xs} : next x = some y → Stretch next y xs → Stretch next x (x :: xs)

private theorem unique_stretch {l r : List α} (h : Stretch next x l)
    (k : Stretch next x r) : l = r := by
  induction h generalizing r with
  | last x hx =>
    cases k with
    | last => rfl
    | more _ hk _ => simp_all
  | more x hx _ ih =>
    cases k with
    | last _ hk => simp_all
    | more _ hk k =>
      simp_all
      exact ih k

private theorem member_stretch {xs : List α} (h : Stretch next x xs) {z : α}
    (hz : z ∈ xs) : ∃ ys, Stretch next z ys ∧ ys.length ≤ xs.length := by
  induction h with
  | last x hx =>
    have hzx : z = x := by simpa using hz
    subst z
    exact ⟨_, .last x hx, Nat.le_refl _⟩
  | more x hx run ih =>
    rcases List.mem_cons.mp hz with hzx | hz
    · subst z
      exact ⟨_, .more x hx run, Nat.le_refl _⟩
    · obtain ⟨ys, hys, size⟩ := ih hz
      exact ⟨ys, hys, Nat.le_trans size (by simp)⟩

theorem stretch_nodup {xs : List α} (h : Stretch next x xs) : xs.Nodup := by
  induction h with
  | last => simp
  | more x hx run ih =>
    refine List.nodup_cons.mpr ⟨?_, ih⟩
    intro occurs
    obtain ⟨ys, hy, hySize⟩ := member_stretch run occurs
    rw [unique_stretch hy (.more x hx run)] at hySize
    simp at hySize
    omega

/-- At most as many distinct visited slots as entries in the available list. -/
private theorem count_slots [DecidableEq α] (xs slots : List α) (uniq : xs.Nodup)
    (inside : ∀ z ∈ xs, z ∈ slots) : xs.length ≤ slots.length := by
  induction xs generalizing slots with
  | nil => simp
  | cons x tail ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp uniq
    have present := inside x (by simp)
    have pos := List.length_pos_of_mem present
    have smaller := ih (slots.erase x) rest (by
      intro z hz
      have hne : z ≠ x := fun eq => fresh (eq ▸ hz)
      exact (List.mem_erase_of_ne hne).2 (inside z (by simp [hz])))
    rw [List.length_erase_of_mem present] at smaller
    simp
    omega

theorem stretch_bound [DecidableEq α] (slots : List α) (run : Stretch next x xs)
    (inside : ∀ z ∈ xs, z ∈ slots) : xs.length ≤ slots.length :=
  count_slots xs slots (stretch_nodup run) inside

/-- Sum the nonbranch lengths of the (possibly empty) stretches separated by
    the b charged conditional instructions. -/
theorem total_stretches (lengths : List Nat) (cap : ∀ d ∈ lengths, d ≤ C)
    (count : lengths.length = b + 1) : lengths.sum ≤ C * (b + 1) := by
  rw [← count]
  clear count
  induction lengths with
  | nil => simp
  | cons d ds ih =>
    have hd := cap d (by simp)
    have tail := ih (fun e he => cap e (by simp [he]))
    simpa [Nat.mul_succ, Nat.add_comm] using Nat.add_le_add tail hd

def threshold (C h r b₀ : Nat) : Nat := (C + 1) * (h + r + 2*C) + C + 2*C*b₀

theorem endpoint_margin (run : U + b ≤ T) (stretches : U ≤ C*(b+1))
    (stock : 2*m ≤ U + (h+r+2*C)) (fast : T ≤ 2*(m+b₀)) :
    2*m ≤ threshold C h r b₀ := by
  have timeCap := Nat.mul_le_mul_left C (Nat.le_trans run fast)
  simp only [Nat.mul_add, Nat.mul_comm C 2, ← Nat.mul_assoc] at timeCap
  rw [Nat.mul_add, Nat.mul_one] at stretches
  have stockCap := Nat.mul_le_mul_left (C+1) stock
  rw [Nat.mul_add, Nat.add_mul C 1, Nat.one_mul, Nat.add_mul C 1, Nat.one_mul] at stockCap
  have rearrange : C * (2*m) = (2*C)*m := by ac_rfl
  rw [rearrange] at stockCap
  unfold threshold
  omega

/-- The exact first integer m passing this sufficient strict-margin test. -/
def firstMarked (C h r b₀ : Nat) : Nat := threshold C h r b₀ / 2 + 1

theorem first_iff : firstMarked C h r b₀ ≤ m ↔ threshold C h r b₀ < 2*m := by
  unfold firstMarked
  omega

theorem threshold_step :
    threshold (C+1) h r b₀ = threshold C h r b₀ + (4*C+h+r+5+2*b₀) := by
  simp only [threshold, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

/-- Increasing m by the rounded-up half of the threshold increase works for
    every replacement program with one extra slot. -/
theorem lift_one_slot (large : firstMarked C h r b₀ ≤ m)
    (more : m + (4*C+h+r+5+2*b₀+1)/2 ≤ m') : firstMarked (C+1) h r b₀ ≤ m' := by
  apply first_iff.mpr
  rw [threshold_step]
  have before := first_iff.mp large
  omega

theorem beyond_two (run : U + b ≤ T) (stretches : U ≤ C*(b+1))
    (stock : 2*m ≤ U + (h+r+2*C)) (words : nWords ≤ m+b₀)
    (large : firstMarked C h r b₀ ≤ m) : 2*nWords < T := by
  have marg := first_iff.mp large
  apply Classical.byContradiction
  intro fail
  have contra := endpoint_margin run stretches stock (show T ≤ 2*(m+b₀) by omega)
  omega

end AddressStockEndpoint
