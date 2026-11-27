import Std

namespace ErasureHierarchy

/-- Each occupied point either agrees with the true restriction or has a
    certified wrong label. A point with both kinds of label is charged once. -/
theorem count_by_cases (xs : List ι) (hit agree bad : ι → Bool)
    (charge : ∀ i, hit i = true → agree i = true ∨ bad i = true) :
    xs.countP hit ≤ xs.countP agree + xs.countP bad := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.countP_cons]
    have chargeAt := charge i
    cases h : hit i <;> cases g : agree i <;> cases b : bad i <;> simp_all <;> omega

def best (score : α → Nat) : List α → Nat
  | [] => 0
  | a :: rest => max (score a) (best score rest)

private theorem own_le_best (score : α → Nat) {a : α} {menu : List α} (ha : a ∈ menu) :
    score a ≤ best score menu := by
  induction menu with
  | nil => simp at ha
  | cons head tail ih =>
    rcases List.mem_cons.mp ha with rfl | later
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

private theorem best_le (score : α → Nat) {menu : List α} {n : Nat}
    (h : ∀ a ∈ menu, score a ≤ n) : best score menu ≤ n := by
  induction menu with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
    exact Nat.max_le.mpr ⟨h head (by simp), ih (fun a ha => h a (by simp [ha]))⟩

structure Line (ι γ : Type) where
  points : List ι
  truth : ι → γ
  reported : ι → γ → Bool
  bad : ι → Bool
  sameCenter : List (ι → γ)
  wrongCenter : List (ι → γ)

def hits (s : Line ι γ) (f : ι → γ) := s.points.countP (fun t => s.reported t (f t))

/-- The finite-field root bound provides the agreement premise for two
    polynomial restrictions with different center values. -/
def Valid [DecidableEq γ] (s : Line ι γ) (degree : Nat) : Prop :=
  s.truth ∈ s.sameCenter ∧
  (∀ f ∈ s.wrongCenter, s.points.countP (fun t => decide (f t = s.truth t)) ≤ degree) ∧
  (∀ t a, s.reported t a = true → a ≠ s.truth t → s.bad t = true)

theorem line_scores [DecidableEq γ] (s : Line ι γ) (degree : Nat) (valid : Valid s degree) :
    hits s s.truth ≤ degree + (best (hits s) s.sameCenter - degree) ∧
    best (hits s) s.wrongCenter - degree ≤ s.points.countP s.bad := by
  obtain ⟨trueMem, intersect, err⟩ := valid
  have lower := own_le_best (hits s) trueMem
  have upper : best (hits s) s.wrongCenter ≤ degree + s.points.countP s.bad := by
    apply best_le
    intro f hf
    have split := count_by_cases s.points (fun t => s.reported t (f t))
      (fun t => decide (f t = s.truth t)) s.bad (by
        intro t accepted
        by_cases eq : f t = s.truth t
        · exact Or.inl (by simp [eq])
        · exact Or.inr (err t (f t) accepted eq))
    exact Nat.le_trans split (Nat.add_le_add_right (intersect f hf) _)
  omega

theorem total_scores [DecidableEq γ] (lines : List (Line ι γ)) (degree : Nat)
    (valid : ∀ s ∈ lines, Valid s degree) :
    (lines.map (fun s => hits s s.truth)).sum ≤ degree * lines.length +
      (lines.map (fun s => best (hits s) s.sameCenter - degree)).sum ∧
    (lines.map (fun s => best (hits s) s.wrongCenter - degree)).sum ≤
      (lines.map (fun s => s.points.countP s.bad)).sum := by
  induction lines with
  | nil => simp
  | cons s rest ih =>
    obtain ⟨lo, hi⟩ := line_scores s degree (valid s (by simp))
    obtain ⟨los, his⟩ := ih (fun a ha => valid a (by simp [ha]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

/-- The punctured affine lines through a point partition all other points.
    This counting step extracts a line with enough interpolation samples. -/
theorem some_line (lines : List α) (occupied : α → Nat) (degree : Nat)
    (dense : degree * lines.length < (lines.map occupied).sum) :
    ∃ line ∈ lines, degree < occupied line := by
  induction lines with
  | nil => simp at dense
  | cons line rest ih =>
    by_cases first : degree < occupied line
    · exact ⟨line, by simp, first⟩
    · simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_succ] at dense
      obtain ⟨l, member, enough⟩ := ih (by omega)
      exact ⟨l, by simp [member], enough⟩

end ErasureHierarchy
