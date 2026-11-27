import Std

namespace GeometricHistory

/-- Integer weights allow a sweep to remove old histogram entries. -/
def total {α : Type} : List α → (α → Int) → Int
  | [], _ => 0
  | p :: ps, f => f p + total ps f

theorem total_congr {α : Type} (ps : List α) (f g : α → Int)
    (h : ∀ p ∈ ps, f p = g p) : total ps f = total ps g := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [total]
    rw [h p (by simp), ih (fun t ht => h t (by simp [ht]))]

theorem total_zero {α : Type} (ps : List α) : total ps (fun _ => 0) = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [total, ih]

theorem total_add {α : Type} (ps : List α) (f g : α → Int) :
    total ps (fun p => f p + g p) = total ps f + total ps g := by
  induction ps with
  | nil => simp [total]
  | cons p ps ih => simp only [total, ih]; omega

/-- Counts from the independent coordinate histograms multiply on one slab. -/
theorem slab_product {α β : Type} (xs : List α) (ys : List β)
    (f : α → Int) (g : β → Int) :
    total xs (fun x => total ys (fun y => f x * g y)) = total xs f * total ys g := by
  have scaled (x : α) : total ys (fun y => f x * g y) = f x * total ys g := by
    induction ys with
    | nil => simp [total]
    | cons y ys ih => simp [total, ih, Int.mul_add]
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    simp only [total, Int.add_mul]
    rw [ih, scaled x]

/-- A common XOR flip permutes the histogram bins by its own inverse. -/
theorem flip_bin (v target mask : Nat) : v ^^^ mask = target ↔ v = target ^^^ mask := by
  constructor
  · intro heq
    rw [← heq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · intro heq
    rw [heq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem xor_right_inj (x y mask : Nat) : x ^^^ mask = y ^^^ mask ↔ x = y := by
  rw [flip_bin, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- A y-prefix with fewer free bits determines the coarser y-prefix
    used by x. After the shear this rectangle still has two prefix tests. -/
theorem ordered_prefix_shear (x y bx byy freeY extra : Nat) :
    (x >>> (freeY + extra) = bx ∧ y >>> freeY = byy) ↔
    (y >>> freeY = byy ∧ (x ^^^ y) >>> (freeY + extra) = bx ^^^ (byy >>> extra)) := by
  have coarser (h : y >>> freeY = byy) : y >>> (freeY + extra) = byy >>> extra := by
    rw [Nat.shiftRight_add, h]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨hy, by rw [Nat.shiftRight_xor_distrib, hx, coarser hy]⟩
  · rintro ⟨hy, hxy⟩
    rw [Nat.shiftRight_xor_distrib, coarser hy, xor_right_inj] at hxy
    exact ⟨hxy, hy⟩

/-- A diagonal-track interval becomes a stripe at the fixed second
    coordinate after (x,y) ↦ (y,x XOR y). -/
theorem diagonal_track_shear (x y offset : Nat) (inInterval : Nat → Prop) :
    (inInterval x ∧ y = x ^^^ offset) ↔
      (inInterval (y ^^^ offset) ∧ x ^^^ y = offset) := by
  constructor
  · rintro ⟨hx, rfl⟩
    constructor
    · simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using hx
    · rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · rintro ⟨hy, key⟩
    have ys : y = x ^^^ offset := by
      rw [← key, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rw [ys, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at hy
    exact ⟨hy, ys⟩

/-- A mask-domain remains a product domain when y fixes every bit fixed by x. -/
theorem mask_domain_shear (x y vx vy mx my : Nat) (included : my &&& mx = mx) :
    ((x &&& mx) = vx &&& mx ∧ (y &&& my) = vy &&& my) ↔
    ((y &&& my) = vy &&& my ∧ ((x ^^^ y) &&& mx) = (vx ^^^ vy) &&& mx) := by
  have coarser (hy : (y &&& my) = vy &&& my) : (y &&& mx) = vy &&& mx := by
    have h := congrArg (fun a : Nat => a &&& mx) hy
    simpa only [Nat.and_assoc, included] using h
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨hy, by rw [Nat.and_xor_distrib_right, Nat.and_xor_distrib_right, hx, coarser hy]⟩
  · rintro ⟨hy, hxy⟩
    rw [Nat.and_xor_distrib_right, Nat.and_xor_distrib_right, coarser hy, xor_right_inj] at hxy
    exact ⟨hxy, hy⟩

def hit (value target : Nat) : Int := if value = target then 1 else 0

def histogram {α : Type} (ps : List α) (value : α → Nat) (target : Nat) : Int :=
  total ps (fun p => hit (value p) target)

theorem histogram_flip {α : Type} (ps : List α) (value : α → Nat) (target mask : Nat) :
    histogram ps (fun p => value p ^^^ mask) target = histogram ps value (target ^^^ mask) := by
  apply total_congr
  intro p _
  simp only [hit, flip_bin]

def changeOn {α : Type} (ps : List α) (key : α → Nat) (before after : α → Int)
    (d : Nat) : Int :=
  total ps (fun p => if key p = d then after p - before p else 0)

/-- Sum changes on distinct named fibers. Positions outside the named
    fibers contribute nothing even if they appear multiple times in the scan. -/
theorem sum_fibers {α : Type} (ps : List α) (offsets : List Nat)
    (key : α → Nat) (before after : α → Int) (unique : offsets.Nodup) :
    total offsets (changeOn ps key before after) =
      total ps (fun p => if key p ∈ offsets then after p - before p else 0) := by
  induction offsets with
  | nil => simp [total, total_zero]
  | cons d ds ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp unique
    simp only [total, ih rest, changeOn]
    rw [← total_add]
    apply total_congr
    intro p _
    by_cases same : key p = d
    · simp [same, fresh]
    · by_cases present : key p ∈ ds <;> simp [same, present]

/-- Equality of the histogram from a rectangle sweep plus all XOR-track
    corrections, on an arbitrary list of allowed positions. -/
theorem corrected_histogram (ps : List (Nat × Nat)) (offsets : List Nat)
    (base actual : Nat × Nat → Nat) (target : Nat) (unique : offsets.Nodup)
    (outside : ∀ p ∈ ps, p.1 ^^^ p.2 ∉ offsets → actual p = base p) :
    histogram ps actual target =
      histogram ps base target +
      total offsets (changeOn ps (fun p => p.1 ^^^ p.2)
        (fun p => hit (base p) target) (fun p => hit (actual p) target)) := by
  rw [sum_fibers _ _ _ _ _ unique]
  unfold histogram
  rw [← total_add]
  apply total_congr
  intro p hp
  by_cases named : p.1 ^^^ p.2 ∈ offsets
  · simp only [if_pos named]
    omega
  · simp [named, outside p hp named]

end GeometricHistory
