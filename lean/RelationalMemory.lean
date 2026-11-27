import Std

namespace RelationalMemory

/-- All pre-cells, including sparse pins, can be filled once a common
    alignment, anchor rows and register states have been chosen. -/
theorem extendIndependent {I W : Type} (allowed : I → W → Prop)
    (pin : I → Option W) :
    (∃ memory : I → W, (∀ i, allowed i (memory i)) ∧
      ∀ i x, pin i = some x → memory i = x) ↔
    ∀ i, ∃ x, allowed i x ∧ ∀ y, pin i = some y → x = y := by
  constructor
  · rintro ⟨m, hm, hp⟩ i
    exact ⟨m i, hm i, hp i⟩
  · intro h
    classical
    let m := fun i => Classical.choose (h i)
    refine ⟨m, ?_, ?_⟩
    · intro i
      exact (Classical.choose_spec (h i)).1
    · intro i x hx
      exact (Classical.choose_spec (h i)).2 x hx

abbrev Row (I : Type) := (I → Bool) × Bool

def dot {I : Type} (a : I → Bool) : List I → Bool
  | [] => false
  | x :: xs => xor (a x) (dot a xs)

def addRow {I : Type} (r s : Row I) : Row I :=
  (fun i => xor (r.1 i) (s.1 i), xor r.2 s.2)

def sumRows {I : Type} : List (Row I) → Row I
  | [] => (fun _ => false, false)
  | r :: rs => addRow r (sumRows rs)

/-- A Boolean tag is encoded by the finite list of its active coordinates. -/
def satisfied {I : Type} (tag : List I) (r : Row I) : Prop :=
  dot r.1 tag = r.2

private theorem xorSwap (a b c d : Bool) :
    xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem dotAdd {I : Type} (a b : I → Bool) (tag : List I) :
    dot (fun i => xor (a i) (b i)) tag = xor (dot a tag) (dot b tag) := by
  induction tag with
  | nil => rfl
  | cons x xs ih =>
    simp only [dot, ih]
    exact xorSwap _ _ _ _

theorem dotZero {I : Type} (tag : List I) : dot (fun _ : I => false) tag = false := by
  induction tag with
  | nil => rfl
  | cons x xs ih => simp [dot, ih]

theorem sumSatisfied {I : Type} (rs : List (Row I)) (tag : List I)
    (holds : ∀ r ∈ rs, satisfied tag r) : satisfied tag (sumRows rs) := by
  induction rs with
  | nil => exact dotZero tag
  | cons r rs ih =>
    have one := holds r (by simp)
    have rest := ih (fun u hu => holds u (by simp [hu]))
    change dot r.1 tag = r.2 at one
    change dot (sumRows rs).1 tag = (sumRows rs).2 at rest
    change dot (fun i => xor (r.1 i) ((sumRows rs).1 i)) tag =
      xor r.2 (sumRows rs).2
    rw [dotAdd, one, rest]

/-- Reconstructing both the coefficient vector and right side from anchor
    rows transports any satisfying tag to the entire row family. -/
theorem reconstructed {I J : Type} (anchors : List (Row I)) (rows : J → Row I)
    (tag : List I) (holds : ∀ r ∈ anchors, satisfied tag r)
    (span : ∀ j, ∃ terms : List (Row I),
      (∀ r ∈ terms, r ∈ anchors) ∧ sumRows terms = rows j) :
    ∀ j, satisfied tag (rows j) := by
  intro j
  obtain ⟨terms, hm, he⟩ := span j
  rw [← he]
  exact sumSatisfied terms tag (fun r hr => holds r (hm r hr))

theorem inconsistency {I : Type} (rs : List (Row I))
    (zeroCol : ∀ i, (sumRows rs).1 i = false) (bad : (sumRows rs).2 = true) :
    ¬ ∃ tag : List I, ∀ r ∈ rs, satisfied tag r := by
  rintro ⟨tag, ht⟩
  have h := sumSatisfied rs tag ht
  change dot (sumRows rs).1 tag = (sumRows rs).2 at h
  have zero : (sumRows rs).1 = (fun _ : I => false) := funext zeroCol
  rw [zero, dotZero, bad] at h
  contradiction

/-- A certificate excluding a state must mention each index at which
    changing only that index can restore relatedness. -/
theorem mustCoverRepairs {I W : Type} (checked : I → Prop) (x : I → W)
    (related : (I → W) → Prop)
    (rejects : ∀ y, (∀ j, checked j → y j = x j) → ¬ related y)
    (repair : ∀ i, ∃ y, related y ∧ ∀ j, j ≠ i → y j = x j) :
    ∀ i, checked i := by
  classical
  intro i
  apply Classical.byContradiction
  intro hi
  obtain ⟨y, hy, agrees⟩ := repair i
  exact rejects y (fun j hj => agrees j (fun he => hi (he ▸ hj))) hy

end RelationalMemory
