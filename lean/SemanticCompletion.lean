import Std

namespace SemanticCompletion

/-- The free addresses form an initial segment of the as yet unprinted addresses. -/
def FirstGaps (free printed : Nat → Prop) : Prop :=
  (∀ x, free x → ¬ printed x) ∧
  (∀ x y, x < y → free y → ¬ printed x → free x)

theorem initially_free (capacity : Nat) :
    FirstGaps (fun x => x < capacity) (fun _ => False) := by
  exact ⟨by simp, fun x y xy y_free _ => Nat.lt_trans xy y_free⟩

/-- When the original name produces a free value, take it. Otherwise take the
    largest free value. The input event may also be a timeout. -/
theorem update {free printed : Nat → Prop} [DecidablePred free]
    (old : FirstGaps free printed) (event : Option Nat) (largest : Nat)
    (top : ∀ y, free y → y ≤ largest) :
    let choice := match event with
      | none => largest
      | some v => if free v then v else largest
    FirstGaps (fun y => free y ∧ y ≠ choice)
      (fun y => printed y ∨ event = some y) := by
  intro choice
  have priority (x : Nat) (hx : free x) (produced : event = some x) :
      x = choice := by simp [choice, produced, hx]
  have fallback (absent : event ≠ some choice) : choice = largest := by
    cases event with
    | none => rfl
    | some v =>
      by_cases hv : free v
      · simp [choice, hv] at absent
      · simp [choice, hv]
  constructor
  · intro x hx printed_now
    rcases printed_now with past | current
    · exact old.1 x hx.1 past
    · exact hx.2 (priority x hx.1 current)
  · intro x y xy hy missing
    have x_free := old.2 x y xy hy.1 (fun h => missing (Or.inl h))
    refine ⟨x_free, ?_⟩
    intro eq_choice
    have absent : event ≠ some choice := by
      rw [← eq_choice]
      exact fun h => missing (Or.inr h)
    have upper := top y hy.1
    have eq_top := fallback absent
    omega

theorem unique_gap {free printed : Nat → Prop} {w : Nat}
    (invariant : FirstGaps free printed) (sole : ∀ x, free x ↔ x = w) :
    ¬ printed w ∧ ∀ x, x < w → printed x := by
  classical
  have hw := (sole w).2 rfl
  refine ⟨invariant.1 w hw, ?_⟩
  intro x hx
  exact Classical.byContradiction fun absent =>
    (Nat.ne_of_lt hx) ((sole x).1 (invariant.2 x w hx hw absent))

def FirstMissing {ι : Type} (f : ι → Option Nat) (x : Nat) : Prop :=
  (∀ i, f i ≠ some x) ∧ (∀ y, y < x → ∃ i, f i = some y)

def hide {ι : Type} (f : ι → Option Nat) (x : Nat) (i : ι) : Option Nat :=
  if f i = some x then none else f i

theorem hiding_makes_first {ι : Type} {f : ι → Option Nat} {x w : Nat}
    (hw : FirstMissing f w) (hx : x < w) : FirstMissing (hide f x) x := by
  constructor
  · intro i
    by_cases h : f i = some x <;> simp [hide, h]
  · intro y hy
    obtain ⟨i, hi⟩ := hw.2 y (Nat.lt_trans hy hx)
    refine ⟨i, ?_⟩
    simp [hide, hi, Nat.ne_of_lt hy]

theorem must_read_producer {ι : Type} {f : ι → Option Nat} {x w : Nat}
    (hw : FirstMissing f w) (hx : x < w) (reads : List ι)
    (sound : ∀ g : ι → Option Nat,
      (∀ i ∈ reads, g i = f i) → ¬ FirstMissing g x) :
    ∃ i ∈ reads, f i = some x := by
  apply Classical.byContradiction
  intro absent
  apply sound (hide f x) _ (hiding_makes_first hw hx)
  intro i hi
  have h : f i ≠ some x := fun same => absent ⟨i, hi, same⟩
  simp [hide, h]

end SemanticCompletion
