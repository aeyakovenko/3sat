import Std

/-! Same-length calibration for opposite verdicts with at most three observable colors. -/
namespace ThreeSignatureCalibration

def decidePair (noColor yesColor file mate : Fin 3) : Bool :=
  if file = noColor then false
  else if file = yesColor then true
  else decide (mate = noColor)

private theorem remaining_colors : ∀ a b c d : Fin 3,
    a ≠ b → c ≠ a → c ≠ b → c ≠ d → d = a ∨ d = b := by decide

theorem calibrated (label : Fin 3 → Bool) (n y f g : Fin 3)
    (hn : label n = false) (hy : label y = true) (opp : label g = !(label f)) :
    decidePair n y f g = label f := by
  have n_ne_y : n ≠ y := by intro h; subst y; simp [hn] at hy
  have f_ne_g : f ≠ g := by
    intro h
    subst g
    cases hbit : label f <;> simp [hbit] at opp
  by_cases fn : f = n
  · simp [decidePair, fn, hn]
  by_cases fy : f = y
  · simp [decidePair, fn, fy, hy, Ne.symm n_ne_y]
  obtain gn | gy := remaining_colors n y f g n_ne_y fn fy f_ne_g
  · subst g
    cases hbit : label f <;> simp_all [decidePair]
  · subst g
    have y_ne_n : y ≠ n := Ne.symm n_ne_y
    cases hbit : label f <;> simp_all [decidePair]

/-- Comparable YES-sets give the same orientation to every oppositely labelled pair. -/
theorem chain_orientation {A : Type} (d e : A → Bool) (p q : A)
    (order : (∀ x, d x = true → e x = true) ∨ (∀ x, e x = true → d x = true))
    (dOpp : d q = !(d p)) (eOpp : e q = !(e p)) : d p = e p := by
  cases hp : d p <;> cases ep : e p <;> try rfl
  · have dq : d q = true := by simp [dOpp, hp]
    have eq : e q = false := by simp [eOpp, ep]
    rcases order with de | ed
    · have h := de q dq
      simp [eq] at h
    · have h := ed p ep
      simp [hp] at h
  · have dq : d q = false := by simp [dOpp, hp]
    have eq : e q = true := by simp [eOpp, ep]
    rcases order with de | ed
    · have h := de p hp
      simp [ep] at h
    · have h := ed q eq
      simp [dq] at h

/-- Four possible reports can describe a query in both possible truth worlds. -/
def fourColor (query : Bool → Bool) : Bool × Bool := (query false, query true)

def coordinate (world : Bool) (color : Bool × Bool) : Bool :=
  if world then color.2 else color.1

theorem both_worlds (world : Bool) (query : Bool → Bool) :
    coordinate world (fourColor query) = query world := by cases world <;> rfl

theorem indistinguishable (recover : ((Bool → Bool) → Bool × Bool) → Bool) :
    ∃ world : Bool, recover fourColor ≠ world := by
  cases h : recover fourColor
  · exact ⟨true, by simp [h]⟩
  · exact ⟨false, by simp [h]⟩

end ThreeSignatureCalibration
