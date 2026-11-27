import Std

namespace DefaultEscapes

/-- Unfold a finite acyclic game. Each choice can use the remaining budget
    to determine which port is the default. -/
inductive Game where
  | terminal (value : Bool)
  | challenge (a b : Game)
  | choice (rightDefault : Nat → Bool) (a b : Game)

def truth : Game → Bool
  | .terminal v => v
  | .challenge a b => truth a && truth b
  | .choice _ a b => truth a || truth b

def win : Game → Nat → Bool
  | .terminal v, _ => v
  | .challenge a b, i => win a i && win b i
  | .choice right a b, 0 => if right 0 then win b 0 else win a 0
  | .choice right a b, i+1 =>
      if right (i+1) then win b (i+1) || win a i
      else win a (i+1) || win b i

/-- A successful existential refutation selects one challenger port,
    recursively refutes the alternative while saving the default, then
    continues to the default without increasing the stack. -/
def refute : Game → Nat → Bool
  | .terminal v, _ => !v
  | .challenge a b, i => refute a i || refute b i
  | .choice right a b, 0 => if right 0 then refute b 0 else refute a 0
  | .choice right a b, i+1 =>
      if right (i+1) then refute a i && refute b (i+1)
      else refute b i && refute a (i+1)

theorem refute_eq (g : Game) (i : Nat) : refute g i = !win g i := by
  induction g generalizing i with
  | terminal v => rfl
  | challenge a b ha hb =>
    simp [win, refute, ha, hb, Bool.not_and]
  | choice right a b ha hb =>
    cases i with
    | zero => cases hh : right 0 <;> simp [win, refute, hh, ha, hb]
    | succ j =>
      cases hh : right (j+1) <;>
        simp [win, refute, hh, ha, hb, Bool.not_or, Bool.and_comm]

theorem win_sound (g : Game) (i : Nat) : win g i = true → truth g = true := by
  induction g generalizing i with
  | terminal v => exact id
  | challenge a b ha hb =>
    simp only [win, truth, Bool.and_eq_true]
    rintro ⟨wa, wb⟩
    exact ⟨ha _ wa, hb _ wb⟩
  | choice right a b ha hb =>
    simp only [truth, Bool.or_eq_true]
    cases i with
    | zero =>
      cases h : right 0 <;> simp only [win, h, Bool.false_eq_true, ↓reduceIte]
      · exact fun w => Or.inl (ha _ w)
      · exact fun w => Or.inr (hb _ w)
    | succ j =>
      cases h : right (j+1) <;>
        simp only [win, h, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
      · exact fun wboth => Or.elim wboth (fun w => Or.inl (ha _ w)) (fun w => Or.inr (hb _ w))
      · exact fun wboth => Or.elim wboth (fun w => Or.inr (hb _ w)) (fun w => Or.inl (ha _ w))

/-- A larger actual budget can simulate a strategy using a smaller virtual
    budget. While they differ, any single move is affordable. -/
theorem win_succ (g : Game) (i : Nat) : win g i = true → win g (i+1) = true := by
  induction g generalizing i with
  | terminal v => exact id
  | challenge a b ha hb =>
    simp only [win, Bool.and_eq_true]
    rintro ⟨wa, wb⟩
    exact ⟨ha _ wa, hb _ wb⟩
  | choice right a b ha hb =>
    intro hw
    cases i with
    | zero =>
      have a01 := ha 0
      have b01 := hb 0
      cases first : right 0 <;> cases next : right 1 <;>
        simp [win, first, next] at hw ⊢ <;> solve_by_elim [Or.inl, Or.inr]
    | succ j =>
      have a01 := ha j
      have b01 := hb j
      have a12 := ha (j+1)
      have b12 := hb (j+1)
      cases first : right (j+1) <;> cases next : right (j+2) <;>
        simp [win, first, next] at hw ⊢ <;> rcases hw with hw | hw <;>
          solve_by_elim [Or.inl, Or.inr]

/-- Assigning the answer to the lighter prediction class means that the
    chosen class's doubled weight adds at most half the old total. -/
theorem weightedRound (old chosen : Nat) (light : 2*chosen ≤ old) :
    2*(old+chosen) ≤ 3*old := by omega

/-- The correction list determines the remaining budget before a stage, even
    if we extend the forecast process after budget exhaustion. -/
def priorErrors (error : Nat → Bool) : Nat → Nat
  | 0 => 0
  | j+1 => priorErrors error j + (if error j then 1 else 0)

def remaining (error : Nat → Bool) (initial : Nat) : Nat → Nat
  | 0 => initial
  | j+1 => if error j then remaining error initial j - 1
           else remaining error initial j

theorem remaining_eq (error : Nat → Bool) (initial j : Nat) :
    remaining error initial j = initial - priorErrors error j := by
  induction j with
  | zero => simp [remaining, priorErrors]
  | succ j ih =>
    cases h : error j <;> simp [remaining, priorErrors, h, ih] <;> omega

/-- An ordinary circuit can recover any individual truth-table bit using the
    predictor and the prefix rank and membership bit of the error list. -/
theorem recoverBit (target error : Nat → Bool) (predict : Nat → Nat → Bool)
    (initial j : Nat)
    (marks : ∀ k, error k = (target k != predict k (remaining error initial k))) :
    (predict j (initial - priorErrors error j) != error j) = target j := by
  rw [← remaining_eq, marks j]
  cases h : target j <;> cases h' : predict j (remaining error initial j) <;> decide

end DefaultEscapes
