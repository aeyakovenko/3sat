import Std

namespace SlopeSwitch

abbrev Term := Nat × Nat
abbrev Pattern := List Term

/-- Terms are added over F₂, so repeated positions cancel when tested. -/
def parity (xs : List α) (test : α → Bool) : Bool :=
  xs.foldr (fun x b => test x ^^ b) false

theorem parity_append (xs ys : List α) (test : α → Bool) :
    parity (xs ++ ys) test = (parity xs test ^^ parity ys test) := by
  induction xs with
  | nil => simp [parity]
  | cons a as ih =>
    change (test a ^^ parity (as ++ ys) test) = ((test a ^^ parity as test) ^^ parity ys test)
    rw [ih, Bool.xor_assoc]

theorem parity_map (xs : List α) (g : α → β) (test : β → Bool) :
    parity (xs.map g) test = parity xs (fun x => test (g x)) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change (test (g a) ^^ parity (as.map g) test) = (test (g a) ^^ parity as (fun x => test (g x)))
    rw [ih]

def view (xs : Pattern) (s : Nat) (test : Nat → Bool) :=
  parity xs fun z => test (z.1 + s*z.2)

def Invisible (xs : Pattern) (s : Nat) := ∀ test, view xs s test = false

/-- Multiplication by Y + X^q. -/
def extend (q : Nat) (xs : Pattern) : Pattern :=
  xs.map (fun z => (z.1, z.2+1)) ++ xs.map (fun z => (z.1+q, z.2))

theorem view_extend (q s : Nat) (xs : Pattern) (test : Nat → Bool) :
    view (extend q xs) s test =
      (view xs s (fun v => test (v+s)) ^^ view xs s (fun v => test (v+q))) := by
  unfold view extend
  rw [parity_append, parity_map, parity_map]
  simp only [Nat.mul_succ, ← Nat.add_assoc]
  congr 2
  funext z
  congr 1
  omega

theorem new_slope (q : Nat) (xs : Pattern) : Invisible (extend q xs) q := by
  intro test
  rw [view_extend, Bool.xor_self]

theorem keep_slope (q s : Nat) (xs : Pattern) (h : Invisible xs s) :
    Invisible (extend q xs) s := by
  intro test
  rw [view_extend, h, h]
  rfl

def ghost : List Nat → Pattern
  | [] => [(0,0)]
  | q :: rest => extend q (ghost rest)

theorem invisible_at_all (slopes : List Nat) (s : Nat) (mem : s ∈ slopes) :
    Invisible (ghost slopes) s := by
  induction slopes with
  | nil => simp at mem
  | cons q qs ih =>
    rcases List.mem_cons.mp mem with e | h
    · subst s
      exact new_slope q _
    · exact keep_slope _ _ _ (ih h)

theorem row_zero_survives (slopes : List Nat) (pos : ∀ q ∈ slopes, 0 < q) :
    parity (ghost slopes) (fun z => decide (z.1 = 0)) = true := by
  induction slopes with
  | nil => decide +revert
  | cons q qs ih =>
    have hq := pos q (by simp)
    have old := ih (fun p hp => pos p (by simp [hp]))
    simp only [ghost, extend, parity_append, parity_map]
    rw [old]
    have zero : ∀ xs : Pattern, parity xs (fun z => decide (z.1 + q = 0)) = false := by
      intro xs
      induction xs with
      | nil => rfl
      | cons a as ih' =>
        have h : a.1 + q ≠ 0 := by omega
        change (decide (a.1+q = 0) ^^ parity as _) = false
        rw [ih']
        simp [h]
    rw [zero]
    rfl

end SlopeSwitch
