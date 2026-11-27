import Std

namespace FactoredLookup

/-- Coefficients of 1 and α in the binary field with α² = 1 + α. -/
abbrev F4 := Bool × Bool

def plus (x y : F4) : F4 := (x.1 ^^ y.1, x.2 ^^ y.2)
def times (x y : F4) : F4 :=
  ((x.1 && y.1) ^^ (x.2 && y.2),
   (x.1 && y.2) ^^ (x.2 && y.1) ^^ (x.2 && y.2))
def bit (b : Bool) : F4 := (b, false)
def alpha : F4 := (false, true)
def oneMinusAlpha : F4 := (true, true)

/-- The multilinear lookup with every field coordinate equal to α. -/
def evaluate : Nat → (List Bool → Bool) → F4
  | 0, f => bit (f [])
  | n + 1, f =>
    plus (times oneMinusAlpha (evaluate n (fun x => f (false :: x))))
         (times alpha (evaluate n (fun x => f (true :: x))))

def parity : Nat → (List Bool → Bool) → Bool
  | 0, f => f []
  | n + 1, f =>
    parity n (fun x => f (false :: x)) ^^ parity n (fun x => f (true :: x))

/-- Reject incomplete or equal pairs, otherwise pass the first bit on to f. -/
def paired (f : List Bool → Bool) : List Bool → Bool
  | [] => f []
  | [_] => false
  | a :: b :: rest =>
    if a == b then false else paired (fun x => f (a :: x)) rest

private theorem dead (n : Nat) : evaluate n (fun _ => false) = bit false := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [evaluate, ih]; rfl

private theorem twoBits (a b : Bool) :
    plus
      (times oneMinusAlpha
        (plus (times oneMinusAlpha (bit false)) (times alpha (bit a))))
      (times alpha
        (plus (times oneMinusAlpha (bit b)) (times alpha (bit false)))) =
    bit (a ^^ b) := by
  cases a <;> cases b <;> rfl

theorem pairedLookup (n : Nat) (f : List Bool → Bool) :
    evaluate (2*n) (paired f) = bit (parity n f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega]
    simp only [evaluate, paired, Bool.false_beq, Bool.true_beq, Bool.not_false,
      Bool.not_true, Bool.false_eq_true, if_false, if_true, dead, ih, parity]
    exact twoBits _ _

/-- Apply the append payloads in proposed chronological order. -/
def replayWrites {α : Type} (base : Nat → α) : List (Nat × α) → Nat → α
  | [] => base
  | (k, v) :: xs => replayWrites (fun j => if j = k then v else base j) xs

/-- Last payload for a slot in the proposed chronology. -/
def latest {α : Type} (i : Nat) : List (Nat × α) → Option α
  | [] => none
  | (k, v) :: xs =>
    match latest i xs with
    | some w => some w
    | none => if i = k then some v else none

/-- Looking up a slot can bypass replay, even for inconsistent payloads. -/
theorem readSlot {α : Type} (base : Nat → α) (writes : List (Nat × α)) (i : Nat) :
    replayWrites base writes i = (latest i writes).getD (base i) := by
  induction writes generalizing base with
  | nil => rfl
  | cons payload rest ih =>
    obtain ⟨k,v⟩ := payload
    simp only [replayWrites, ih, latest]
    cases past : latest i rest with
    | some w => rfl
    | none => split <;> simp_all

end FactoredLookup
