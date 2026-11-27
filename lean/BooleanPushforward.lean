import Std

namespace BooleanPushforward

def Word : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Word n

/-- Coefficient of a squarefree monomial in the unique multilinear
    expression for an arbitrary Boolean function. -/
def coeff : (n : Nat) → (Word n → Bool) → Word n → Bool
  | 0, f, _ => f ()
  | n+1, f, (false, m) => coeff n (fun z => f (false, z)) m
  | n+1, f, (true, m) =>
    xor (coeff n (fun z => f (false, z)) m)
        (coeff n (fun z => f (true, z)) m)

theorem coeff_zero (n : Nat) (m : Word n) : coeff n (fun _ => false) m = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b,m⟩ := m
    cases b <;> simp [coeff, ih]

private theorem xor_four :
    ∀ (a b c d : Bool), xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by decide

theorem coeff_xor (n : Nat) (f g : Word n → Bool) (m : Word n) :
    coeff n (fun z => xor (f z) (g z)) m = xor (coeff n f m) (coeff n g m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b,m⟩ := m
    cases b with
    | false => exact ih _ _ _
    | true =>
      simp only [coeff]
      rw [ih (fun z => f (false,z)) (fun z => g (false,z)),
          ih (fun z => f (true,z)) (fun z => g (true,z))]
      apply xor_four

def delta : (n : Nat) → Word n → Word n → Bool
  | 0, _, _ => true
  | n+1, (v,y), (b,z) => (v == b) && delta n y z

/-- A point contributes to the coefficient indexed by m if its
    nonzero coordinates are contained in m. -/
def contained : (n : Nat) → Word n → Word n → Bool
  | 0, _, _ => true
  | n+1, (v,y), (b,m) => (!v || b) && contained n y m

theorem coeff_delta (n : Nat) (y m : Word n) :
    coeff n (delta n y) m = contained n y m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨v,y⟩ := y
    obtain ⟨b,m⟩ := m
    cases v <;> cases b <;> simp [coeff, delta, contained, ih, coeff_zero]

def push (n : Nat) : List (Word n × Bool) → Word n → Bool
  | [], _ => false
  | (y,w) :: rest, z => xor (w && delta n y z) (push n rest z)

def atMask (n : Nat) : List (Word n × Bool) → Word n → Bool
  | [], _ => false
  | (y,w) :: rest, m => xor (w && contained n y m) (atMask n rest m)

/-- Exact coefficient of the parity pushforward of any list of weighted
    observations. Duplicate output points are counted with multiplicity. -/
theorem coeff_push (n : Nat) (xs : List (Word n × Bool)) (m : Word n) :
    coeff n (push n xs) m = atMask n xs m := by
  induction xs with
  | nil => exact coeff_zero n m
  | cons entry rest ih =>
    obtain ⟨y,w⟩ := entry
    change coeff n (fun z => xor (w && delta n y z) (push n rest z)) m = _
    rw [coeff_xor, ih]
    cases w <;> simp [atMask, coeff_zero, coeff_delta]

def total : (n : Nat) → (Word n → Bool) → Bool
  | 0, f => f ()
  | n+1, f => xor (total n (fun z => f (false,z))) (total n (fun z => f (true,z)))

def monomial : (n : Nat) → Word n → Word n → Bool
  | 0, _, _ => true
  | n+1, (b,m), (v,z) => (!b || v) && monomial n m z

def fullMask : (n : Nat) → Word n → Bool
  | 0, _ => true
  | n+1, (b,m) => b && fullMask n m

theorem total_zero (n : Nat) : total n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [total, ih]

/-- Summation over all Boolean inputs annihilates each monomial
    missing a coordinate. -/
theorem total_monomial (n : Nat) (m : Word n) :
    total n (monomial n m) = fullMask n m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b,m⟩ := m
    cases b <;> simp [total, monomial, fullMask, ih, total_zero]

end BooleanPushforward
