import Std

namespace AdaptiveHashTables

/-- Sum f(weight) over all binary vectors of a given length. -/
def cubeSum : Nat → (Nat → Nat) → Nat
  | 0, f => f 0
  | n+1, f => cubeSum n f + cubeSum n (fun i => f (i+1))

private theorem total (n : Nat) : cubeSum n (fun _ => 1) = 2^n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [cubeSum, ih, Nat.pow_succ]; omega

private theorem add (n : Nat) (f g : Nat → Nat) :
    cubeSum n (fun i => f i + g i) = cubeSum n f + cubeSum n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [cubeSum]
    rw [ih f g, ih (fun i => f (i+1)) (fun i => g (i+1))]
    omega

private theorem mono (n : Nat) (f g : Nat → Nat) (h : ∀ i, i ≤ n → f i ≤ g i) :
    cubeSum n f ≤ cubeSum n g := by
  induction n generalizing f g with
  | zero => exact h 0 (by omega)
  | succ n ih =>
    exact Nat.add_le_add (ih f g (fun i hi => h i (by omega)))
      (ih (fun i => f (i+1)) (fun i => g (i+1)) (fun i hi => h (i+1) (by omega)))

private theorem complement (n : Nat) (f g : Nat → Nat)
    (mirror : ∀ i, i ≤ n → f i = g (n-i)) : cubeSum n f = cubeSum n g := by
  induction n generalizing f g with
  | zero => exact mirror 0 (by omega)
  | succ n ih =>
    have a := ih f (fun i => g (i+1)) (by
      intro i hi
      simpa [show n+1-i = n-i+1 by omega] using mirror i (by omega))
    have b := ih (fun i => f (i+1)) g (by
      intro i hi
      simpa using mirror (i+1) (by omega))
    simp only [cubeSum]
    omega

def low (t i : Nat) : Nat := if i ≤ t then 1 else 0

/-- Pairing a subset with its complement puts at least half the cube
    at Hamming weights no larger than its rounded-down half dimension. -/
theorem binomialMedian (s k : Nat) (enough : s/2 ≤ k) :
    2^s ≤ 2*cubeSum s (low k) := by
  let rev := fun i => low k (s-i)
  have reflected : cubeSum s rev = cubeSum s (low k) := complement s rev (low k) (by
    intro _ _
    rfl)
  have cover := mono s (fun _ => 1) (fun i => low k i + rev i) (by
    intro i hi
    by_cases h : i ≤ k
    · simp [low, h]
    · have h' : s-i ≤ k := by omega
      simp [low, rev, h, h'])
  rw [total, add, reflected] at cover
  omega

/-- Supplies the strict low-degree binomial-sum hypothesis and the
    factor-four size bound used with the external finite-closure theorem. -/
theorem closureThreshold (L d : Nat) (nonempty : 0 < L) (size : L ≤ 2^d) :
    L < cubeSum (L.log2+2) (low (d/2+1)) ∧ 2^(L.log2+2) ≤ 4*L := by
  have lo := Nat.log2_self_le (Nat.ne_of_gt nonempty)
  have hi := Nat.lt_log2_self (n := L)
  have ld : L.log2 ≤ d := by
    have bound := (Nat.le_log2 (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2)))).2
      (Nat.le_trans lo size)
    simpa only [Nat.log2_two_pow] using bound
  have estimate := binomialMedian (L.log2+2) (d/2+1) (by omega)
  simp only [Nat.pow_succ] at hi estimate ⊢
  omega

/-- The three other points of a binary affine plane give its missing
    vertex by XOR. Natural numbers here encode fixed-length binary words. -/
theorem planeCompletion (y u v : Nat) :
    (y ^^^ u) ^^^ (y ^^^ v) ^^^ (y ^^^ u ^^^ v) = y := by
  calc
    _ = y ^^^ ((u ^^^ u) ^^^ (v ^^^ v) ^^^ (y ^^^ y)) := by ac_rfl
    _ = y := by simp

end AdaptiveHashTables
