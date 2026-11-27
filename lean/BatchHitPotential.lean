import Std

namespace BatchHitPotential

/-- Number of ordered draws of length k from N distinct points, without
    replacement. It is zero if there are too few points. -/
def falling (N : Nat) : Nat → Nat
  | 0 => 1
  | k+1 => falling N k * (N-k)

theorem fallingAppend (N t u : Nat) :
    falling N (t+u) = falling N t * falling (N-t) u := by
  induction u with
  | zero => simp [falling]
  | succ u ih =>
    simp [falling, ih, Nat.sub_sub, Nat.mul_assoc]

private theorem avoidStep (N g i : Nat) (subset : g ≤ N) :
    N*(g-i) ≤ g*(N-i) := by
  rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_comm N g]
  have h := Nat.mul_le_mul_right i subset
  omega

/-- Probability that t specified sample slots all avoid the bad row. Its
    exact without-replacement numerator is (g)_t on denominator (N)_t,
    where g counts good points. This bounds it by (g/N)^t. -/
theorem avoidPower (N g t : Nat) (subset : g ≤ N) :
    N^t * falling g t ≤ g^t * falling N t := by
  induction t with
  | zero => simp [falling]
  | succ t ih =>
    rw [Nat.pow_succ, Nat.pow_succ, falling, falling]
    calc
      _ = (N^t * falling g t) * (N*(g-t)) := by ac_rfl
      _ ≤ (g^t * falling N t) * (g*(N-t)) := Nat.mul_le_mul ih (avoidStep N g t subset)
      _ = _ := by ac_rfl

/-- Sum over flag strings, recording (number of restricted slots, number
    of unrestricted slots). Each slot has one option of each kind. -/
def flagSum : Nat → (Nat → Nat → Nat) → Nat
  | 0, f => f 0 0
  | k+1, f => flagSum k (fun t u => f (t+1) u) + flagSum k (fun t u => f t (u+1))

private theorem flagScale (k c : Nat) (f : Nat → Nat → Nat) :
    flagSum k (fun t u => c*f t u) = c*flagSum k f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => simp only [flagSum, ih, Nat.mul_add]

private theorem flagMono (k : Nat) (f g : Nat → Nat → Nat)
    (pointwise : ∀ t u, t+u=k → f t u ≤ g t u) : flagSum k f ≤ flagSum k g := by
  induction k generalizing f g with
  | zero => exact pointwise 0 0 rfl
  | succ k ih =>
    apply Nat.add_le_add
    · exact ih _ _ (fun t u h => pointwise (t+1) u (by omega))
    · exact ih _ _ (fun t u h => pointwise t (u+1) (by omega))

private theorem flaggedBinomial (k g N : Nat) :
    flagSum k (fun t u => g^t*N^u) = (g+N)^k := by
  induction k with
  | zero => simp [flagSum]
  | succ k ih =>
    simp only [flagSum]
    have first : (fun t u => g^(t+1) * N^u) = (fun t u => g*(g^t*N^u)) := by
      funext t u
      rw [Nat.pow_succ]
      ac_rfl
    have second : (fun t u => g^t * N^(u+1)) = (fun t u => N*(g^t*N^u)) := by
      funext t u
      rw [Nat.pow_succ]
      ac_rfl
    rw [first, second, flagScale, flagScale, ih, Nat.pow_succ, ← Nat.add_mul, Nat.mul_comm (g+N)]

/-- Cleared numerator of the product moment. For a chosen flag pattern
    first fill its t restricted positions from the g outside the row, then
    fill its u other positions from the N-t unused points. Summing flags
    gives weight two to every outside draw and weight one to every row
    draw. Divide by 2^k (N)_k for the expected original product. -/
def momentNumerator (N g k : Nat) : Nat :=
  flagSum k (fun t u => falling g t * falling (N-t) u)

/-- For g=N-s this states E[product x_i] ≤ (1-s/(2N))^k for a uniform
    k-subset when k≤N and N>0. The integer inequality is also valid at
    degenerate sizes without assuming any positive denominators. -/
theorem productMoment (N g k : Nat) (subset : g ≤ N) :
    N^k * momentNumerator N g k ≤ (g+N)^k * falling N k := by
  unfold momentNumerator
  rw [← flagScale, ← flaggedBinomial, Nat.mul_comm _ (falling N k), ← flagScale]
  apply flagMono
  intro t u same
  rw [← same, Nat.pow_add, fallingAppend]
  calc
    _ = (N^t*falling g t) * (N^u * falling (N-t) u) := by ac_rfl
    _ ≤ (g^t*falling N t) * (N^u * falling (N-t) u) :=
      Nat.mul_le_mul_right _ (avoidPower N g t subset)
    _ = _ := by ac_rfl

/-- Rational row weights w_i are represented on scale den. Each guessed
    integer z_i may round upwards, so 2^K times the weight units is at most
    den times z_i. Neither a lower rounding bound nor the lower C estimate
    is needed to conclude Phi ≤ 64. -/
theorem qualificationBound (K D e den weightUnits C : Nat)
    (roundUp : 2^K * weightUnits ≤ den*C)
    (upper : C ≤ 8*2^e) (qualifies : e ≤ D+K+3) :
    2^K * weightUnits ≤ 2^K * (64*(den*2^D)) := by
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) qualifies
  calc
    _ ≤ den*C := roundUp
    _ ≤ den*(8*2^e) := Nat.mul_le_mul_left _ upper
    _ ≤ den*(8*2^(D+K+3)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpow)
    _ = _ := by rw [Nat.pow_add, Nat.pow_add]; change den*(8*((2^D*2^K)*8)) = 2^K*((8*8)*(den*2^D)); ac_rfl

theorem potentialAtMost64 (K D e den weightUnits C : Nat)
    (roundUp : 2^K * weightUnits ≤ den*C)
    (upper : C ≤ 8*2^e) (qualifies : e ≤ D+K+3) :
    weightUnits ≤ 64*(den*2^D) :=
  Nat.le_of_mul_le_mul_left (qualificationBound K D e den weightUnits C roundUp upper qualifies)
    (Nat.two_pow_pos K)

/-- Exact upward rounding of a nonnegative rational with positive den. -/
def ceiling (a den : Nat) : Nat := if a%den=0 then a/den else a/den+1

theorem ceilingBounds (a den : Nat) (pos : 0 < den) :
    a ≤ den*ceiling a den ∧ den*ceiling a den < a+den := by
  have eq := Nat.mod_add_div a den
  have lt := Nat.mod_lt a pos
  by_cases h : a%den=0 <;> simp [ceiling,h,Nat.mul_add] <;> omega

theorem roundedSum (units : List Nat) (K den : Nat) (pos : 0 < den) :
    2^K*units.sum ≤ den*(units.map (fun u => ceiling (2^K*u) den)).sum := by
  induction units with
  | nil => simp
  | cons x xs ih =>
    have hh := (ceilingBounds (2^K*x) den pos).1
    simpa [Nat.mul_add] using Nat.add_le_add hh ih

theorem qualifiedWeights (units : List Nat) (K D e den : Nat) (pos : 0 < den)
    (upper : (units.map (fun u => ceiling (2^K*u) den)).sum ≤ 8*2^e)
    (qualified : e ≤ D+K+3) : units.sum ≤ 64*(den*2^D) :=
  potentialAtMost64 K D e den _ _ (roundedSum units K den pos) upper qualified

private theorem heavyCount {X : Type} (xs : List X) (tag : X → Bool) (w : X → Nat)
    (v : Nat) (h : ∀ x ∈ xs, tag x = true → v ≤ w x) :
    xs.countP tag * v ≤ (xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have tail := ih (fun y hy => h y (by simp [hy]))
    cases t : tag x with
    | false =>
      simp only [List.countP_cons, t, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, List.map_cons, List.sum_cons]
      omega
    | true =>
      have hh := h x (by simp) t
      simpa [List.countP_cons, t, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hh tail

/-- A qualified potential also bounds the number of rows hit at most j
    times by 64·2^(D+j). No independence between sample hit counts enters
    this deterministic consequence. -/
theorem weakHitTail (hits : List Nat) (K D j : Nat) (within : j ≤ K)
    (bound : (hits.map (fun t => 2^(K-t))).sum ≤ 64*(2^K*2^D)) :
    hits.countP (fun t => decide (t≤j)) ≤ 64*2^(D+j) := by
  have h := heavyCount hits (fun t => decide (t≤j)) (fun t => 2^(K-t)) (2^(K-j)) (by
    intro t _ tag
    have ht : t ≤ j := of_decide_eq_true tag
    apply Nat.pow_le_pow_right (by decide)
    omega)
  apply Nat.le_of_mul_le_mul_right (c := 2^(K-j)) _ (Nat.two_pow_pos _)
  calc
    _ ≤ 64*(2^K*2^D) := Nat.le_trans h bound
    _ = (64*2^(D+j))*2^(K-j) := by
      have eq : 2^j * 2^(K-j) = 2^K := by
        rw [← Nat.pow_add]
        congr 1
        omega
      rw [Nat.pow_add]
      calc
        _ = 64*((2^j*2^(K-j))*2^D) := by rw [eq]
        _ = _ := by ac_rfl

/-- Independently marking slots (true) selects which drawn points must
    avoid the bad row. This tests flag patterns against an actual ordered
    sample recorded by its outside-row indicators. -/
def compatible : List Bool → List Bool → Bool
  | [], [] => true
  | a::xs, f::fs => (!f || a) && compatible xs fs
  | _, _ => false

def choices : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (choices n).map (false :: ·) ++ (choices n).map (true :: ·)

def doubledWeight : List Bool → Nat
  | [] => 1
  | a::xs => (if a then 2 else 1) * doubledWeight xs

theorem compatibleCount (outside : List Bool) :
    (choices outside.length).countP (compatible outside) = doubledWeight outside := by
  induction outside with
  | nil => rfl
  | cons a xs ih =>
    cases a <;>
      simp [choices, compatible, Function.comp_def, doubledWeight, ih, Nat.two_mul]

end BatchHitPotential
