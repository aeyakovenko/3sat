import Std

namespace LowRankErasureAmplification

abbrev Matrix (I J : Type) := I → J → Bool
variable {I H J U : Type}

def xs {α : Type} (as : List α) (f : α → Bool) : Bool :=
  match as with
  | [] => false
  | a :: rest => f a ^^ xs rest f

private theorem xs_add {α : Type} (as : List α) (f g : α → Bool) :
    xs as (fun a => f a ^^ g a) = (xs as f ^^ xs as g) := by
  induction as with
  | nil => rfl
  | cons a tail ih =>
    simp only [xs, ih]
    cases f a <;> cases g a <;> cases xs tail f <;> cases xs tail g <;> rfl

private theorem xs_left {α : Type} (as : List α) (p : Bool) (f : α → Bool) :
    xs as (fun a => p && f a) = (p && xs as f) := by
  induction as with
  | nil => cases p <;> rfl
  | cons a tail ih => simp only [xs, ih]; cases p <;> rfl

private theorem xs_zero {α : Type} (as : List α) : xs as (fun _ => false) = false := by
  induction as with
  | nil => rfl
  | cons a tail ih => simp [xs, ih]

def add (A B : Matrix I J) : Matrix I J := fun i j => A i j ^^ B i j
def mul (ks : List H) (A : Matrix I H) (B : Matrix H J) : Matrix I J :=
  fun i j => xs ks (fun k => A i k && B k j)

theorem add_mul (ks : List H) (A A' : Matrix I H) (B : Matrix H J) (i : I) (j : J) :
    mul ks (add A A') B i j = (mul ks A B i j ^^ mul ks A' B i j) := by
  unfold mul add
  rw [← xs_add]
  apply congrArg (xs ks)
  funext k
  cases A i k <;> cases A' i k <;> cases B k j <;> rfl

theorem mul_add (ks : List H) (A : Matrix I H) (B B' : Matrix H J) (i : I) (j : J) :
    mul ks A (add B B') i j = (mul ks A B i j ^^ mul ks A B' i j) := by
  unfold mul add
  rw [← xs_add]
  apply congrArg (xs ks)
  funext k
  cases A i k <;> cases B k j <;> cases B' k j <;> rfl

abbrev RankOne (I J : Type) := (I → Bool) × (J → Bool)

def outer (s : RankOne I J) : Matrix I J := fun i j => s.1 i && s.2 j

def shifts (ss : List (RankOne I J)) : Matrix I J :=
  match ss with
  | [] => fun _ _ => false
  | h :: t => add (outer h) (shifts t)

theorem outer_mul (ks : List H) (s : RankOne I H) (B : Matrix H J) (i : I) (j : J) :
    mul ks (outer s) B i j = (s.1 i && xs ks (fun k => s.2 k && B k j)) := by
  unfold mul outer
  simp only [Bool.and_assoc]
  exact xs_left _ _ _

theorem mul_outer (ks : List H) (A : Matrix I H) (t : RankOne H J) (i : I) (j : J) :
    mul ks A (outer t) i j = (t.2 j && xs ks (fun k => A i k && t.1 k)) := by
  unfold mul outer
  rw [← xs_left]
  apply congrArg (xs ks)
  funext k
  cases A i k <;> cases t.1 k <;> cases t.2 j <;> rfl

private theorem shifts_mul (ks : List H) (ss : List (RankOne I H))
    (B : Matrix H J) (i : I) (j : J) :
    mul ks (shifts ss) B i j =
      xs ss (fun s => s.1 i && xs ks (fun k => s.2 k && B k j)) := by
  induction ss with
  | nil => simpa [mul, shifts, xs] using xs_zero ks
  | cons h t ih => simp [shifts, add_mul, outer_mul, xs, ih]

private theorem mul_shifts (ks : List H) (A : Matrix I H)
    (ts : List (RankOne H J)) (i : I) (j : J) :
    mul ks A (shifts ts) i j =
      xs ts (fun t => t.2 j && xs ks (fun k => A i k && t.1 k)) := by
  induction ts with
  | nil => simpa [mul, shifts, xs] using xs_zero ks
  | cons h t ih => simp [shifts, mul_add, mul_outer, xs, ih]

/-- Correct a single exact reported bit after independently perturbing both
operands by any given lists of rank-one matrices. The two correction sums use
matrix-vector contractions and the already shifted right operand. -/
theorem recover_shifted_entry (ks : List H) (A : Matrix I H) (B : Matrix H J)
    (ss : List (RankOne I H)) (ts : List (RankOne H J)) (i : I) (j : J) :
    let D := add B (shifts ts)
    (mul ks (add A (shifts ss)) D i j
      ^^ xs ss (fun s => s.1 i && xs ks (fun k => s.2 k && D k j))
      ^^ xs ts (fun t => t.2 j && xs ks (fun k => A i k && t.1 k))) = mul ks A B i j := by
  dsimp only
  rw [← shifts_mul, ← mul_shifts, add_mul, mul_add]
  simp

/-- The four corrected answers combine without a residual cross term. -/
theorem recover_four (ks : List H) (A R : Matrix I H) (B S : Matrix H J) (i : I) (j : J) :
    (mul ks (add A R) (add B S) i j ^^ mul ks (add A R) S i j
      ^^ mul ks R (add B S) i j ^^ mul ks R S i j) = mul ks A B i j := by
  simp only [add_mul, mul_add]
  cases mul ks A B i j <;> cases mul ks A S i j <;>
    cases mul ks R B i j <;> cases mul ks R S i j <;> rfl

section Walsh

/-- Signed character sum over a complete binary vector space. -/
def words : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (words n).map (false :: ·) ++ (words n).map (true :: ·)

def dot : List Bool → List Bool → Bool
  | a :: u, b :: v => ((a && b) ^^ dot u v)
  | _, _ => false

def sign : Bool → Int
  | false => 1
  | true => -1

def isum {α : Type} (as : List α) (f : α → Int) : Int := (as.map f).sum

private theorem isum_neg {α : Type} (as : List α) (f : α → Int) :
    isum as (fun x => -(f x)) = -(isum as f) := by
  induction as with
  | nil => simp [isum]
  | cons a as ih => simp [isum] at ih ⊢; omega

private theorem sign_flip (b : Bool) : sign (true ^^ b) = -sign b := by cases b <;> rfl

private theorem sum_append_int (l r : List Int) : (l ++ r).sum = l.sum + r.sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Int.add_assoc]

theorem character_sum (u : List Bool) :
    isum (words u.length) (fun v => sign (dot u v)) =
      if u.all (fun b => !b) then (2 : Int) ^ u.length else 0 := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    simp only [List.length_cons, words, isum, List.map_append, sum_append_int,
      List.map_map, Function.comp_apply, List.all_cons]
    change isum (words u.length) (fun v => sign ((a && false) ^^ dot u v)) +
      isum (words u.length) (fun v => sign ((a && true) ^^ dot u v)) = _
    cases a with
    | false =>
      simp only [Bool.false_and, Bool.false_xor, Bool.not_false, Bool.true_and]
      rw [ih]
      split <;> simp [Int.pow_succ] <;> omega
    | true =>
      simp only [Bool.true_and, Bool.false_xor, sign_flip, Bool.not_true, Bool.false_and]
      rw [isum_neg]
      simp <;> omega

private theorem bit_count_sum {α : Type} (as : List α) (test : α → Bool) (c : Int) :
    isum as (fun x => if test x then c else 0) = ((as.filter test).length : Int) * c := by
  induction as with
  | nil => simp [isum]
  | cons x as ih =>
    cases h : test x <;> simp [isum, h, Int.add_mul] at ih ⊢ <;> omega

/-- For the rank-one step, the character on uvᵀ is the sign of the dot
product of the linear image of u with v. Averaging over v leaves exactly the
kernel mass. Applied to a transform of rank r this gives 2^(-r). -/
theorem rank_one_character (us : List U) (image : U → List Bool) (n : Nat)
    (width : ∀ u, (image u).length = n) :
    isum us (fun u => isum (words n) (fun v => sign (dot (image u) v))) =
      ((us.filter (fun u => (image u).all (fun b => !b))).length : Int) * 2 ^ n := by
  have one (u : U) := character_sum (image u)
  simp only [width] at one
  simpa only [one] using
    (bit_count_sum us (fun u => (image u).all (fun b => !b)) ((2 : Int)^n))

end Walsh

section StationaryWalk

def prefixSum (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | k+1 => prefixSum k f + f k

private theorem geom_two (n : Nat) : prefixSum n (fun h => 2 ^ h) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prefixSum, Nat.pow_succ]; omega

private theorem prefix_mono (n : Nat) (f g : Nat → Nat) (bound : ∀ i < n, f i ≤ g i) :
    prefixSum n f ≤ prefixSum n g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    exact Nat.add_le_add (ih (fun i hi => bound i (by omega))) (bound n (by omega))

private theorem prefix_scale (n c : Nat) (f : Nat → Nat) :
    prefixSum n (fun i => c * f i) = c * prefixSum n f := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih => simp [prefixSum, ih, Nat.mul_add]

/-- With covariance at lag h bounded by μ/2^h, multiply the variance by
2^n/μ. The n diagonal terms cost n·2^n, and lag h contributes twice
(n-h)·2^(n-h). Their total is at most 3n·2^n. -/
theorem half_decay_covariance_budget (n : Nat) :
    n * 2 ^ n + 2 * prefixSum n (fun i => i * 2 ^ i) ≤ 3 * (n * 2 ^ n) := by
  have pair := prefix_mono n (fun i => i * 2 ^ i) (fun i => n * 2 ^ i)
    (fun i hi => Nat.mul_le_mul_right _ (Nat.le_of_lt hi))
  rw [prefix_scale] at pair
  have geo := geom_two n
  have geometric_le : prefixSum n (fun h => 2 ^ h) ≤ 2 ^ n := by omega
  have bound := Nat.le_trans pair (Nat.mul_le_mul_left n geometric_le)
  omega

private def tally {α : Type} (as : List α) (f : α → Nat) : Nat :=
  match as with
  | [] => 0
  | a :: tail => f a + tally tail f

def ct {α : Type} (as : List α) (p : α → Bool) : Nat := (as.filter p).length

private def deviation (m value : Nat) : Nat := (value - m)^2 + (m - value)^2

def squareError {α : Type} (paths : List α) (hits : α → Nat) (m q : Nat) :=
  tally paths (fun x => deviation m (q * hits x))

private theorem missed_charge {α : Type} (paths : List α) (hits : α → Nat) (m q : Nat) :
    ct paths (fun x => hits x == 0) * m^2 ≤ squareError paths hits m q := by
  induction paths with
  | nil => simp [ct, squareError, tally]
  | cons x paths ih =>
    cases h : hits x with
    | zero =>
      simp [ct, squareError, tally, deviation, h, Nat.succ_mul, Nat.add_mul] at ih ⊢
      omega
    | succ n =>
      simpa [ct, squareError, tally, h] using
        Nat.le_trans ih (Nat.le_add_left (squareError paths hits m q) (deviation m (q*(n+1))))

/-- The mean visit count is m/q. The finite second-moment hypothesis is
the cleared-denominator form of variance at most 3m/q. -/
theorem stationary_miss_bound {α : Type} (paths : List α) (hits : α → Nat) {m q : Nat}
    (positive : 0 < m)
    (variance : squareError paths hits m q ≤ (3 * q * paths.length) * m) :
    ct paths (fun x => hits x == 0) * m ≤ 3 * q * paths.length := by
  have h := Nat.le_trans (missed_charge paths hits m q) variance
  apply Nat.le_of_mul_le_mul_right (c := m) _ positive
  simpa [Nat.pow_succ, Nat.mul_assoc] using h

/-- Lower bound for the number of paths on which all four terms are visited.
It uses marginal miss bounds only and allows arbitrarily dependent terms. -/
theorem four_visits (paths : List U) (a b c d : U → Bool) (m q : Nat)
    (ha : ct paths (fun x => !a x) * m ≤ 3*q*paths.length)
    (hb : ct paths (fun x => !b x) * m ≤ 3*q*paths.length)
    (hc : ct paths (fun x => !c x) * m ≤ 3*q*paths.length)
    (hd : ct paths (fun x => !d x) * m ≤ 3*q*paths.length) :
    paths.length * m ≤ ct paths (fun x => a x && b x && c x && d x) * m +
      12 * (q * paths.length) := by
  have cover : paths.length ≤ ct paths (fun x => a x && b x && c x && d x) +
      ct paths (fun x => !a x) + ct paths (fun x => !b x) +
      ct paths (fun x => !c x) + ct paths (fun x => !d x) := by
    clear ha hb hc hd
    induction paths with
    | nil => simp [ct]
    | cons x paths ih =>
      cases h₁ : a x <;> cases h₂ : b x <;> cases h₃ : c x <;> cases h₄ : d x <;>
        simp only [ct] at * <;> simp [h₁, h₂, h₃, h₄] <;> omega
  have scaled := Nat.mul_le_mul_right m cover
  simp only [Nat.add_mul] at scaled
  simp only [Nat.mul_assoc] at ha hb hc hd
  omega

end StationaryWalk

end LowRankErasureAmplification
