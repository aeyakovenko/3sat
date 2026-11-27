import Std

namespace FeedbackVerdictSyndrome

abbrev Pair := Bool × Bool

/-- A binary fault pair at each of n distinct times. -/
def Trace : Nat → Type
  | 0 => Unit
  | n+1 => Pair × Trace n

def ip : (n : Nat) → Trace n → Bool
  | 0, _ => false
  | n+1, (v, z) => (v.1 && v.2) ^^ ip n z

def run : (n : Nat) → Bool → Trace n → Bool
  | 0, q, _ => q
  | n+1, q, (v,z) => run n (q ^^ (v.1 && v.2)) z

theorem verdict_parity (n : Nat) (q : Bool) (z : Trace n) :
    run n q z = (q ^^ ip n z) := by
  induction n generalizing q with
  | zero => simp [run, ip]
  | succ n ih =>
    rcases z with ⟨⟨a,b⟩,z⟩
    simp only [run, ip, ih, Bool.xor_assoc]

def zeroMask : (n : Nat) → Trace n
  | 0 => ()
  | n+1 => ((false,false),zeroMask n)

def add : (n : Nat) → Trace n → Trace n → Trace n
  | 0, _, _ => ()
  | n+1, (v,x), (w,y) => ((v.1 ^^ w.1, v.2 ^^ w.2), add n x y)

def lin : (n : Nat) → Trace n → Trace n → Bool
  | 0, _, _ => false
  | n+1, (w,l), (v,z) => ((w.1 && v.1) ^^ (w.2 && v.2)) ^^ lin n l z

private theorem lin_zero (n : Nat) (z : Trace n) : lin n (zeroMask n) z = false := by
  induction n with
  | zero => rfl
  | succ n ih => rcases z with ⟨⟨a,b⟩,z⟩; simp [zeroMask, lin, ih]

private theorem lin_add (n : Nat) (u v z : Trace n) :
    lin n (add n u v) z = (lin n u z ^^ lin n v z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases u with ⟨⟨a,b⟩,u⟩
    rcases v with ⟨⟨c,d⟩,v⟩
    rcases z with ⟨⟨x,y⟩,z⟩
    simp only [add, lin, ih]
    cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> cases y <;>
      cases lin n u z <;> cases lin n v z <;> rfl

def tally : (n : Nat) → (Trace n → Int) → Int
  | 0, f => f ()
  | n+1, f =>
      tally n (fun z => f ((false,false),z)) + tally n (fun z => f ((false,true),z)) +
      tally n (fun z => f ((true,false),z)) + tally n (fun z => f ((true,true),z))

private theorem tally_add (n : Nat) (f g : Trace n → Int) :
    tally n (fun z => f z + g z) = tally n f + tally n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tally, ih]; omega

private theorem tally_neg (n : Nat) (f : Trace n → Int) :
    tally n (fun z => -f z) = -tally n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tally, ih]; omega

private theorem tally_const (n : Nat) (c : Int) : tally n (fun _ => c) = 4^n * c := by
  induction n with
  | zero => simp [tally]
  | succ n ih =>
    simp only [tally, ih, Int.pow_succ]
    rw [Int.mul_right_comm]
    omega

def sign (b : Bool) : Int := if b then -1 else 1

private theorem tally_flip (n : Nat) (b : Bool) (g : Trace n → Bool) :
    tally n (fun z => sign (b ^^ g z)) = if b then -tally n (fun z => sign (g z))
                                       else tally n (fun z => sign (g z)) := by
  cases b with
  | false => simp
  | true =>
    have f : (fun z => sign (true ^^ g z)) = (fun z => -sign (g z)) := by
      funext z; cases g z <;> rfl
    simp only [f, tally_neg, if_true]

private theorem shuffle (a b c d : Bool) : ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- Full (unnormalized) Walsh transform of the m-pair inner product. -/
theorem bent_transform (n : Nat) (u : Trace n) :
    tally n (fun z => sign (ip n z ^^ lin n u z)) =
      if ip n u then -(2^n : Int) else 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases u with ⟨⟨a,b⟩,u⟩
    simp only [tally, ip, lin, shuffle _ (ip n _) _ (lin n u _), tally_flip, ih]
    by_cases h : ip n u = true
    · cases a <;> cases b <;> simp [h, Int.pow_succ] <;> omega
    · have e : ip n u = false := Bool.eq_false_iff.mpr h
      cases a <;> cases b <;> simp [e, Int.pow_succ] <;> omega

private theorem linear_nonnegative (n : Nat) (u : Trace n) :
    0 ≤ tally n (fun z => sign (lin n u z)) := by
  induction n with
  | zero => simp [tally,lin,sign]
  | succ n ih =>
    rcases u with ⟨⟨a,b⟩,u⟩
    have h := ih u
    simp only [tally, lin, tally_flip]
    cases a <;> cases b <;> simp <;> omega

def ok (n : Nat) (tests : List (Trace n)) (z : Trace n) : Bool :=
  tests.all (fun u => !lin n u z)

def transform (n : Nat) (value : Trace n → Bool) (tests : List (Trace n)) (u : Trace n) : Int :=
  tally n (fun z => if ok n tests z then sign (value z ^^ lin n u z) else 0)

private theorem split_point (k a b v : Bool) :
    (if !b && k then sign (v ^^ a) else 0) + (if !b && k then sign (v ^^ a) else 0) =
    (if k then sign (v ^^ a) else 0) + (if k then sign (v ^^ (a ^^ b)) else 0) := by
  cases k <;> cases a <;> cases b <;> cases v <;> decide

private theorem halve (n : Nat) (f : Trace n → Bool) (l : List (Trace n)) (u v : Trace n) :
    transform n f (v::l) u + transform n f (v::l) u =
      transform n f l u + transform n f l (add n u v) := by
  unfold transform
  rw [← tally_add, ← tally_add]
  congr 1
  funext z
  simp only [ok, List.all_cons, lin_add]
  exact split_point _ _ _ _

/-- Restricting to any sequence of homogeneous parity tests preserves the
    uniform signed excess bound, even for dependent tests. -/
theorem restricted_bound (n : Nat) (l : List (Trace n)) (u : Trace n) :
    transform n (ip n) l u ≤ (2^n : Int) := by
  induction l generalizing u with
  | nil =>
    unfold transform
    simp only [ok, List.all_nil, if_true]
    rw [bent_transform]
    have nonneg : 0 ≤ (2^n : Int) := Int.pow_nonneg (by decide)
    split <;> omega
  | cons v l ih =>
    have a := ih u
    have b := ih (add n u v)
    have eq := halve n (ip n) l u v
    omega

private theorem plain_nonnegative (n : Nat) (l : List (Trace n)) (u : Trace n) :
    0 ≤ transform n (fun _ => false) l u := by
  induction l generalizing u with
  | nil => simpa [transform,ok] using linear_nonnegative n u
  | cons v l ih =>
    have a := ih u
    have b := ih (add n u v)
    have eq := halve n (fun _ => false) l u v
    omega

/-- Size of the zero-transcript kernel times 2^number-of-tests is at least 4^m. -/
theorem kernel_size (n : Nat) (l : List (Trace n)) :
    (4^n : Int) ≤ 2^l.length * transform n (fun _ => false) l (zeroMask n) := by
  induction l with
  | nil => simp [transform, ok, lin_zero, sign, tally_const]
  | cons v l ih =>
    have eq := halve n (fun _ => false) l (zeroMask n) v
    have nonneg := plain_nonnegative n l (add n (zeroMask n) v)
    have double : transform n (fun _ => false) l (zeroMask n) ≤
        2 * transform n (fun _ => false) (v::l) (zeroMask n) := by omega
    have bound := Int.mul_le_mul_of_nonneg_left double (Int.pow_nonneg (m := l.length) (by decide : (0 : Int) ≤ 2))
    simp only [List.length_cons, Int.pow_succ, Int.mul_assoc]
    exact Int.le_trans ih bound

def members (n : Nat) (l : List (Trace n)) : Int :=
  tally n (fun z => if ok n l z then 1 else 0)

def flips (n : Nat) (l : List (Trace n)) : Int :=
  tally n (fun z => if ok n l z && ip n z then 1 else 0)

private theorem count_split (n : Nat) (l : List (Trace n)) :
    transform n (ip n) l (zeroMask n) + flips n l + flips n l = members n l := by
  unfold transform flips members
  rw [← tally_add, ← tally_add]
  congr 1
  funext z
  simp only [lin_zero, Bool.xor_false]
  have h (a b : Bool) : (if a then sign b else 0) + (if a && b then 1 else 0) +
        (if a && b then 1 else 0) = (if a then 1 else 0) := by
    cases a <;> cases b <;> decide
  exact h _ _

private theorem square_two (n : Nat) : (2^n : Int) * 2^n = 4^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      (2^(n+1) : Int)*2^(n+1) = (2^n*2^n)*(2*2) := by rw [Int.pow_succ]; ac_rfl
      _ = 4^(n+1) := by rw [ih, Int.pow_succ]; rfl

/-- Cleared denominators for flip fraction ≥ (1−2^(r−m))/2.
    The cardinalities count actual fault pairs with zero syndrome. -/
theorem undetected_final_flips (n : Nat) (l : List (Trace n)) :
    (2^n : Int) * members n l ≤ 2^n * flips n l + 2^n * flips n l + 2^l.length * members n l := by
  have signed := restricted_bound n l (zeroMask n)
  have relation := count_split n l
  have size : (4^n : Int) ≤ 2^l.length * members n l := by
    simpa [transform, members, lin_zero, sign] using kernel_size n l
  have bound : members n l ≤ flips n l + flips n l + 2^n := by omega
  have scaled := Int.mul_le_mul_of_nonneg_left bound (Int.pow_nonneg (m:=n) (by decide : (0:Int)≤2))
  rw [Int.mul_add, Int.mul_add, square_two] at scaled
  omega

end FeedbackVerdictSyndrome
