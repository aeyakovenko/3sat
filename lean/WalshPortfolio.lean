import Std

namespace WalshPortfolio

/-- A frequency is the same kind of Boolean word as an instance label. -/
def Word : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Word n

def total : (n : Nat) → (Word n → Int) → Int
  | 0, f => f ()
  | n+1, f => total n (fun x => f (false,x)) + total n (fun x => f (true,x))

def coeff : (n : Nat) → (Word n → Int) → Word n → Int
  | 0, f, _ => f ()
  | n+1, f, (s,a) =>
    let l := coeff n (fun x => f (false,x)) a
    let r := coeff n (fun x => f (true,x)) a
    if s then l-r else l+r

def count (n : Nat) : Int := 2^n

theorem count_succ (n : Nat) : count (n+1) = count n + count n := by
  simp only [count, Int.pow_succ]
  omega

theorem count_pos (n : Nat) : 0 < count n := by
  induction n with
  | zero => decide
  | succ n ih => rw [count_succ]; omega

theorem sum_add (n : Nat) (f g : Word n → Int) :
    total n (fun x => f x + g x) = total n f + total n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total, ih]; omega

theorem sum_scale (n : Nat) (k : Int) (f : Word n → Int) :
    total n (fun x => k * f x) = k * total n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total, ih, Int.mul_add]

theorem sum_const (n : Nat) (k : Int) :
    total n (fun _ => k) = count n * k := by
  induction n with
  | zero => simp [total, count]
  | succ n ih => simp only [total, ih, count_succ, Int.add_mul]

theorem sum_le (n : Nat) (f g : Word n → Int) (le : ∀ x, f x ≤ g x) :
    total n f ≤ total n g := by
  induction n with
  | zero => exact le ()
  | succ n ih =>
    exact Int.add_le_add (ih _ _ (fun x => le (false,x))) (ih _ _ (fun x => le (true,x)))

private theorem butterfly (u v : Int) :
    (u+v)*(u+v)+(u-v)*(u-v) = 2*(u*u+v*v) := by
  simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]; omega

theorem parseval (n : Nat) (f : Word n → Int) :
    total n (fun a => coeff n f a * coeff n f a) =
    count n * total n (fun x => f x * f x) := by
  induction n with
  | zero => simp [total, coeff, count]
  | succ n ih =>
    let l := coeff n (fun x => f (false,x))
    let r := coeff n (fun x => f (true,x))
    change total n (fun a => (l a+r a)*(l a+r a)) +
      total n (fun a => (l a-r a)*(l a-r a)) = _
    rw [← sum_add]
    simp only [butterfly, sum_scale, sum_add]
    change 2 * (total n (fun a => coeff n (fun x => f (false,x)) a *
            coeff n (fun x => f (false,x)) a) +
        total n (fun a => coeff n (fun x => f (true,x)) a *
            coeff n (fun x => f (true,x)) a)) = _
    rw [ih, ih, count_succ]
    simp only [total, Int.mul_add, Int.add_mul]
    omega

/-- Constructive pigeonhole: choose a frequency from the half with the
better of the two recursively obtained points. -/
theorem exists_small (n : Nat) (f : Word n → Int) :
    ∃ a, count n * f a ≤ total n f := by
  induction n with
  | zero => exact ⟨(), by simp [count, total]⟩
  | succ n ih =>
    obtain ⟨l, hl⟩ := ih (fun x => f (false,x))
    obtain ⟨r, hr⟩ := ih (fun x => f (true,x))
    have nonneg : 0 ≤ count n := Int.le_of_lt (count_pos n)
    by_cases better : f (false,l) ≤ f (true,r)
    · refine ⟨(false,l), ?_⟩
      have := Int.mul_le_mul_of_nonneg_left better nonneg
      simp only [total, count_succ, Int.add_mul]; omega
    · refine ⟨(true,r), ?_⟩
      have other : f (true,r) ≤ f (false,l) := by omega
      have := Int.mul_le_mul_of_nonneg_left other nonneg
      simp only [total, count_succ, Int.add_mul]; omega

def sign (b : Bool) : Int := if b then -1 else 1

def parity : (n : Nat) → Word n → Word n → Bool
  | 0, _, _ => false
  | n+1, (b,a), (c,x) => (b && c) ^^ parity n a x

private theorem sign_flip (b : Bool) : sign (!b) = -sign b := by
  cases b <;> decide

private theorem sum_neg (n : Nat) (f : Word n → Int) :
    total n (fun x => -(f x)) = -(total n f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total, ih]; omega

theorem coefficient_is_parity_sum (n : Nat) (f : Word n → Int) (a : Word n) :
    coeff n f a = total n (fun x => f x * sign (parity n a x)) := by
  induction n with
  | zero => simp [coeff, total, parity, sign]
  | succ n ih =>
    obtain ⟨b,a⟩ := a
    cases b <;> simp only [coeff, total, parity, Bool.false_and, Bool.true_and,
      Bool.false_xor, Bool.true_xor, Bool.false_eq_true, ↓reduceIte, ih, sign_flip,
      Int.mul_neg, sum_neg] <;> omega

/-- Reporters predict the SAT decision at each of the two pins. The
signed score is twice their pin-averaged proposed checksum character. -/
def rowScore (zeroPin onePin : Bool) : Int := sign (!zeroPin) + sign onePin

theorem bound_score (b c : Bool) : rowScore b c * rowScore b c ≤ 4 := by
  cases b <;> cases c <;> decide

theorem pin_agreement (target zeroPin onePin : Bool) :
    rowScore zeroPin onePin * sign target =
      (if zeroPin == (!target) then 1 else -1) +
      (if onePin == target then 1 else -1) := by
  cases target <;> cases zeroPin <;> cases onePin <;> decide

def Reporter (n : Nat) := Word n → Bool → Bool

def score {n : Nat} (r : Reporter n) (x : Word n) : Int :=
  rowScore (r x false) (r x true)

def cost (n : Nat) (rs : List (Reporter n)) (a : Word n) : Int :=
  match rs with
  | [] => 0
  | r::rest => coeff n (score r) a * coeff n (score r) a + cost n rest a

theorem cost_budget (n : Nat) (rs : List (Reporter n)) :
    total n (cost n rs) ≤ count n * (4 * (rs.length : Int) * count n) := by
  induction rs with
  | nil => simp only [cost, List.length_nil, Int.natCast_zero, Int.mul_zero,
      Int.zero_mul, sum_const, Int.le_refl]
  | cons r rest ih =>
    let N := count n
    have scaled : total n (fun x => score r x * score r x) ≤ N*4 := by
      rw [← sum_const]
      exact sum_le n _ _ (fun x => bound_score _ _)
    have contribution := Int.mul_le_mul_of_nonneg_left scaled (Int.le_of_lt (count_pos n))
    change total n (fun a => coeff n (score r) a * coeff n (score r) a +
      cost n rest a) ≤ _
    rw [sum_add, parseval]
    simp only [List.length_cons, Int.ofNat_succ, Int.mul_add, Int.add_mul, Int.mul_one]
    dsimp [N] at contribution
    have reorder : count n * (count n * 4) = count n * (4 * count n) := by
      rw [Int.mul_comm (count n) 4]
    rw [reorder] at contribution
    omega

private theorem square_nonneg (a : Int) : 0 ≤ a*a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

theorem cost_nonneg (n : Nat) (rs : List (Reporter n)) (a : Word n) :
    0 ≤ cost n rs a := by
  induction rs with
  | nil => exact Int.le_refl 0
  | cons r rest ih => exact Int.add_nonneg (square_nonneg _) ih

theorem term_le_cost (n : Nat) (rs : List (Reporter n)) (a : Word n)
    (r : Reporter n) (member : r ∈ rs) :
    coeff n (score r) a * coeff n (score r) a ≤ cost n rs a := by
  induction rs with
  | nil => cases member
  | cons x rest ih =>
    rcases List.mem_cons.mp member with eq | inside
    · subst r
      have := cost_nonneg n rest a
      simp only [cost]; omega
    · have := ih inside
      have := square_nonneg (coeff n (score x) a)
      simp only [cost]; omega

/-- With N=2^n, divide the coefficient by 2N for the actual signed
pin-and-label average. Every reporter at this same frequency then
has squared normalized correlation at most (#reporters)/N. -/
theorem one_frequency_for_all (n : Nat) (rs : List (Reporter n)) :
    ∃ a, ∀ r ∈ rs,
      coeff n (score r) a * coeff n (score r) a ≤ 4*(rs.length : Int)*count n := by
  obtain ⟨a, small⟩ := exists_small n (cost n rs)
  have budget := Int.le_trans small (cost_budget n rs)
  have at_a := Int.le_of_mul_le_mul_left budget (count_pos n)
  exact ⟨a, fun r h => Int.le_trans (term_le_cost n rs a r h) at_a⟩

end WalshPortfolio
