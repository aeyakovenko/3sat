import Std

namespace InnerProductFlatFibers

abbrev Word (d : Nat) := Fin d → Bool

def zero (d : Nat) : Word d := fun _ => false

def add (a b : Word d) : Word d := fun i => xor (a i) (b i)

def ipOn (indices : List (Fin d)) (a b : Word d) : Bool :=
  match indices with
  | [] => false
  | i :: rest => xor (a i && b i) (ipOn rest a b)

def ip (a b : Word d) := ipOn (List.finRange d) a b

private theorem bitDistrib (a b c u v : Bool) :
    xor (a && xor b c) (xor u v) = xor (xor (a && b) u) (xor (a && c) v) := by
  cases a <;> cases b <;> cases c <;> cases u <;> cases v <;> decide

theorem ip_add (a b v : Word d) : ip a (add b v) = xor (ip a b) (ip a v) := by
  unfold ip
  generalize List.finRange d = indices
  induction indices with
  | nil => rfl
  | cons i rest ih => simp only [ipOn, add, ih]; exact bitDistrib _ _ _ _ _

theorem ip_zero_left (b : Word d) : ip (zero d) b = false := by
  unfold ip
  generalize List.finRange d = indices
  induction indices with
  | nil => rfl
  | cons i rest ih => simp [ipOn, zero, ih]

theorem ip_zero_right (b : Word d) : ip b (zero d) = false := by
  unfold ip
  generalize List.finRange d = indices
  induction indices with
  | nil => rfl
  | cons i rest ih => simp [ipOn, zero, ih]

theorem add_right_zero (b : Word d) : add b (zero d) = b := by
  funext i; simp [add, zero]

theorem add_left_injective (b : Word d) : ∀ ⦃u v⦄, add b u = add b v → u = v := by
  intro u v h
  funext i
  have eq := congrFun h i
  cases hb : b i <;> simpa [add, hb] using eq

/-- Every projected first coordinate of a monochromatic affine flat annihilates
    the vertical kernel, by comparing two points of the same right fiber. -/
theorem projection_annihilates {H : Word d → Word d → Prop} {sign : Bool}
    (constant : ∀ a b, H a b → ip a b = sign)
    {a b v : Word d} (member : H a b) (shifted : H a (add b v)) :
    ip a v = false := by
  have eq := constant a _ shifted
  rw [ip_add, constant a b member] at eq
  cases sign <;> simpa using eq

theorem one_projection_misses_zero {H : Word d → Word d → Prop}
    (constant : ∀ a b, H a b → ip a b = true) :
    ¬∃ b, H (zero d) b := by
  rintro ⟨b, hb⟩
  simpa [ip_zero_left] using constant _ _ hb

/-- Supply the ordinary rank-nullity chart: the annihilator has 2^a elements,
    the realized projection has 2^p, and the vertical kernel has dimension k.
    The restricted projection loses one further dimension for the one verdict. -/
theorem chart_dimension_bound {H : Word d → Word d → Prop} {sign : Bool}
    (constant : ∀ a b, H a b → ip a b = sign)
    (orthogonal : List (Word d)) (leftHit : Word d → Bool)
    (detect : ∀ a, leftHit a = true ↔ ∃ b, H a b)
    (zeroIn : zero d ∈ orthogonal) {a p k : Nat}
    (dualCount : orthogonal.length = 2^a) (dualDim : a + k = d)
    (projectCount : (orthogonal.filter leftHit).length = 2^p) :
    p + k + (if sign then 1 else 0) ≤ d := by
  cases sign with
  | false =>
    have h := List.length_filter_le leftHit orthogonal
    rw [dualCount, projectCount, Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at h
    simp; omega
  | true =>
    have noZero : ¬ leftHit (zero d) = true :=
      fun h => one_projection_misses_zero constant ((detect _).mp h)
    have h := (List.length_filter_lt_length_iff_exists
      (l := orthogonal) (p := leftHit)).2 ⟨_, zeroIn, noZero⟩
    rw [dualCount, projectCount, Nat.pow_lt_pow_iff_right (by decide : 1 < 2)] at h
    simp; omega

/-- Holding the left word fixed and varying the right in the kernel of that
    left word always retains its value. -/
theorem right_kernel_flat (a b v : Word d) (orthogonal : ip a v = false) :
    ip a (add b v) = ip a b := by simp [ip_add, orthogonal]

/-- At a zero point with nonzero left word, the extra left direction exchanges
    the two distinct left words zero and a. -/
theorem extra_zero_direction (a b v : Word d) (t : Bool)
    (atZero : ip a b = false) (orthogonal : ip a v = false) :
    ip (if t then zero d else a) (add b v) = false := by
  cases t <;> simp [ip_add, ip_zero_left, atZero, orthogonal]

theorem extra_direction_injective (a b : Word d) (nonzero : a ≠ zero d) :
    ∀ ⦃x y : Bool × Word d⦄,
      (if x.1 then zero d else a, add b x.2) =
      (if y.1 then zero d else a, add b y.2) → x = y := by
  intro x y h
  have right : x.2 = y.2 := add_left_injective b (congrArg Prod.snd h)
  have left := congrArg Prod.fst h
  obtain ⟨s,u⟩ := x
  obtain ⟨t,v⟩ := y
  cases s <;> cases t <;> simp_all

end InnerProductFlatFibers
