import Std

namespace ReplayClockGrowth

/-- A finite prefix of a sequence bounded by a constant. -/
theorem sum_cap (xs : List Nat) (a : Nat) (cap : ∀ x ∈ xs, x ≤ a) :
    xs.sum ≤ xs.length * a := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h1 := cap x (by simp)
    have h2 := ih (fun y hy => cap y (by simp [hy]))
    simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add h1 h2

/-- The early and late portions of a replay have separate running maxima. -/
theorem split_cap (early late : List Nat) (a b : Nat)
    (h1 : ∀ x ∈ early, x ≤ a) (h2 : ∀ x ∈ late, x ≤ b) :
    (early ++ late).sum ≤ early.length * a + late.length * b := by
  have join (u : List Nat) : (u ++ late).sum = u.sum + late.sum := by
    induction u with
    | nil => simp
    | cons x xs ih => simp [ih, Nat.add_assoc]
  rw [join]
  exact Nat.add_le_add (sum_cap early a h1) (sum_cap late b h2)

/-- If the running maximum did not change, a lower bound on its average
    at the previous record continues to hold, in integer denominator units. -/
theorem extend_record (k r recip peak sum : Nat) (hr : 1 ≤ recip)
    (hs : k * peak ≤ recip * sum) :
    (k+r) * peak ≤ recip * (sum + r*peak) := by
  have le : r*peak ≤ recip * (r*peak) := by
    simpa using Nat.mul_le_mul_right (r*peak) hr
  rw [Nat.add_mul, Nat.mul_add]
  exact Nat.add_le_add hs le

/-- If at least one K-th of the possible total is present, deleting a
    suffix of size at most j/(2K) leaves a fixed proportion of the maximum
    at an earlier index.  hcut is the integral version of that suffix bound. -/
theorem peak_at_cut (j m K a b s : Nat) (pos : 0 < j) (hm : m ≤ j)
    (hd : j*b ≤ K*s) (hs : s ≤ m*a+(j-m)*b)
    (hcut : 2*K*(j-m) ≤ j) :
    b ≤ 2*K*a := by
  have dup := Nat.mul_le_mul_left 2 (Nat.le_trans hd (Nat.mul_le_mul_left K hs))
  have cut := Nat.mul_le_mul_right b hcut
  have early := Nat.mul_le_mul_left (2*K*a) hm
  have lhs : 2 * (j*b) ≤ (2*K*a)*m + (2*K*(j-m))*b := by
    rw [Nat.mul_add, Nat.mul_add] at dup
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using dup
  have ans : b*j ≤ (2*K*a)*j := by
    rw [Nat.mul_comm b j]
    omega
  exact Nat.le_of_mul_le_mul_right ans pos

theorem binom_gain (p x y:Nat) :
  x^(p+1) + (p+1)*(x^p*y) ≤ (x+y)^(p+1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have le := Nat.mul_le_mul_right (x+y) ih
    rw [Nat.pow_succ (x+y) (p+1)]
    apply Nat.le_trans _ le
    have eqn : (x^(p+1)+(p+1)*(x^p*y))*(x+y)
        = x^((p+1)+1)+((p+1)+1)*(x^(p+1)*y)+((p+1)*(x^p*y))*y := by
        simp only [Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.one_mul]
        ac_rfl
    rw [eqn]
    omega


/-- The first nonconstant binomial term pays for one backward replay step. -/
theorem shrink_power (j m K p : Nat) (hm : m ≤ j)
    (h : K*(m+1) ≤ (p+1)*(j-m)) :
    K*(m+1)^(p+1) ≤ (j+1)^(p+1) := by
  have le := Nat.mul_le_mul_right ((m+1)^p) h
  have gain := binom_gain p (m+1) (j-m)
  have join : m+1+(j-m) = j+1 := by omega
  rw [join] at gain
  have lower : K*(m+1)^(p+1) ≤ (p+1)*((m+1)^p*(j-m)) := by
    rw [Nat.pow_succ]
    simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using le
  omega

/-- A fixed multiplicative loss at a shrinking index, or an existing
    polynomial bound, gives one polynomial envelope at all indices. -/
theorem polynomial_envelope (a : Nat → Nat) (D K p : Nat)
    (step : ∀ j, a j ≤ D*(j+1)^(p+1) ∨
      ∃ m < j, a j ≤ K*a m ∧ K*(m+1) ≤ (p+1)*(j-m)) :
    ∀ j, a j ≤ D*(j+1)^(p+1) := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    rcases step j with done | ⟨m,hm,rate,shrink⟩
    · exact done
    · calc a j ≤ K*a m := rate
           _ ≤ K*(D*(m+1)^(p+1)) := Nat.mul_le_mul_left K (ih m hm)
           _ = D*(K*(m+1)^(p+1)) := by ac_rfl
           _ ≤ D*(j+1)^(p+1) :=
             Nat.mul_le_mul_left D (shrink_power j m K p (Nat.le_of_lt hm) shrink)

/-- Replay of either polarity can be capped.  A correct partial recognizer
    abstains on the opposite input; the chosen default then labels it. -/
theorem capped_polarity (p : Bool) (opposite : Option Bool)
    (sound : ∀ b, opposite = some b → b = !p) :
    (some p).getD (!p) = p ∧ opposite.getD (!p) = !p := by
  cases opposite with
  | none => simp
  | some b => simp_all

end ReplayClockGrowth
