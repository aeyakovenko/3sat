import Std

namespace ExecutedPrefixCount

/-- Sum over prefix lengths zero through n-1, including an empty sum. -/
def sum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sum f n + f n

private theorem sum_mono {f g : Nat → Nat} {n : Nat}
    (h : ∀ i, i < n → f i ≤ g i) : sum f n ≤ sum g n := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h n (by omega))

private theorem sum_split (f : Nat → Nat) (k n : Nat) :
    sum f (k+n) = sum f k + sum (fun i => f (k+i)) n := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    simp [sum, ih, Nat.add_assoc]

private theorem sum_head (f : Nat → Nat) (n : Nat) :
    sum f (n+1) = f 0 + sum (fun i => f (1+i)) n := by
  simpa [sum, Nat.add_comm 1 n] using sum_split f 1 n

private theorem powers_left (w a : Nat) (hw : 0 < w) :
    sum (fun i => 2^(w*i)) (a+1) ≤ 2*2^(w*a) := by
  induction a with
  | zero => simp [sum]
  | succ a ih =>
    have inc : w*a+1 ≤ w*(a+1) := by rw [Nat.mul_add]; omega
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) inc
    rw [Nat.pow_succ] at h
    change sum _ (a+1) + 2^(w*(a+1)) ≤ _
    omega

private theorem powers_right (n : Nat) :
    sum (fun i => 2^(n-i)) n ≤ 2*2^n := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    rw [sum_head]
    have he (i : Nat) : n+1 - (1+i) = n-i := by omega
    simp only [Nat.sub_zero, he, Nat.pow_succ]
    omega

def level (w j : Nat) : Nat := j-j/(w+1)

def loadPathBound (w j : Nat) : Nat :=
  sum (fun l => min (2^(w*l)) (2^(j-l+1))) (j+1)

/-- Combined branch-string and reply-word evidence, summed over the exact
    number of loads at this depth. The constant is uniform in the word width. -/
theorem at_depth (w j : Nat) (hw : 0 < w) :
    loadPathBound w j ≤ 4 * 2^(level w j) := by
  let a := j / (w+1)
  let q := j-a
  have ha : a ≤ j := Nat.div_le_self _ _
  have cut : j+1 = (a+1)+q := by dsimp [q]; omega
  have haq : w*a ≤ q := by
    have h := Nat.div_mul_le_self j (w+1)
    change a * (w+1) ≤ j at h
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm a w] at h
    dsimp [q]; omega
  have hleft := sum_mono (f := fun l => min (2^(w*l)) (2^(j-l+1)))
      (g := fun l => 2^(w*l)) (n := a+1) (fun i _ => Nat.min_le_left _ _)
  have hright := sum_mono (f := fun i => min (2^(w*(a+1+i))) (2^(j-(a+1+i)+1)))
      (g := fun i => 2^(q-i)) (n := q) (by
        intro i hi
        have he : j-(a+1+i)+1 = q-i := by dsimp [q] at *; omega
        change min _ (2^(j-(a+1+i)+1)) ≤ 2^(q-i)
        rw [← he]
        exact Nat.min_le_right _ _)
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) haq
  have h₁ := powers_left w a hw
  have h₂ := powers_right q
  change sum _ (j+1) ≤ 4*2^q
  rw [cut, sum_split]
  omega

private theorem div_small_step (w j k : Nat) (hk : k ≤ w+1) :
    (j+k)/(w+1) ≤ j/(w+1) + 1 := by
  rw [← Nat.add_div_right j (by omega : 0 < w+1)]
  exact (Nat.le_div_iff_mul_le (by omega)).mpr
    (Nat.le_trans (Nat.div_mul_le_self (j+k) (w+1)) (by omega))

private theorem sum_levels (w : Nat) (hw : w > 0) (j : Nat) :
    sum (fun i => 2^(level w i)) (j+1) ≤ 4*2^(level w j) := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero => simp [sum, level]
    | succ j =>
      cases j with
      | zero => simp [sum, level, Nat.div_eq_of_lt (by omega : 1 < w+1)]
      | succ j =>
        have htwo := div_small_step w j 2 (by omega)
        have hone := div_small_step w (j+1) 1 (by omega)
        change (j+2)/(w+1) ≤ (j+1)/(w+1) + 1 at hone
        have hj := Nat.div_le_self j (w+1)
        have hj1 := Nat.div_le_self (j+1) (w+1)
        have ht : level w j + 1 ≤ level w (j+2) := by dsimp [level]; omega
        have ho : level w (j+1) ≤ level w (j+2) := by dsimp [level]; omega
        have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) ht
        have hpow1 := Nat.pow_le_pow_right (by decide : 0 < 2) ho
        rw [Nat.pow_succ] at hpow
        have old := ih j (by omega)
        change sum _ (j+1) + 2^(level w (j+1)) + 2^(level w (j+2)) ≤ 4*2^(level w (j+2))
        omega

/-- At all depths through T, branch strings and LOAD replies bound the
    number of reachable nodes by a constant times 2^(T - floor(T/(w+1))). -/
theorem all_depths (w T : Nat) (hw : 0 < w) :
    sum (loadPathBound w) (T+1) ≤ 16*2^(level w T) := by
  have hs := sum_mono (n := T+1) (fun i _ => at_depth w i hw)
  have hmul (n : Nat) : sum (fun i => 4*2^(level w i)) n =
      4 * sum (fun i => 2^(level w i)) n := by
    induction n with
    | zero => simp [sum]
    | succ n ih => simp [sum, ih, Nat.mul_add]
  rw [hmul] at hs
  have hl := sum_levels w hw T
  omega

end ExecutedPrefixCount
