import Std

namespace FewWriterMaxima

private def bins (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => bins f n + f n

private theorem bins_add (f g : Nat → Nat) (n : Nat) :
    bins (fun i => f i + g i) n = bins f n + bins g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bins, ih]; omega

private theorem bins_ext (f g : Nat → Nat) (n : Nat) (eq : ∀ i, f i = g i) :
    bins f n = bins g n := by
  simp [funext eq]

private theorem single_bin (v n : Nat) :
    bins (fun i => if v = i then i else 0) n = (if v < n then v else 0) := by
  induction n with
  | zero => simp [bins]
  | succ n ih =>
    simp only [bins, ih]
    by_cases h : v = n
    · subst v; simp
    · by_cases lt : v < n <;> simp [h, lt, show (v < n+1 ↔ v < n) by omega]

private theorem zero_bins (n : Nat) : bins (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bins, ih]

private theorem regroup (xs : List Nat) (n : Nat) (small : ∀ x ∈ xs, x < n) :
    bins (fun i => i * xs.count i) n = xs.sum := by
  induction xs with
  | nil => simpa using zero_bins n
  | cons x xs ih =>
    have hv := small x (by simp)
    have tail := ih (fun v h => small v (by simp [h]))
    calc
      _ = bins (fun i => (if x = i then i else 0) + i * xs.count i) n := by
        apply bins_ext
        intro i
        by_cases eq : x = i <;> simp [List.count_cons, eq, Nat.mul_add, Nat.add_comm]
      _ = _ := by rw [bins_add, single_bin, if_pos hv, tail, List.sum_cons]

/-- Total variation of equal-length histograms, in unnormalized integer counts. -/
def variation (xs ys : List Nat) (n : Nat) : Nat :=
  bins (fun i => xs.count i - ys.count i) n

private theorem bin_charge (i a b k : Nat) (inside : i ≤ k) :
    i * a ≤ i * b + k * (a-b) := by
  by_cases small : a ≤ b
  · exact Nat.le_trans (Nat.mul_le_mul_left i small) (by omega)
  · calc
      i * a = i * (b+(a-b)) := congrArg (i * ·) (by omega)
      _ = i*b + i*(a-b) := Nat.mul_add ..
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ inside) _

private theorem moments (xs ys : List Nat) (n k : Nat) (inside : n ≤ k+1) :
    bins (fun i => i * xs.count i) n ≤
    bins (fun i => i * ys.count i) n + k * variation xs ys n := by
  induction n with
  | zero => simp [bins, variation]
  | succ n ih =>
    have prev := ih (by omega)
    have last := bin_charge n (xs.count n) (ys.count n) k (by omega)
    simp only [bins, variation, Nat.mul_add] at *
    omega

structure Reply where
  actual : Nat
  proposed : Nat
  illegal : Bool

def wrong (r : Reply) : Nat := if r.actual = r.proposed then 0 else 1

def penalty (r : Reply) : Nat := if r.illegal then 1 else 0

private theorem reply_charge (r : Reply) (k : Nat) (bounded : r.proposed ≤ k)
    (maximal : r.illegal = false → r.proposed ≤ r.actual) :
    wrong r + r.proposed ≤ r.actual + (k+1) * penalty r := by
  cases r with
  | mk actual proposed illegal =>
    change proposed ≤ k at bounded
    change illegal = false → proposed ≤ actual at maximal
    change (if actual = proposed then 0 else 1) + proposed ≤ actual + (k+1) * (if illegal then 1 else 0)
    cases illegal <;> by_cases eq : actual = proposed <;>
      simp [eq] at maximal ⊢ <;> omega

theorem robust_histogram (rows : List Reply) (k : Nat)
    (bounded : ∀ r ∈ rows, r.actual ≤ k ∧ r.proposed ≤ k)
    (maximal : ∀ r ∈ rows, r.illegal = false → r.proposed ≤ r.actual) :
    (rows.map wrong).sum ≤
      k * variation (rows.map Reply.actual) (rows.map Reply.proposed) (k+1) +
      (k+1) * (rows.map penalty).sum := by
  have charges : (rows.map wrong).sum + (rows.map Reply.proposed).sum ≤
      (rows.map Reply.actual).sum + (k+1) * (rows.map penalty).sum := by
    induction rows with
    | nil => simp
    | cons row rest ih =>
      have prev := ih (fun r h => bounded r (by simp [h]))
        (fun r h => maximal r (by simp [h]))
      have last := reply_charge row k (bounded row (by simp)).2 (maximal row (by simp))
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      omega
  have ha : ∀ v ∈ rows.map Reply.actual, v < k+1 := by
    intro v hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
    exact Nat.lt_succ_of_le (bounded r hr).1
  have hb : ∀ v ∈ rows.map Reply.proposed, v < k+1 := by
    intro v hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
    exact Nat.lt_succ_of_le (bounded r hr).2
  have h := moments (rows.map Reply.actual) (rows.map Reply.proposed) (k+1) k (by omega)
  rw [regroup _ _ ha, regroup _ _ hb] at h
  omega

theorem recover_alternating (sign parity : Bool) : (sign ^^ parity) ^^ parity = sign := by
  cases sign <;> cases parity <;> rfl

end FewWriterMaxima
