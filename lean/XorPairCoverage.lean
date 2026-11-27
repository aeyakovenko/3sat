import Std

namespace XorPairCoverage

/-- Ordered XORs include the diagonal when the two lists agree. -/
def orderedSums (xs ys : List Nat) : List Nat :=
  xs.flatMap (fun x => ys.map (fun y => x ^^^ y))

/-- For a list without repetitions this emits one sum per unordered pair. -/
def distinctPairSums : List Nat → List Nat
  | [] => []
  | x :: xs => xs.map (fun y => x ^^^ y) ++ distinctPairSums xs

def quadratic (w : Nat) : Bool :=
  (w.testBit 0 && w.testBit 1) ^^ (w.testBit 2 && w.testBit 3)

def support4 : List Nat := (List.range 16).filter quadratic

theorem support4_exact : support4 = [3,7,11,12,13,14] := by decide

theorem uniqueNonzeroSums :
    (distinctPairSums support4).length = 15 ∧
    (distinctPairSums support4).count 0 = 0 ∧
    (List.range 15).all (fun i => (distinctPairSums support4).count (i+1) == 1) = true := by
  decide

/-- For a uniform translation, each point occurs on six of the sixteen
    translates, and any two distinct points occur together on two. -/
theorem translateMarginals :
    (List.range 16).all (fun x =>
      (List.range 16).countP (fun t => quadratic (t ^^^ x)) == 6 &&
      (List.range x).all (fun y =>
        (List.range 16).countP (fun t => quadratic (t ^^^ x) && quadratic (t ^^^ y)) == 2)
    ) = true := by decide

/-- One ticket per diagonal pair and three per off-diagonal pair make both
    endpoint marginals uniform on the six points and the XOR uniform on all
    sixteen words, including zero. The denominator is 96. -/
private def tickets (x y : Nat) : Nat := if x = y then 1 else 3

theorem uniformCoupling :
    (support4.map (fun x => (support4.map (tickets x)).sum)).sum = 96 ∧
    support4.all (fun x => (support4.map (tickets x)).sum == 16 &&
      (support4.map (fun y => tickets y x)).sum == 16) = true ∧
    (List.range 16).all (fun z =>
      (support4.map (fun x => (support4.map (fun y =>
        if x ^^^ y = z then tickets x y else 0)).sum)).sum == 6) = true := by decide

theorem orderedCount (xs ys : List Nat) :
    (orderedSums xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [orderedSums]
  | cons x xs ih =>
    simp only [orderedSums, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, Nat.succ_mul] at *
    omega

private theorem countOnce (xs : List Nat) (x : Nat) (nd : xs.Nodup) (mem : x ∈ xs) :
    xs.count x = 1 := by
  induction xs with
  | nil => simp at mem
  | cons y ys ih =>
    have ⟨fresh,tail⟩ := List.nodup_cons.mp nd
    by_cases eq : y = x
    · subst y
      simp [List.count_eq_zero_of_not_mem fresh]
    · rw [List.count_cons_of_ne eq]
      exact ih tail (by simpa [Ne.symm eq] using mem)

private theorem addSample (bins samples : List Nat) (x : Nat) :
    (bins.map (fun b => (x :: samples).count b)).sum =
      (bins.map (fun b => samples.count b)).sum + bins.count x := by
  induction bins with
  | nil => simp
  | cons b bins ih =>
    by_cases eq : x = b
    · subst b
      simp only [List.map_cons, List.sum_cons, List.count_cons_self, ih]
      omega
    · simp only [List.map_cons, List.sum_cons, List.count_cons_of_ne eq,
        List.count_cons_of_ne (Ne.symm eq), ih]
      omega

theorem histogramTotal (bins samples : List Nat) (nd : bins.Nodup)
    (covers : ∀ x ∈ samples, x ∈ bins) :
    (bins.map (fun b => samples.count b)).sum = samples.length := by
  induction samples with
  | nil =>
    induction bins with
    | nil => rfl
    | cons b bins ih =>
      simp only [List.map_cons, List.sum_cons, List.count_nil, Nat.zero_add]
      exact ih (List.nodup_cons.mp nd).2 (by simp)
  | cons x xs ih =>
    rw [addSample, ih (fun z hz => covers z (by simp [hz]))]
    simp [countOnce bins x nd (covers x (by simp))]

private theorem capSum (bins : List Nat) (f : Nat → Nat) (cap : Nat)
    (bounded : ∀ b ∈ bins, f b ≤ cap) :
    (bins.map f).sum ≤ (bins.countP (fun b => decide (0 < f b))) * cap := by
  induction bins with
  | nil => simp
  | cons b bins ih =>
    have h := bounded b (by simp)
    have t := ih (fun z hz => bounded z (by simp [hz]))
    by_cases zero : f b = 0
    · simp [List.countP_cons, zero, t]
    · simp [List.countP_cons, Nat.pos_of_ne_zero zero, Nat.succ_mul]
      omega

/-- Any list of admissible ordered pairs contributes once to the histogram.
    If each XOR value is attained at most cap times, the number of distinct
    attained values times cap bounds the total number of pairs. -/
theorem coverageByCap (xs ys bins : List Nat) (cap : Nat) (nd : bins.Nodup)
    (covers : ∀ z ∈ orderedSums xs ys, z ∈ bins)
    (bounded : ∀ b ∈ bins, (orderedSums xs ys).count b ≤ cap) :
    xs.length * ys.length ≤
      (bins.countP (fun b => decide (0 < (orderedSums xs ys).count b))) * cap := by
  rw [← orderedCount xs ys, ← histogramTotal bins (orderedSums xs ys) nd covers]
  exact capSum bins _ cap bounded

/-- The two consecutive integers j,j+1 flank no other integer. The
    resulting tangent inequality becomes an energy bound on a histogram. -/
private theorem adjacentSquares (j n : Nat) : (2*j+1)*n ≤ n*n + j*(j+1) := by
  rw [Nat.two_mul j, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
  by_cases h : n ≤ j
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.two_mul, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_comm]
    omega
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le (show j+1 ≤ n by omega)
    simp only [Nat.two_mul, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_comm]
    omega

/-- For every j this gives a lower bound on the number of nonempty bins
    from the number of pairs and the collision energy. For j=1 it is the
    sharp bound 3*pairs ≤ energy + 2*support when multiplicities are ≤2. -/
theorem coverageByEnergy (counts : List Nat) (j : Nat) :
    (2*j+1)*counts.sum ≤ (counts.map (fun n => n*n)).sum +
      counts.countP (fun n => decide (0 < n)) * (j*(j+1)) := by
  induction counts with
  | nil => simp
  | cons n ns ih =>
    by_cases zero : n = 0
    · simpa [zero, List.countP_cons] using ih
    · have one := adjacentSquares j n
      simp only [List.map_cons, List.sum_cons, List.countP_cons, Nat.mul_add,
        decide_eq_true (Nat.pos_of_ne_zero zero), ↓reduceIte, Nat.succ_mul] at *
      omega

end XorPairCoverage
