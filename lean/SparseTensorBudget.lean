import Std

namespace SparseTensorBudget

variable {I : Type}

def mass (ids : List I) (weight : I → Nat) : Nat :=
  (ids.map weight).sum

def active (ids : List I) (weight : I → Nat) : Nat :=
  (ids.filter (fun i => decide (0 < weight i))).length

def ones (ids : List I) (vector : I → Bool) : Nat :=
  (ids.filter vector).length

private theorem member_le_mass {i : I} (ids : List I) (w : I → Nat)
    (mem : i ∈ ids) : w i ≤ mass ids w := by
  induction ids with
  | nil => simp at mem
  | cons a tail ih =>
    rcases List.mem_cons.mp mem with rfl | inTail
    · simp [mass]
    · have tailBound := ih inTail
      simp [mass] at tailBound ⊢
      omega

private theorem positive_minimum (ids : List I) (w : I → Nat)
    (nonzero : 0 < mass ids w) :
    ∃ i ∈ ids, 0 < w i ∧ ∀ j ∈ ids, 0 < w j → w i ≤ w j := by
  induction ids with
  | nil => simp [mass] at nonzero
  | cons a tail ih =>
    by_cases ht : 0 < mass tail w
    · obtain ⟨b, hb, bp, minimal⟩ := ih ht
      by_cases choose : 0 < w a ∧ w a ≤ w b
      · refine ⟨a, by simp, choose.1, ?_⟩
        intro j hj jp
        rcases List.mem_cons.mp hj with rfl | hj
        · exact Nat.le_refl _
        · exact Nat.le_trans choose.2 (minimal _ hj jp)
      · refine ⟨b, by simp [hb], bp, ?_⟩
        intro j hj jp
        rcases List.mem_cons.mp hj with rfl | hj
        · omega
        · exact minimal _ hj jp
    · have hp : 0 < w a := by
        simp [mass] at nonzero ht
        omega
      refine ⟨a, by simp, hp, ?_⟩
      intro j hj jp
      rcases List.mem_cons.mp hj with rfl | hj
      · exact Nat.le_refl _
      · have leSum := member_le_mass tail w hj
        omega

private theorem minimum_times_active (ids : List I) (w : I → Nat) (b : Nat)
    (minimal : ∀ j ∈ ids, 0 < w j → b ≤ w j) :
    active ids w * b ≤ mass ids w := by
  induction ids with
  | nil => simp [active, mass]
  | cons a tail ih =>
    have bound := ih (fun j hj => minimal j (List.mem_cons_of_mem _ hj))
    by_cases hp : 0 < w a
    · have ha := minimal a (by simp) hp
      simpa [active, mass, hp, Nat.add_mul, Nat.add_comm] using Nat.add_le_add ha bound
    · simpa [active, mass, hp, Nat.eq_zero_of_not_pos hp] using bound

/-- A nonzero tensor has an active slice whose weight times the number of active
slices fits the whole budget. Repetitions in the index enumeration also work. -/
theorem lightest_slice (ids : List I) (w : I → Nat) {K : Nat}
    (nonzero : 0 < mass ids w) (budget : mass ids w ≤ K) :
    ∃ i ∈ ids, 0 < w i ∧ active ids w * w i ≤ K := by
  obtain ⟨i, hi, pos, minimal⟩ := positive_minimum ids w nonzero
  exact ⟨i, hi, pos, Nat.le_trans (minimum_times_active ids w (w i) minimal) budget⟩

private theorem ones_le_active (ids : List I) (v : I → Bool) (w : I → Nat)
    (sound : ∀ i, v i = true → 0 < w i) :
    ones ids v ≤ active ids w := by
  induction ids with
  | nil => simp [ones, active]
  | cons i tail ih =>
    cases h : v i with
    | true => simpa [ones, active, h, sound i h] using Nat.succ_le_succ ih
    | false =>
      by_cases positive : 0 < w i
      · simpa [ones, active, h, positive] using Nat.le_succ_of_le ih
      · simpa [ones, active, h, positive] using ih

private theorem ones_pos {ids : List I} {v : I → Bool} {i : I}
    (mem : i ∈ ids) (observed : v i = true) : 0 < ones ids v := by
  have included := List.mem_filter.mpr (show i ∈ ids ∧ v i = true from ⟨mem, observed⟩)
  exact List.length_pos_of_mem included

/-- A test family that detects each nonzero input at cost at most its weight
and never reports one on weight zero. -/
structure Detector (X Q : Type) (weight : X → Nat) where
  cost : Q → Nat
  eval : Q → X → Bool
  sound : ∀ q x, eval q x = true → 0 < weight x
  detects : ∀ x, 0 < weight x → ∃ q, eval q x = true ∧ cost q ≤ weight x

variable {X P Q : Type} {weight : X → Nat}

/-- Evaluate one shared inner test on all slices and then one outer test
on the resulting bit vector. The pair has the product of its component costs. -/
def tensor (ids : List I) (outer : Detector (I → Bool) P (ones ids))
    (inner : Detector X Q weight) :
    Detector (I → X) (P × Q) (fun x => mass ids (fun i => weight (x i))) where
  cost pair := outer.cost pair.1 * inner.cost pair.2
  eval pair x := outer.eval pair.1 (fun i => inner.eval pair.2 (x i))
  sound := by
    intro pair x found
    let v := fun i => inner.eval pair.2 (x i)
    have positive := outer.sound pair.1 v found
    have bounded := ones_le_active ids v (fun i => weight (x i))
      (fun i => inner.sound pair.2 (x i))
    have lower := minimum_times_active ids (fun i => weight (x i)) 1
      (fun _ _ pos => pos)
    omega
  detects := by
    intro x positive
    let w := fun i => weight (x i)
    obtain ⟨i, hi, wi, bound⟩ := lightest_slice ids w positive (Nat.le_refl _)
    obtain ⟨b, found, cb⟩ := inner.detects (x i) wi
    let v := fun j => inner.eval b (x j)
    obtain ⟨a, hit, ca⟩ := outer.detects v (ones_pos hi found)
    have cheap := Nat.le_trans ca (ones_le_active ids v w (fun j => inner.sound b (x j)))
    exact ⟨(a, b), hit, Nat.le_trans (Nat.mul_le_mul cheap cb) bound⟩

def TensorInput (I : Type) : Nat → Type
  | 0 => Bool
  | n + 1 => I → TensorInput I n

def TensorProbe (P : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => P × TensorProbe P n

def tensorWeight (ids : List I) : (n : Nat) → TensorInput I n → Nat
  | 0, x => Bool.toNat x
  | n + 1, x => mass ids (fun i => tensorWeight ids n (x i))

def tensorDetector (ids : List I) (base : Detector (I → Bool) P (ones ids)) :
    (n : Nat) → Detector (TensorInput I n) (TensorProbe P n) (tensorWeight ids n)
  | 0 => {
      cost := fun _ => 1
      eval := fun _ x => x
      sound := by intro _ x hit; cases x <;> simp_all [tensorWeight]
      detects := by
        intro x pos
        cases x with
        | false => simp [tensorWeight] at pos
        | true => exact ⟨(), rfl, Nat.le_refl 1⟩
    }
  | n + 1 => tensor ids base (tensorDetector ids base n)

/-- Every nonzero tensor of weight at most K is detected by a product test
of cost at most K, independently of tensor order. -/
theorem detects_within_budget (ids : List I) (base : Detector (I → Bool) P (ones ids))
    (n : Nat) (x : TensorInput I n) {K : Nat}
    (nonzero : 0 < tensorWeight ids n x) (budget : tensorWeight ids n x ≤ K) :
    ∃ p, (tensorDetector ids base n).eval p x = true ∧ (tensorDetector ids base n).cost p ≤ K := by
  obtain ⟨p, hit, cost⟩ := (tensorDetector ids base n).detects x nonzero
  exact ⟨p, hit, Nat.le_trans cost budget⟩

end SparseTensorBudget
