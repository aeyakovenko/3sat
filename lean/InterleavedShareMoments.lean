import Std

namespace InterleavedShareMoments

def inside (lo hi pos : Nat) : Bool := decide (lo ≤ pos ∧ pos < hi)

/-- A nonempty proper interval in the three rounds cuts one group's triple. -/
theorem split_group (q lo hi : Nat) (hq : 0 < q) (order : lo < hi) (bound : hi < 3*q) :
    ∃ i < q, inside lo hi i ≠ inside lo hi (i+2*q) ∨
             inside lo hi (i+q) ≠ inside lo hi (i+2*q) := by
  classical
  apply Classical.byContradiction
  intro none
  have same (i : Nat) (small : i < q) :
      inside lo hi i = inside lo hi (i+2*q) ∧ inside lo hi (i+q) = inside lo hi (i+2*q) := by
    apply And.intro <;> apply Classical.byContradiction <;> intro ne
    · exact none ⟨i, small, Or.inl ne⟩
    · exact none ⟨i, small, Or.inr ne⟩
  have periodic (j : Nat) (small : j+q < 3*q) :
      (lo ≤ j ∧ j < hi) ↔ (lo ≤ j+q ∧ j+q < hi) := by
    have eq : inside lo hi j = inside lo hi (j+q) := by
      by_cases hj : j < q
      · exact (same j hj).1.trans (same j hj).2.symm
      · have h := (same (j-q) (by omega)).2
        simpa only [show j-q+q = j by omega, show j-q+2*q = j+q by omega] using h
    simpa [inside] using congrArg (· = true) eq |> Iff.of_eq
  by_cases first : q ≤ lo
  · have p := (periodic (lo-q) (by omega)).mpr (by omega)
    omega
  · have m := (periodic lo (by omega)).mp (by omega)
    have l := (periodic (lo+q) (by omega)).mp (by omega)
    have e := (periodic (hi-q) (by omega)).mp (by omega)
    omega

/-- The three contributions of one group to the XOR of the first stop shares.
    The fixed literal signs are arbitrary, and the last share enforces pin. -/
def groupPrefix (m₀ m₁ m₂ pin s₀ s₁ s₂ a b : Bool) : Bool :=
  (m₀ && (a ^^ s₀)) ^^ (m₁ && (b ^^ s₁)) ^^ (m₂ && (a ^^ b ^^ pin ^^ s₂))

def linear (p q a b : Bool) := (p && a) ^^ (q && b)

private theorem factor_group (m₀ m₁ m₂ pin s₀ s₁ s₂ a b : Bool) :
    groupPrefix m₀ m₁ m₂ pin s₀ s₁ s₂ a b =
    (groupPrefix m₀ m₁ m₂ pin s₀ s₁ s₂ false false ^^
      linear (m₀ ^^ m₂) (m₁ ^^ m₂) a b) := by
  unfold groupPrefix linear
  bv_decide

/-- Count the eight equally weighted choices for two independent shares and
    the cycle seed. Outputs below are an ordered pair of stored states. -/
def countEight (eval : Bool → Bool → Bool → Bool × Bool) (target : Bool × Bool) : Nat :=
  ([false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].map fun seed => eval a b seed).count target

private theorem affine_eight : ∀ p q r s c d x y : Bool,
    (p ≠ r ∨ q ≠ s) →
    countEight (fun a b z =>
      (z ^^ (c ^^ linear p q a b), z ^^ (d ^^ linear r s a b))) (x, y) = 2 := by
  decide

private theorem before_xor (lo hi i : Nat) (h : lo ≤ hi) :
    (decide (i < lo) ^^ decide (i < hi)) = inside lo hi i := by
  by_cases b : i < hi
  · by_cases a : i < lo
    · have hn : ¬ lo ≤ i := by omega
      simp [a, b, inside, hn]
    · have hy : lo ≤ i := by omega
      simp [a, b, inside, hy]
  · have a : ¬ i < lo := by omega
    simp [b, a, inside]

private theorem unequal_coefficients (a b c d e f : Bool)
    (h : (a ^^ d) ≠ (c ^^ f) ∨ (b ^^ e) ≠ (c ^^ f)) :
    (a ^^ c) ≠ (d ^^ f) ∨ (b ^^ c) ≠ (e ^^ f) := by bv_decide

/-- All randomness outside the selected group and the cycle seed is fixed.
    Its contributions to the two prefixes can be any bits ext₀ and ext₁. -/
def stored (q i stop : Nat) (pin : Bool) (neg : Nat → Bool)
    (ext a b seed : Bool) : Bool :=
  seed ^^ (ext ^^ groupPrefix (decide (i < stop)) (decide (i+q < stop))
    (decide (i+2*q < stop)) pin (neg i) (neg (i+q)) (neg (i+2*q)) a b)

private theorem stored_affine (q i stop : Nat) (pin : Bool) (neg : Nat → Bool)
    (ext a b seed : Bool) :
    stored q i stop pin neg ext a b seed = (seed ^^
      ((ext ^^ groupPrefix (decide (i < stop)) (decide (i+q < stop))
        (decide (i+2*q < stop)) pin (neg i) (neg (i+q)) (neg (i+2*q)) false false) ^^
       linear (decide (i < stop) ^^ decide (i+2*q < stop))
         (decide (i+q < stop) ^^ decide (i+2*q < stop)) a b)) := by
  unfold stored
  rw [factor_group _ _ _ _ _ _ _ a b]
  simp only [Bool.xor_assoc]

/-- Conditional on every other share, each of the four pairs at the two
    indicated prefixes occurs in precisely two of eight equally likely ways. -/
theorem inactive_pair_uniform (q lo hi : Nat) (hq : 0 < q) (order : lo < hi)
    (bound : hi < 3*q) :
    ∃ i < q, ∀ (pin : Bool) (neg : Nat → Bool) (ext₀ ext₁ x y : Bool),
      countEight (fun a b seed => (stored q i lo pin neg ext₀ a b seed,
        stored q i hi pin neg ext₁ a b seed)) (x,y) = 2 := by
  obtain ⟨i, small, split⟩ := split_group q lo hi hq order bound
  refine ⟨i, small, ?_⟩
  intro pin neg ext₀ ext₁ x y
  simp only [← before_xor lo hi _ (Nat.le_of_lt order)] at split
  have coefficients := unequal_coefficients _ _ _ _ _ _ split
  simp only [stored_affine]
  exact affine_eight _ _ _ _ _ _ x y coefficients

/-- For uniform shares in the other q-1 groups, enumerate their four choices
    per group by an index. Their two prefix contributions may be arbitrary
    functions of that index. -/
def atomCount (q i lo hi : Nat) (pin : Bool) (neg : Nat → Bool)
    (environment : Nat → Bool × Bool) (x y : Bool) : Nat :=
  ((List.range (4^(q-1))).map fun j =>
    countEight (fun a b seed =>
      (stored q i lo pin neg (environment j).1 a b seed,
       stored q i hi pin neg (environment j).2 a b seed)) (x,y)).sum

theorem unconditional_prefix_pair (q lo hi : Nat) (hq : 0 < q) (order : lo < hi)
    (bound : hi < 3*q) :
    ∃ i < q, ∀ (pin : Bool) (neg : Nat → Bool) (environment : Nat → Bool × Bool)
      (x y : Bool), atomCount q i lo hi pin neg environment x y = 2 * 4^(q-1) := by
  obtain ⟨i, small, each⟩ := inactive_pair_uniform q lo hi hq order bound
  refine ⟨i, small, ?_⟩
  intro pin neg environment x y
  unfold atomCount
  have sum (indices : List Nat) :
      (indices.map fun j => countEight (fun a b seed =>
        (stored q i lo pin neg (environment j).1 a b seed,
         stored q i hi pin neg (environment j).2 a b seed)) (x,y)).sum = 2 * indices.length := by
    induction indices with
    | nil => rfl
    | cons j js ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
      rw [ih, each pin neg (environment j).1 (environment j).2 x y]
      omega
  simpa using sum (List.range (4^(q-1)))

abbrev Atoms := Bool → Bool → Nat

def mass (P : Atoms) : Nat :=
  P false false + P false true + P true false + P true true

def paritySum (P : Atoms) : Int :=
  (P false false : Int) + (P true true : Int) - (P false true : Int) - (P true false : Int)

theorem zero_of_uniform (P : Atoms) (k : Nat) (flat : ∀ x y, P x y = k) :
    paritySum P = 0 := by simp [paritySum, flat]

/-- Add the equally weighted atom tables, listing the exceptional block first. -/
def mix (active : Atoms) : List Atoms → Atoms
  | [] => active
  | p :: ps => fun x y => p x y + mix active ps x y

/-- The denominator is block count times M and the absolute signed excess
    is at most M. Dividing gives absolute pair bias at most 1/block count. -/
theorem single_exception_mixture (active : Atoms) (inactive : List Atoms) (M : Nat)
    (activeMass : mass active = M)
    (others : ∀ p ∈ inactive, mass p = M ∧ paritySum p = 0) :
    mass (mix active inactive) = M * (inactive.length+1) ∧
      -(M : Int) ≤ paritySum (mix active inactive) ∧ paritySum (mix active inactive) ≤ M := by
  induction inactive with
  | nil =>
    simp only [mix, List.length_nil, Nat.zero_add, Nat.mul_one, activeMass, true_and]
    unfold mass at activeMass
    unfold paritySum
    omega
  | cons p tail ih =>
    obtain ⟨hm, hz⟩ := others p (by simp)
    obtain ⟨mt, lt, ut⟩ := ih (fun a ha => others a (List.mem_cons_of_mem _ ha))
    have plusMass : mass (mix active (p :: tail)) = mass p + mass (mix active tail) := by
      unfold mass
      simp only [mix]
      omega
    have plusParity :
        paritySum (mix active (p :: tail)) = paritySum p + paritySum (mix active tail) := by
      unfold paritySum
      simp only [mix, Int.natCast_add]
      omega
    rw [plusMass, plusParity, hm, hz, Int.zero_add, mt, List.length_cons, Nat.mul_succ]
    exact ⟨Nat.add_comm .., lt, ut⟩

end InterleavedShareMoments
