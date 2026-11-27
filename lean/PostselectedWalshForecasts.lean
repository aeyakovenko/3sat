import Std

namespace PostselectedWalshForecasts

abbrev Row := Int × Int

def weight : List Row → Int
  | [] => 0
  | (w, _) :: xs => w + weight xs

def balance : List Row → Int
  | [] => 0
  | (w, s) :: xs => w * s + balance xs

/-- Integer numerator of the updated total under a common denominator. -/
def updated (base delta : Int) : List Row → Int
  | [] => 0
  | (w, s) :: xs => w * (base + s * delta) + updated base delta xs

theorem sum_update (xs : List Row) (base delta : Int) :
    updated base delta xs = base * weight xs + balance xs * delta := by
  induction xs with
  | nil => simp [updated, weight, balance]
  | cons row xs ih =>
    rcases row with ⟨w, s⟩
    simp only [updated, weight, balance, ih, Int.mul_add, Int.add_mul]
    rw [Int.mul_comm w base, Int.mul_assoc w s delta]
    omega

/-- With fractional target p/d there is an endpoint whose total potential
is at most the previous total multiplied by its common denominator. -/
theorem endpoint (xs : List Row) (base p d : Int) (lo : 0 ≤ p) (hi : p ≤ d) :
    updated base (-p) xs ≤ base * weight xs ∨
    updated base (d-p) xs ≤ base * weight xs := by
  by_cases h : 0 ≤ balance xs
  · left
    rw [sum_update]
    have t := Int.mul_nonpos_of_nonneg_of_nonpos h (show -p ≤ 0 by omega)
    omega
  · right
    rw [sum_update]
    have t := Int.mul_nonpos_of_nonpos_of_nonneg
      (show balance xs ≤ 0 by omega) (show 0 ≤ d-p by omega)
    omega

def isolated {ι α β : Type} (key : ι → α → β) (member : α → Prop)
    (i : ι) (x : α) : Prop :=
  ∀ y, member y → key i x = key i y → x = y

/-- The universal counterexample can hold the entire array of collisions.
Each point's positive membership can itself be witnessed. -/
theorem isolation_certificate {ι α β : Type} (key : ι → α → β)
    (member : α → Prop) :
    (∀ x, member x → ∃ i, isolated key member i x) ↔
    ¬ ∃ x, member x ∧ ∃ ys : ι → α, ∀ i,
      member (ys i) ∧ key i x = key i (ys i) ∧ x ≠ ys i := by
  classical
  constructor
  · intro h
    rintro ⟨x, hx, ys, hy⟩
    obtain ⟨i, hi⟩ := h x hx
    exact (hy i).2.2 (hi (ys i) (hy i).1 (hy i).2.1)
  · intro h x hx
    apply Classical.byContradiction
    intro noKey
    have per (i : ι) : ∃ y,
        member y ∧ key i x = key i y ∧ x ≠ y := by
      apply Classical.byContradiction
      intro noBad
      apply noKey
      refine ⟨i, ?_⟩
      intro y hy same
      apply Classical.byContradiction
      exact fun neq => noBad ⟨y, hy, same, neq⟩
    let ys := fun i => Classical.choose (per i)
    exact h ⟨x, hx, ys, fun i => Classical.choose_spec (per i)⟩

/-- An isolated point is named injectively by a chosen key and its value. -/
theorem isolated_names {ι α β : Type} (key : ι → α → β)
    (member : α → Prop) (pick : α → ι)
    (good : ∀ x, member x → isolated key member (pick x) x)
    (x y : α) (hx : member x) (hy : member y)
    (eqKey : pick x = pick y) (eqValue : key (pick x) x = key (pick y) y) :
    x = y := by
  apply good x hx y hy
  simpa only [eqKey] using eqValue

/-- A certificate's retained neighbours can be counted either by seed or by
coordinate. The sums are ordinary finite lists, with no assumption that
different seeds have comparable numbers of verifying witnesses. -/
def retained {α β : Type} (seeds : List α) (dirs : List β) (keep : α → β → Nat) : Nat :=
  (seeds.map (fun a => (dirs.map (keep a)).sum)).sum

private theorem sum_add_map {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun a => f a + g a)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem count_neighbours {α β : Type} (seeds : List α) (dirs : List β)
    (keep : α → β → Nat) :
    retained seeds dirs keep = retained dirs seeds (fun i a => keep a i) := by
  induction seeds with
  | nil =>
    simp only [retained, List.map_nil, List.sum_nil]
    induction dirs with
    | nil => rfl
    | cons b bs ih => simpa only [List.map_cons, List.sum_cons, Nat.zero_add] using ih
  | cons a seeds ih =>
    unfold retained at ih ⊢
    simp only [List.map_cons, List.sum_cons]
    rw [sum_add_map, ih]

theorem pointwise_bound (v u a b : Int)
    (edge_count : (v-u)*a ≤ v*(b-a)) :
    (2*v-u)*a ≤ v*b := by
  simp only [Int.sub_mul, Int.mul_sub, Int.mul_assoc] at *
  omega

end PostselectedWalshForecasts
