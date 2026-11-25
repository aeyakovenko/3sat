import Std

namespace CubicCoverCounts

/-- The order on these three labels orients the rim of the base K4. -/
inductive Index | zero | one | two deriving DecidableEq, Repr

def next : Index → Index
  | .zero => .one
  | .one => .two
  | .two => .zero

structure Bits where
  a : Bool
  b : Bool
  c : Bool

def exactOne (v : Bits) : Prop := v.a.toNat + v.b.toNat + v.c.toNat = 1

/-- At a rim vertex, a is the spoke, b the outgoing rim edge, c the incoming one. -/
def rimRule (v : Bits) : Prop := v.a = v.b ∧ (v.c = true → v.a = true)

def yesBit : Index → Bool
  | .zero => true
  | _ => false

/-- Assign the same bit to all three ports of a rim vertex of residue s.
This depends on no other sheet coordinate. -/
theorem yes_rim (s : Index) : rimRule ⟨yesBit s, yesBit s, yesBit s⟩ := by
  exact ⟨rfl, id⟩

/-- The three center spokes of offsets [0,1,2] see exactly one selected residue. -/
theorem yes_center (s : Index) :
    exactOne ⟨yesBit s, yesBit (next s), yesBit (next (next s))⟩ := by
  cases s <;> rfl

def ones (xs : List Bool) : Nat := (xs.map Bool.toNat).sum

private theorem ones_cons (x : Bool) (xs : List Bool) :
    ones (x :: xs) = x.toNat + ones xs := by simp [ones]

/-- Permutations of sheets leave the number of selected edge bits invariant. -/
theorem ones_perm {xs ys : List Bool} (p : xs.Perm ys) : ones xs = ones ys := by
  induction p with
  | nil => rfl
  | cons x _ ih => simp only [ones_cons]; omega
  | swap => simp only [ones_cons]; omega
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private theorem center_sum (vs : List Bits) (ok : ∀ x ∈ vs, exactOne x) :
    ones (vs.map Bits.a) + ones (vs.map Bits.b) + ones (vs.map Bits.c) = vs.length := by
  induction vs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.a.toNat + x.b.toNat + x.c.toNat = 1 := ok x (by simp)
    have ht := ih (fun y hy => ok y (by simp [hy]))
    simp only [List.map_cons, ones_cons, List.length_cons]
    omega

private theorem rim_sum (vs : List Bits) (ok : ∀ x ∈ vs, rimRule x) :
    ones (vs.map Bits.a) = ones (vs.map Bits.b) ∧
      ones (vs.map Bits.c) ≤ ones (vs.map Bits.a) := by
  induction vs with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons x xs ih =>
    obtain ⟨ab, ca⟩ := ok x (by simp)
    have equalBits := congrArg Bool.toNat ab
    have v : x.c.toNat ≤ x.a.toNat := by
      cases hc : x.c with
      | false => simp
      | true => simp [ca hc]
    obtain ⟨e, l⟩ := ih (fun y hy => ok y (by simp [hy]))
    simp only [List.map_cons, ones_cons]
    constructor <;> omega

/-- Consequence of the three sums, without any restriction on sheet number d. -/
theorem cyclic_counts {d u₀ u₁ u₂ : Nat}
    (h₀ : 2*u₀ + u₁ = d) (h₁ : 2*u₁ + u₂ = d) (h₂ : 2*u₂ + u₀ = d) :
    u₀ = u₁ ∧ u₁ = u₂ ∧ d = 3*u₀ := by omega

/-- The assignments and edge matchings of any putative NO-cover solution.
Each list orders its fiber arbitrarily; the incidence assumptions require only
permutations between the projected edge-bit lists, so include arbitrary lifts. -/
structure NoCover (d : Nat) where
  center : Index → List Bits
  rim : Index → Index → List Bits
  centerSize : ∀ s, (center s).length = d
  centerOK : ∀ s x, x ∈ center s → exactOne x
  rimOK : ∀ p s x, x ∈ rim p s → rimRule x
  rimEdges : ∀ p s, ((rim p s).map Bits.b).Perm ((rim (next p) s).map Bits.c)
  spokeA : ∀ s, ((center s).map Bits.a).Perm ((rim .zero s).map Bits.a)
  spokeB : ∀ s, ((center s).map Bits.b).Perm ((rim .one s).map Bits.a)
  spokeC : ∀ s, ((center s).map Bits.c).Perm ((rim .two (next s)).map Bits.a)

/-- Grouped fiber sums for spoke offsets [0,0,1] give the divisibility obstruction. -/
theorem no_cover_divisibility {d : Nat} (g : NoCover d) : 3 ∣ d := by
  let u := fun p s => ones ((g.rim p s).map Bits.a)
  have monotone (p s : Index) : u p s ≤ u (next p) s := by
    calc
      u p s = ones ((g.rim p s).map Bits.b) := (rim_sum _ (g.rimOK p s)).1
      _ = ones ((g.rim (next p) s).map Bits.c) := ones_perm (g.rimEdges p s)
      _ ≤ u (next p) s := (rim_sum _ (g.rimOK (next p) s)).2
  have rimEqual (s : Index) : u .zero s = u .one s ∧ u .zero s = u .two s := by
    have a : u .zero s ≤ u .one s := monotone .zero s
    have b : u .one s ≤ u .two s := monotone .one s
    have c : u .two s ≤ u .zero s := monotone .two s
    omega
  have relation (s : Index) : 2*u .zero s + u .zero (next s) = d := by
    have hs := center_sum (g.center s) (g.centerOK s)
    rw [g.centerSize s, ones_perm (g.spokeA s), ones_perm (g.spokeB s),
      ones_perm (g.spokeC s)] at hs
    change u .zero s + u .one s + u .two (next s) = d at hs
    rw [← (rimEqual s).1, ← (rimEqual (next s)).2] at hs
    omega
  have h := cyclic_counts (relation .zero) (relation .one) (relation .two)
  exact ⟨u .zero .zero, h.2.2⟩

private theorem two_power_mod_three (k : Nat) : (2^k)%3 = 1 ∨ (2^k)%3 = 2 := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

/-- A power-of-two fiber size cannot support the NO-cover edge assignments. -/
theorem no_cover_power_of_two (k : Nat) : ¬ Nonempty (NoCover (2^k)) := by
  rintro ⟨g⟩
  obtain ⟨t, ht⟩ := no_cover_divisibility g
  have h := two_power_mod_three k
  omega

/-- Previous residue modulo three, opposite to `next`. -/
def prev : Index → Index
  | .zero => .two
  | .one => .zero
  | .two => .one

/-- At point u the exact-cover incidence test reads membership of u, P⁻¹(u),
and Q⁻¹(u).  For (+1,+2) shifts, choosing residue zero passes every test. -/
theorem yes_permutation_cover {α : Type} (label : α → Index) (pBack qBack : α → α)
    (hp : ∀ u, label (pBack u) = prev (label u))
    (hq : ∀ u, label (qBack u) = next (label u)) (u : α) :
    exactOne ⟨yesBit (label u), yesBit (label (pBack u)), yesBit (label (qBack u))⟩ := by
  rw [hp u, hq u]
  cases label u <;> rfl

/-- An arbitrary pair of inverse permutation arrays inducing shifts (0,-1)
on equal-size residue fibers. The list permutations are exactly the grouped
histogram hypotheses needed, independently of the way their points are named. -/
theorem no_permutation_cover_divisibility {α : Type} {d : Nat}
    (fiber : Index → List α) (pBack qBack : α → α) (selected : α → Bool)
    (sizes : ∀ s, (fiber s).length = d)
    (hp : ∀ s, ((fiber s).map pBack).Perm (fiber s))
    (hq : ∀ s, ((fiber s).map qBack).Perm (fiber (prev s)))
    (cover : ∀ u, exactOne ⟨selected u, selected (pBack u), selected (qBack u)⟩) :
    3 ∣ d := by
  let count := fun s => ones ((fiber s).map selected)
  have relation (s : Index) : 2 * count s + count (prev s) = d := by
    let triple := fun (u : α) => Bits.mk (selected u) (selected (pBack u)) (selected (qBack u))
    have ok : ∀ b ∈ (fiber s).map triple, exactOne b := by
      intro b hb
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hb
      exact cover u
    have he := center_sum _ ok
    have ha := ones_perm ((hp s).map selected)
    have hb := ones_perm ((hq s).map selected)
    simp only [List.map_map, Function.comp_def, triple, List.length_map, sizes] at he
    simp only [List.map_map, Function.comp_def] at ha hb
    rw [ha, hb] at he
    change count s + count s + count (prev s) = d at he
    omega
  have h := cyclic_counts (relation .zero) (relation .two) (relation .one)
  exact ⟨count .zero, h.2.2⟩

/-- No solution is possible at any level with 2^k points over a residue. -/
theorem no_permutation_cover_power_two {α : Type} (k : Nat)
    (fiber : Index → List α) (pBack qBack : α → α)
    (sizes : ∀ s, (fiber s).length = 2^k)
    (hp : ∀ s, ((fiber s).map pBack).Perm (fiber s))
    (hq : ∀ s, ((fiber s).map qBack).Perm (fiber (prev s))) :
    ¬ ∃ selected : α → Bool,
      ∀ u, exactOne ⟨selected u, selected (pBack u), selected (qBack u)⟩ := by
  rintro ⟨selected, cover⟩
  obtain ⟨t, ht⟩ := no_permutation_cover_divisibility fiber pBack qBack selected sizes hp hq cover
  have h := two_power_mod_three k
  omega

end CubicCoverCounts
