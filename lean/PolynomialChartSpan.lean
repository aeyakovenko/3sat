import Std

namespace PolynomialChartSpan

/-- A finite sum over F₂ of packed bit vectors drawn from a family. -/
inductive Span (family : Nat → Prop) : Nat → Prop where
  | zero : Span family 0
  | gen {x} : family x → Span family x
  | add {x y} : Span family x → Span family y → Span family (x ^^^ y)

theorem linear_vanish {family : Nat → Prop} (f : Nat → Bool)
    (zero : f 0 = false) (add : ∀ x y, f (x ^^^ y) = (f x ^^ f y))
    (vanish : ∀ x, family x → f x = false) {x} (generated : Span family x) :
    f x = false := by
  induction generated with
  | zero => exact zero
  | gen h => exact vanish _ h
  | add _ _ ih jh => rw [add, ih, jh]; decide

/-- When two sets of sample vectors are contained in the respective spans
    of two test families, zero on every test pair implies zero on every sample pair. -/
theorem bilinear_vanish {left right rows cols : Nat → Prop} (b : Nat → Nat → Bool)
    (zl : ∀ y, b 0 y = false) (zr : ∀ x, b x 0 = false)
    (al : ∀ x x' y, b (x ^^^ x') y = (b x y ^^ b x' y))
    (ar : ∀ x y y', b x (y ^^^ y') = (b x y ^^ b x y'))
    (hr : ∀ x, rows x → Span left x) (hc : ∀ y, cols y → Span right y)
    (tests : ∀ x, left x → ∀ y, right y → b x y = false) :
    ∀ x, rows x → ∀ y, cols y → b x y = false := by
  intro x hx y hy
  apply linear_vanish (fun z => b z y) (zl y) (fun _ _ => al _ _ y) _ (hr x hx)
  intro z hz
  exact linear_vanish (b z) (zr z) (ar z) (tests z hz) (hc y hy)

/-- Equality of the two left spans and the two right spans suffices for
    decision equivalence even if test vectors are themselves linear combinations. -/
theorem bilinear_test_iff {left right rows cols : Nat → Prop} (b : Nat → Nat → Bool)
    (zl : ∀ y, b 0 y = false) (zr : ∀ x, b x 0 = false)
    (al : ∀ x x' y, b (x ^^^ x') y = (b x y ^^ b x' y))
    (ar : ∀ x y y', b x (y ^^^ y') = (b x y ^^ b x y'))
    (lr : ∀ x, left x → Span rows x) (rl : ∀ x, rows x → Span left x)
    (rc : ∀ x, right x → Span cols x) (cr : ∀ x, cols x → Span right x) :
    (∀ x, left x → ∀ y, right y → b x y = false) ↔
    (∀ x, rows x → ∀ y, cols y → b x y = false) :=
  ⟨bilinear_vanish b zl zr al ar rl cr, bilinear_vanish b zl zr al ar lr rc⟩

/-- Binary truth tables, indexed by their number of free Boolean coordinates. -/
inductive Table : Nat → Type where
  | leaf (b : Bool) : Table 0
  | node {n} (lo hi : Table n) : Table (n+1)

def weight : {n : Nat} → Table n → Nat
  | _, .leaf b => if b then 1 else 0
  | _, .node lo hi => weight lo + weight hi

def addTable : {n : Nat} → Table n → Table n → Table n
  | _, .leaf a, .leaf b => .leaf (a ^^ b)
  | _, .node a b, .node c d => .node (addTable a c) (addTable b d)

theorem weight_triangle {n} (u v : Table n) :
    weight v ≤ weight u + weight (addTable u v) := by
  induction u with
  | leaf b => cases v with | leaf c => cases b <;> cases c <;> decide
  | node a b ih jh =>
    cases v with
    | node c d =>
      have h := ih c
      have j := jh d
      simp only [weight, addTable]
      omega

theorem add_weight_zero {n} (u v : Table n) (h : weight v = 0) :
    weight (addTable u v) = weight u := by
  induction u with
  | leaf b => cases v with | leaf c => cases b <;> cases c <;> simp_all [addTable, weight]
  | node a b ih jh =>
    cases v with
    | node c d =>
      simp only [weight] at h
      simp only [addTable, weight]
      rw [ih c (by omega), jh d (by omega)]

/-- Recursive Reed–Muller tables. The final constructor is the Shannon
    decomposition f(x,b) = u(x) XOR (b AND v(x)), with a lower degree for v. -/
inductive RM : (n d : Nat) → Table n → Prop where
  | base (b : Bool) (d : Nat) : RM 0 d (.leaf b)
  | same {n d} {u : Table n} : RM n d u → RM (n+1) d (.node u u)
  | split {n d} {u v : Table n} : RM n (d+1) u → RM n d v →
      RM (n+1) (d+1) (.node u (addTable u v))

private theorem double_domain (n d w : Nat) (h : 2^n ≤ 2^d*w) :
    2^(n+1) ≤ 2^d*(w+w) := by rw [Nat.pow_succ, Nat.mul_add]; omega

private theorem double_degree (n d w : Nat) (h : 2^n ≤ 2^d*w) :
    2^(n+1) ≤ 2^(d+1)*w := by
  rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_right_comm (2^d) 2 w]
  exact Nat.mul_le_mul_right 2 h

/-- A nonzero degree-d Reed–Muller table has relative weight at least 2⁻ᵈ. -/
theorem min_weight {n d} {f : Table n} (h : RM n d f) (pos : 0 < weight f) :
    2^n ≤ 2^d * weight f := by
  induction h with
  | base b d =>
    cases b with
    | false => simp [weight] at pos
    | true => simpa [weight] using (Nat.two_pow_pos d)
  | same h ih =>
    simp only [weight] at *
    exact double_domain _ _ _ (ih (by omega))
  | @split n d u v _ _ ihu ihv =>
    simp only [weight] at pos ⊢
    by_cases z : weight v = 0
    · rw [add_weight_zero u v z] at pos ⊢
      exact double_domain _ _ _ (ihu (by omega))
    · have hv := ihv (by omega)
      exact double_degree _ _ _ (Nat.le_trans hv (Nat.mul_le_mul_left _ (weight_triangle u v)))

end PolynomialChartSpan
