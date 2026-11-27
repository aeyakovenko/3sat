import Std

/-! A multilinear polynomial with a surviving top monomial in each outside
fiber is nonzero on at least one point per fiber, over any nontrivial field.
The coefficient representation below also makes sense with a weaker addition
law. Variables are evaluated only at zero and one. -/

namespace BundleSupportFilter

universe u

def Bits : Nat → Type
  | 0 => Unit
  | n + 1 => Bool × Bits n

/-- At a variable, the pair (p,q) encodes p + X q. -/
def Poly (R : Type u) : Nat → Type u
  | 0 => R
  | n + 1 => Poly R n × Poly R n

def eval {R : Type u} (add : R → R → R) :
    (n : Nat) → Poly R n → Bits n → R
  | 0, p, _ => p
  | n + 1, p, x =>
    if x.1 then add (eval add n p.1 x.2) (eval add n p.2 x.2)
    else eval add n p.1 x.2

/-- Coefficient of the product of all the displayed variables. -/
def top {R : Type u} : (n : Nat) → Poly R n → R
  | 0, p => p
  | n + 1, p => top n p.2

theorem top_eq_zero_of_vanishing {R : Type u} (zero : R)
    (add : R → R → R) (zero_add : ∀ a, add zero a = a) :
    ∀ (n : Nat) (p : Poly R n),
      (∀ x, eval add n p x = zero) → top n p = zero := by
  intro n
  induction n with
  | zero =>
    intro p h
    exact h ()
  | succ n ih =>
    intro p h
    apply ih p.2
    intro x
    have h₀ : eval add n p.1 x = zero := h (false, x)
    have h₁ : add (eval add n p.1 x) (eval add n p.2 x) = zero :=
      h (true, x)
    simpa [h₀, zero_add] using h₁

theorem nonzero_point {R : Type u} (zero : R) (add : R → R → R)
    (zero_add : ∀ a, add zero a = a) (n : Nat) (p : Poly R n)
    (h : top n p ≠ zero) : ∃ x, eval add n p x ≠ zero := by
  classical
  apply Classical.byContradiction
  intro hn
  apply h
  apply top_eq_zero_of_vanishing zero add zero_add n p
  intro x
  apply Classical.byContradiction
  intro hx
  exact hn ⟨x, hx⟩

/-- Sum over every Boolean assignment, counted once. -/
def cubeSum : (n : Nat) → (Bits n → Nat) → Nat
  | 0, f => f ()
  | n + 1, f =>
    cubeSum n (fun x => f (false, x)) + cubeSum n (fun x => f (true, x))

theorem one_le_cubeSum_of_point :
    ∀ (n : Nat) (f : Bits n → Nat) (x : Bits n),
      1 ≤ f x → 1 ≤ cubeSum n f := by
  intro n
  induction n with
  | zero =>
    intro f x h
    cases x
    exact h
  | succ n ih =>
    intro f x h
    obtain ⟨b, x⟩ := x
    cases b with
    | false =>
      have hh := ih (fun y => f (false, y)) x h
      simp only [cubeSum]
      omega
    | true =>
      have hh := ih (fun y => f (true, y)) x h
      simp only [cubeSum]
      omega

theorem pow_le_cubeSum_of_positive :
    ∀ (n : Nat) (f : Bits n → Nat), (∀ x, 1 ≤ f x) → 2 ^ n ≤ cubeSum n f := by
  intro n
  induction n with
  | zero =>
    intro f h
    exact h ()
  | succ n ih =>
    intro f h
    have h₀ := ih (fun x => f (false, x)) (fun x => h (false, x))
    have h₁ := ih (fun x => f (true, x)) (fun x => h (true, x))
    simp only [cubeSum, Nat.pow_succ]
    omega

theorem cubeSum_one (n : Nat) : cubeSum n (fun _ => 1) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeSum, ih, Nat.pow_succ]
    omega

/-- Among 2^outside * 2^e points, the support contains at least 2^outside
points. The outside assignment may change every other coefficient. -/
theorem support_count {R : Type u} [DecidableEq R] (zero : R)
    (add : R → R → R) (zero_add : ∀ a, add zero a = a)
    (outside e : Nat) (family : Bits outside → Poly R e)
    (leading : ∀ z, top e (family z) ≠ zero) :
    2 ^ outside ≤
      cubeSum outside (fun z => cubeSum e (fun x =>
        if eval add e (family z) x = zero then 0 else 1)) := by
  apply pow_le_cubeSum_of_positive
  intro z
  obtain ⟨x, hx⟩ := nonzero_point zero add zero_add e (family z) (leading z)
  apply one_le_cubeSum_of_point e _ x
  simp [hx]

/-- Homogeneous labels suffice for finite, possibly different bundle domains:
each edge may use any subset of the common label type. -/
def Labels (L : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => L × Labels L n

private def zeroPoly {R : Type u} (zero : R) : (n : Nat) → Poly R n
  | 0 => zero
  | n + 1 => (zeroPoly zero n, zeroPoly zero n)

private def addPoly {R : Type u} (add : R → R → R) :
    (n : Nat) → Poly R n → Poly R n → Poly R n
  | 0, a, b => add a b
  | n + 1, a, b => (addPoly add n a.1 b.1, addPoly add n a.2 b.2)

private theorem top_zero {R : Type u} (z : R) (n : Nat) :
    top n (zeroPoly z n) = z := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem top_add {R : Type u} (add : R → R → R) :
    ∀ (n : Nat) (p q : Poly R n),
      top n (addPoly add n p q) = add (top n p) (top n q) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intro p q; exact ih p.2 q.2

private theorem eval_zero {R : Type u} (zero : R) (add : R → R → R)
    (zero_add : ∀ a, add zero a = a) :
    ∀ (n : Nat) (x : Bits n), eval add n (zeroPoly zero n) x = zero := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro ⟨b,x⟩
    cases b <;> simp [eval, zeroPoly, ih, zero_add]

private theorem eval_add {R : Type u} (add : R → R → R)
    (exchange : ∀ a b c d, add (add a b) (add c d) = add (add a c) (add b d)) :
    ∀ (n : Nat) (p q : Poly R n) (x : Bits n),
      eval add n (addPoly add n p q) x = add (eval add n p x) (eval add n q x) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro p q ⟨b,x⟩
    cases b <;> simp only [eval, addPoly, Bool.false_eq_true, ↓reduceIte, ih]
    apply exchange

universe v

/-- For each bundle, read its distinguished free bit if the two labels agree;
otherwise read the bit selected by the fixed outside filter at that label.
A term survives precisely when all its bundle tests succeed. -/
def enabled {L : Type v} [DecidableEq L] :
    (n : Nat) → Labels L n → Labels L n → Labels (L → Bool) n → Bits n → Bool
  | 0, _, _, _, _ => true
  | n + 1, target, row, fixed, x =>
    (if target.1 = row.1 then x.1 else fixed.1 row.1) &&
      enabled n target.2 row.2 fixed.2 x.2

private def termPoly {R : Type u} {L : Type v} [DecidableEq L] (zero : R) :
    (n : Nat) → Labels L n → Labels L n → Labels (L → Bool) n → R → Poly R n
  | 0, _, _, _, c => c
  | n + 1, target, row, fixed, c =>
    let tail := termPoly zero n target.2 row.2 fixed.2 c
    let empty := zeroPoly zero n
    if target.1 = row.1 then (empty, tail)
    else (if fixed.1 row.1 then tail else empty, empty)

private theorem top_target {R : Type u} {L : Type v} [DecidableEq L]
    (zero : R) (c : R) :
    ∀ (n : Nat) (target : Labels L n) (fixed : Labels (L → Bool) n),
      top n (termPoly zero n target target fixed c) = c := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intro target fixed; simpa [termPoly, top] using ih target.2 fixed.2

private theorem top_different {R : Type u} {L : Type v} [DecidableEq L]
    (zero : R) (c : R) :
    ∀ (n : Nat) (target row : Labels L n) (fixed : Labels (L → Bool) n),
      row ≠ target → top n (termPoly zero n target row fixed c) = zero := by
  intro n
  induction n with
  | zero =>
    intro target row fixed h
    cases target
    cases row
    exact False.elim (h rfl)
  | succ n ih =>
    intro ⟨a,tt⟩ ⟨b,rr⟩ fixed h
    by_cases hab : a = b
    · subst b
      have ht : rr ≠ tt := fun hr => h (by rw [hr])
      simpa [termPoly, top] using ih tt rr fixed.2 ht
    · simp [termPoly, top, hab, top_zero]

private theorem eval_term {R : Type u} {L : Type v} [DecidableEq L]
    (zero : R) (add : R → R → R)
    (zero_add : ∀ a, add zero a = a) (add_zero : ∀ a, add a zero = a) (c : R) :
    ∀ (n : Nat) (target row : Labels L n) (fixed : Labels (L → Bool) n) (x : Bits n),
      eval add n (termPoly zero n target row fixed c) x =
        (if enabled n target row fixed x then c else zero) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro ⟨a,tt⟩ ⟨b,rr⟩ ⟨f,fs⟩ ⟨bit,bs⟩
    by_cases h : a = b <;> cases bit <;> cases hh : f b <;>
      simp [termPoly, eval, enabled, h, hh, eval_zero zero add zero_add,
        ih, zero_add, add_zero]

/-- The scalar contraction on fixed external data. A row is a global
internal labeling and its weight. Ordinary indicator relations use weight one. -/
def contraction {R : Type u} {L : Type v} [DecidableEq L] (zero : R)
    (add : R → R → R) {e : Nat} (target : Labels L e)
    (fixed : Labels (L → Bool) e) (x : Bits e) (rows : List (Labels L e × R)) : R :=
  rows.foldr (fun rc s => add (if enabled e target rc.1 fixed x then rc.2 else zero) s) zero

private def relationPoly {R : Type u} {L : Type v} [DecidableEq L] (zero : R)
    (add : R → R → R) {e : Nat} (target : Labels L e)
    (fixed : Labels (L → Bool) e) (rows : List (Labels L e × R)) : Poly R e :=
  rows.foldr (fun rc p => addPoly add e (termPoly zero e target rc.1 fixed rc.2) p)
    (zeroPoly zero e)

private theorem eval_relation {R : Type u} {L : Type v} [DecidableEq L]
    (zero : R) (add : R → R → R) (zero_add : ∀ a, add zero a = a)
    (add_zero : ∀ a, add a zero = a)
    (exchange : ∀ a b c d, add (add a b) (add c d) = add (add a c) (add b d))
    {e : Nat} (target : Labels L e) (fixed : Labels (L → Bool) e) (x : Bits e)
    (rows : List (Labels L e × R)) :
    eval add e (relationPoly zero add target fixed rows) x =
      contraction zero add target fixed x rows := by
  induction rows with
  | nil => exact eval_zero zero add zero_add e x
  | cons rc rest ih =>
    simp only [relationPoly, contraction, List.foldr_cons] at ih ⊢
    rw [eval_add add exchange, eval_term zero add zero_add add_zero, ih]

private theorem top_others {R : Type u} {L : Type v} [DecidableEq L]
    (zero : R) (add : R → R → R) (zero_add : ∀ a, add zero a = a)
    {e : Nat} (target : Labels L e) (fixed : Labels (L → Bool) e)
    (others : List (Labels L e × R)) (unique : ∀ rc ∈ others, rc.1 ≠ target) :
    top e (relationPoly zero add target fixed others) = zero := by
  induction others with
  | nil => exact top_zero zero e
  | cons rc rest ih =>
    have hrc := unique rc (List.mem_cons_self)
    have hr := ih (fun t ht => unique t (List.mem_cons_of_mem rc ht))
    simp only [relationPoly, List.foldr_cons] at hr ⊢
    rw [top_add, top_different zero _ _ target rc.1 fixed hrc, hr, zero_add]

/-- Finite bundle-labeling filter, including the top-monomial step.
Select one nonzero labeling from the relation. No other row may equal that
labeling; arbitrary other rows may repeat or have arbitrary weights. Outside
assignments choose any fixed filters for the remaining labels. Every outside
fiber contains a surviving contraction across the 2^e distinguished bits.
The additive hypotheses hold for every field, in every characteristic. -/
theorem labeling_filter_support {R : Type u} [DecidableEq R] {L : Type v} [DecidableEq L]
    (zero : R) (add : R → R → R)
    (zero_add : ∀ a, add zero a = a) (add_zero : ∀ a, add a zero = a)
    (exchange : ∀ a b c d, add (add a b) (add c d) = add (add a c) (add b d))
    (outside e : Nat) (target : Labels L e) (c : R) (hc : c ≠ zero)
    (others : List (Labels L e × R)) (unique : ∀ rc ∈ others, rc.1 ≠ target)
    (fixed : Bits outside → Labels (L → Bool) e) :
    2 ^ outside ≤ cubeSum outside (fun z => cubeSum e (fun x =>
      if contraction zero add target (fixed z) x ((target, c) :: others) = zero
      then 0 else 1)) := by
  let rows := (target, c) :: others
  have htop (z : Bits outside) : top e (relationPoly zero add target (fixed z) rows) ≠ zero := by
    have hr := top_others zero add zero_add target (fixed z) others unique
    simp only [rows, relationPoly, List.foldr_cons] at hr ⊢
    rwa [top_add, top_target, hr, add_zero]
  have hh := support_count zero add zero_add outside e
    (fun z => relationPoly zero add target (fixed z) rows) htop
  simpa only [eval_relation zero add zero_add add_zero exchange, rows] using hh

end BundleSupportFilter
