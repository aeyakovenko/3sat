import Std

namespace MultitraceWitnesses

private theorem countOr {X : Type} (xs : List X) (a b : X → Bool) :
    xs.countP (fun x => a x || b x) ≤ xs.countP a + xs.countP b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases h : a x <;> cases j : b x <;> simp [List.countP_cons, h, j] <;> omega

private theorem countAny {X Y : Type} (xs : List X) (ys : List Y) (hit : Y → X → Bool) :
    xs.countP (fun x => ys.any (fun y => hit y x)) ≤
      (ys.map (fun y => xs.countP (hit y))).sum := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    have head := countOr xs (hit y) (fun x => ys.any (fun z => hit z x))
    simpa [List.any_cons] using Nat.le_trans head (Nat.add_le_add_left ih (xs.countP (hit y)))

/-- If the total number of seed-list failures over coordinates is below the
    number of equally likely candidate lists, some whole list succeeds on
    every coordinate. Errors on different coordinates may be dependent. -/
theorem oneListWins {Row Coord : Type} (rows : List Row) (coords : List Coord)
    (wrong : Coord → Row → Bool)
    (small : (coords.map (fun i => rows.countP (wrong i))).sum < rows.length) :
    ∃ row ∈ rows, ∀ i ∈ coords, wrong i row = false := by
  apply Classical.byContradiction
  intro no
  have full : rows.countP (fun r => coords.any (fun i => wrong i r)) = rows.length := by
    apply List.countP_eq_length.mpr
    intro r hr
    cases hh : coords.any (fun i => wrong i r) with
    | true => rfl
    | false =>
      exfalso
      apply no
      refine ⟨r,hr,?_⟩
      intro i hi
      cases h : wrong i r with
      | false => rfl
      | true =>
        have bad := List.any_eq_true.mpr (show ∃ j ∈ coords, wrong j r = true from ⟨i,hi,h⟩)
        simp [hh] at bad
  have upper := countAny rows coords wrong
  omega

private def parity (ys : List Bool) : Bool := ys.foldr xor false

private theorem parityHit {Y : Type} (ys : List Y) (t : Y → Bool)
    (h : parity (ys.map t) = true) : ys.any t = true := by
  induction ys with
  | nil => simp [parity] at h
  | cons y ys ih =>
    cases a : t y with
    | true => simp [a]
    | false =>
      simp [parity, a] at h
      exact (by simpa [a] using ih h)

private theorem onesSum {Y : Type} (ys : List Y) (f : Y → Nat)
    (h : ∀ y ∈ ys, f y ≤ 1) : (ys.map f).sum ≤ ys.length := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    have ht := ih (fun z hz => h z (by simp [hz]))
    have hh := h y (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Each available correcting wire touches at most one hidden position.
    Flipping every hidden position needs at least as many named wires. -/
theorem manyCorrections {Wire Coord : Type} (selected : List Wire) (hidden : List Coord)
    (tangent : Wire → Coord → Bool)
    (thin : ∀ g ∈ selected, hidden.countP (tangent g) ≤ 1)
    (fixes : ∀ i ∈ hidden, parity (selected.map (fun g => tangent g i)) = true) :
    hidden.length ≤ selected.length := by
  have allHit : hidden.countP (fun i => selected.any (fun g => tangent g i)) = hidden.length := by
    apply List.countP_eq_length.mpr
    intro i hi
    exact parityHit selected _ (fixes i hi)
  have cover := countAny hidden selected tangent
  have upper := onesSum selected (fun g => hidden.countP (tangent g)) thin
  omega

inductive Group where
  | a | b | c | d
  deriving DecidableEq, Repr

def groups : List Group := [.a,.b,.c,.d]

def forecast (hidden position : Group) (target : Bool) : Bool :=
  if hidden = position then false else target

def vote (values : List Bool) : Bool :=
  decide (values.length < 2 * values.countP id)

/-- All four chosen traces jointly predict the correct coefficient. A true
    data bit is missed only on its own group's trace. -/
theorem fourTraceVote (position : Group) (target : Bool) :
    vote (groups.map (fun h => forecast h position target)) = target := by
  cases position <;> cases target <;> decide

/-- A pair gives the Boolean value and the formal F₂ variation on a fixed
    direction, before any idempotence simplification of the gate list. -/
private def vadd (a b : Bool × Bool) := (xor a.1 b.1, xor a.2 b.2)

private def vmul (a b : Bool × Bool) :=
  (a.1 && b.1, xor (a.1 && b.2) (b.1 && a.2))

/-- The Boolean-null term (x² + x)h leaves the value unchanged and adds
    h times the direction of x to the gradient, at every baseline,
    regardless of the implementation and derivative of h. -/
theorem silentCorrection (x dx h dh : Bool) :
    vmul (vadd (vmul (x,dx) (x,dx)) (x,dx)) (h,dh) = (false,dx && h) := by
  cases x <;> cases dx <;> cases h <;> cases dh <;> rfl

end MultitraceWitnesses
