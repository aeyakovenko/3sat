import Std

/-! Finite arithmetic for a checkpoint argument with logarithmic losses.

The positive integer L represents a logarithm of the input length. A run uses
at most T * L^a steps and has configurations of size s with s * L^b ≤ T.
Using L^u segments charges an extra L^c per configuration and L^d per
replayed step. The gain g is measured *before* subsequent language
translations. This file does not assume a machine simulation or a SAT bound.
-/

namespace BandTimeSpace

/-- Feasibility of a single segmentation exponent, including unequal costs. -/
theorem existsSplit (a b c d g : Nat) :
    (∃ u : Nat, a + d + g ≤ u ∧ u + c + g ≤ b) ↔
      a + c + d + 2 * g ≤ b := by
  constructor
  · rintro ⟨u, hu, hv⟩
    omega
  · intro h
    exact ⟨a + d + g, Nat.le_refl _, by omega⟩

/-- Using the integer quotient plus one as a rounded-up budget costs at most
one unit, including at exact divisibility. -/
theorem roundedBudget (t p : Nat) (hp : 0 < p) :
    t ≤ (t / p + 1) * p := by
  have hsum := Nat.div_add_mod t p
  have hlt := Nat.mod_lt t hp
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (t / p) p]
  omega

/-- Underlying finite resource estimates. The replay bound counts *whole*
steps after segmentation. Its additive rounding cost is one replayed step. -/
theorem segmentBounds {l t runtime s r a b c d g u : Nat}
    (hl : 0 < l) (hbudget : t ≤ r * l ^ g)
    (htime : runtime ≤ t * l ^ a) (hspace : s * l ^ b ≤ t)
    (hu : a + d + g ≤ u) (hv : u + c + g ≤ b) :
    s * l ^ (u + c) ≤ r ∧
    (runtime / l ^ u + 1) * l ^ d ≤ r + l ^ d := by
  constructor
  · apply Nat.le_of_mul_le_mul_right (c := l ^ g) _ (Nat.pow_pos hl)
    calc
      s * l ^ (u + c) * l ^ g = s * l ^ (u + c + g) := by
        rw [Nat.pow_add l (u + c) g, Nat.mul_assoc]
      _ ≤ s * l ^ b := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hl hv)
      _ ≤ t := hspace
      _ ≤ r * l ^ g := hbudget
  · have hwork : runtime * l ^ d ≤ r * l ^ u := by
      calc
        runtime * l ^ d ≤ t * l ^ a * l ^ d := Nat.mul_le_mul_right _ htime
        _ ≤ (r * l ^ g) * l ^ a * l ^ d :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hbudget)
        _ = r * l ^ (a + d + g) := by
          rw [Nat.pow_add l (a + d) g, Nat.pow_add l a d]
          ac_rfl
        _ ≤ r * l ^ u := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hl hu)
    have hfloor : runtime / l ^ u * l ^ d ≤ r := by
      apply Nat.le_of_mul_le_mul_right (c := l ^ u) _ (Nat.pow_pos hl)
      calc
        runtime / l ^ u * l ^ d * l ^ u = (runtime / l ^ u * l ^ u) * l ^ d := by
          ac_rfl
        _ ≤ runtime * l ^ d := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
        _ ≤ r * l ^ u := hwork
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Choose the splitter and both integer budgets solely from the given data. -/
theorem segmentWithGain {l t runtime s a b c d g : Nat}
    (hl : 0 < l) (htime : runtime ≤ t * l ^ a) (hspace : s * l ^ b ≤ t)
    (hband : a + c + d + 2 * g ≤ b) :
    ∃ u : Nat,
      s * l ^ (u + c) ≤ t / l ^ g + 1 ∧
      (runtime / l ^ u + 1) * l ^ d ≤ (t / l ^ g + 1) + l ^ d := by
  obtain ⟨u, hu, hv⟩ := (existsSplit a b c d g).mpr hband
  exact ⟨u, segmentBounds hl (roundedBudget t _ (Nat.pow_pos hl)) htime hspace hu hv⟩

/-- A recursive call can raise its clock to the input length. The charge
for the additional work is absorbed by the separate input term when the
work multiplier does not exceed the input multiplier. -/
theorem inputGuard {n t p q : Nat} (hpq : p ≤ q) :
    max n t * p + n * q ≤ t * p + 2 * (n * q) := by
  rw [Nat.max_def]
  split
  · omega
  · have h := Nat.mul_le_mul_left n hpq
    omega

/-- The two crossover terms are the cost of the checkpoint input to the
inner computation and the cost of its replay, respectively. -/
def nextExponent (a b e u : Int) : Int :=
  max (a + u - b) (a + e - u)

/-- Twice the optimal exponent is 2a + e - b whenever the two terms
meet at a point of the exponent grid. -/
theorem midpointBound (a b e u : Int) :
    2 * a + e - b ≤ 2 * nextExponent a b e u := by
  have h₁ := Int.le_max_left (a + u - b) (a + e - u)
  have h₂ := Int.le_max_right (a + u - b) (a + e - u)
  unfold nextExponent
  omega

theorem midpointEquality {a b e u : Int} (h : 2 * u = b + e) :
    2 * nextExponent a b e u = 2 * a + e - b := by
  unfold nextExponent
  rw [Int.max_def]
  split <;> omega

/-- If b = 2a + h, the balanced update is e ↦ (e - h)/2.
The exponent at step j is this signed numerator divided by 2^j. -/
def midpointNumerator (a h : Nat) (j : Nat) : Int :=
  (a : Int) + h - (2 : Int)^j * h

theorem midpointStart (a h : Nat) : midpointNumerator a h 0 = a := by
  simp [midpointNumerator]

theorem midpointUpdate (a h j : Nat) :
    midpointNumerator a h (j+1) =
      midpointNumerator a h j - (2 : Int)^j * h := by
  simp only [midpointNumerator, Int.pow_succ]
  have eq : ((2 : Int)^j * 2) * h = (2 : Int)^j * h + (2 : Int)^j * h := by
    rw [show (2 : Int) = 1+1 from rfl, Int.mul_add, Int.mul_one, Int.add_mul]
  omega

theorem midpointCrosses {a h : Nat} (hh : 0 < h) :
    ∃ j : Nat, midpointNumerator a h j < 0 := by
  let j := a + h
  refine ⟨j, ?_⟩
  have hpow : a + h < (2 : Nat)^j := Nat.lt_two_pow_self
  have hmul := Nat.mul_le_mul_left ((2 : Nat)^j) (show 1 ≤ h by omega)
  rw [Nat.mul_one] at hmul
  have hbig : (a : Int) + h < ((2 : Nat)^j : Nat) * (h : Int) := by
    exact_mod_cast (show a + h < (2 : Nat)^j * h by omega)
  rw [Int.natCast_pow] at hbig
  change (a : Int) + h < (2 : Int)^j * h at hbig
  unfold midpointNumerator
  omega

/-- Alternatively, one fixed splitting exponent a+g decreases every live
work exponent by at least g, until reaching exponent at most -g. -/
theorem fixedSplitStep {a b g e : Int} (hb : 2*a + 2*g ≤ b) :
    nextExponent a b e (a+g) ≤ max (-g) (e-g) := by
  unfold nextExponent
  apply Int.max_le.mpr
  constructor
  · have h := Int.le_max_left (-g) (e-g)
    omega
  · have h := Int.le_max_right (-g) (e-g)
    omega

/-- With one unit of strict progress available, a+1 rounds give
a negative work exponent. The input exponent remains a. -/
theorem fixedSplitCrosses {a b : Nat} (hb : 2*a + 2 ≤ b)
    (e : Nat → Int) (hstart : e 0 ≤ (a : Int))
    (hstep : ∀ j, e (j+1) ≤ nextExponent a b (e j) (a+1)) :
    e (a+1) ≤ -1 := by
  have hband : 2*(a : Int) + 2*(1 : Int) ≤ b := by exact_mod_cast hb
  have hall (j : Nat) : e j ≤ max (-1) ((a : Int) - j) := by
    induction j with
    | zero =>
      have h := Int.le_max_right (-1) ((a : Int) - (0 : Nat))
      omega
    | succ j ih =>
      have hs := hstep j
      have h := fixedSplitStep (a := (a : Int)) (b := (b : Int)) (g := 1)
        (e := e j) hband
      rw [Int.max_def] at ih h ⊢
      split at ih <;> split at h <;> split <;> omega
  have h := hall (a+1)
  rw [Int.max_def] at h
  split at h <;> omega

/-- Each accepting and rejecting halted state is taken to have an idle step
when this iteration is used to model a padded clock. -/
def advance (step : State → State) : Nat → State → State
  | 0, s => s
  | k + 1, s => step (advance step k s)

theorem advance_add (step : State → State) (first second : Nat) (s : State) :
    advance step (first + second) s = advance step second (advance step first s) := by
  induction second with
  | zero => rfl
  | succ n ih =>
    change step (advance step (first + n) s) = step (advance step n (advance step first s))
    rw [ih]

theorem idleAfterHalt {step : State → State} {s : State} (halted : step s = s) (n : Nat) :
    advance step n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [advance, ih] using halted

/-- Endpoint acceptance of the full padded computation is equivalent to
guessing exactly p+1 states with the specified endpoints and finding no
defective segment among the p choices. -/
theorem checkpointCertificate (step : State → State) (s : State) (accept : State → Prop)
    (p h : Nat) :
    accept (advance step (p*h) s) ↔
      ∃ cuts : Fin (p+1) → State, cuts 0 = s ∧ accept (cuts (Fin.last p)) ∧
        ¬ ∃ i : Fin p, cuts i.succ ≠ advance step h (cuts i.castSucc) := by
  constructor
  · intro hacc
    refine ⟨fun i => advance step (i.val*h) s, ?_, ?_, ?_⟩
    · simp [advance]
    · simpa using hacc
    · rintro ⟨i, wrong⟩
      apply wrong
      change advance step ((i.val+1)*h) s = advance step h (advance step (i.val*h) s)
      rw [Nat.succ_mul, advance_add]
  · rintro ⟨cuts, hzero, hacc, consistent⟩
    have unique (i : Fin (p+1)) : cuts i = advance step (i.val*h) s := by
      induction i using Fin.induction with
      | zero => simpa [advance] using hzero
      | succ i ih =>
        have ok : cuts i.succ = advance step h (cuts i.castSucc) := by
          apply Classical.byContradiction
          intro wrong
          exact consistent ⟨i, wrong⟩
        rw [ok, ih]
        change advance step h (advance step (i.val*h) s) = advance step ((i.val+1)*h) s
        rw [Nat.succ_mul, advance_add]
    simpa [unique (Fin.last p)] using hacc

/-- Source is the hierarchy source class. Co e represents a complementary
machine with work bound t times log^e and the separate original-input
charge; containment is supplied explicitly by the simulation hypotheses. -/
def simulationAt {Language : Type} (Source : Language → Prop)
    (Co : Int → Language → Prop) (e : Int) : Prop :=
  ∀ lang, Source lang → Co e lang

/-- The finite arithmetic forces a contradiction when the external machine
lemmas supply its initial simulation, one improvement for each live exponent,
and a hierarchy witness excluded at exponent -1. -/
theorem bandHierarchyContradiction {Language : Type} (Source : Language → Prop)
    (Co : Int → Language → Prop) {a b : Nat} (hb : 2*a+2 ≤ b)
    (budgetMono : ∀ e f : Int, e ≤ f → ∀ lang, Co e lang → Co f lang)
    (initialSimulation : simulationAt Source Co a)
    (eliminateBoundedRun : ∀ e : Int, 0 ≤ e → e ≤ a → simulationAt Source Co e →
      simulationAt Source Co (nextExponent a b e (a+1)))
    (separated : ∃ lang, Source lang ∧ ¬ Co (-1) lang) : False := by
  let e : Nat → Int := Nat.rec (a : Int) (fun _ old => nextExponent a b old (a+1))
  have first : e 0 = a := rfl
  have step (j : Nat) : e (j+1) = nextExponent a b (e j) (a+1) := rfl
  have hband : 2*(a : Int) + 2*(1 : Int) ≤ b := by exact_mod_cast hb
  have upper (j : Nat) : e j ≤ a := by
    induction j with
    | zero => omega
    | succ j ih =>
      rw [step]
      have hs := fixedSplitStep (e := e j) hband
      rw [Int.max_def] at hs
      split at hs <;> omega
  obtain ⟨witness, inSource, excluded⟩ := separated
  have nonneg {work : Int} (simulation : simulationAt Source Co work) : 0 ≤ work := by
    apply Classical.byContradiction
    intro h
    exact excluded (budgetMono work (-1) (by omega) witness (simulation witness inSource))
  have every (j : Nat) : simulationAt Source Co (e j) := by
    induction j with
    | zero => simpa only [first] using initialSimulation
    | succ j ih => exact eliminateBoundedRun (e j) (nonneg ih) (upper j) ih
  have low := fixedSplitCrosses hb e (by omega) (fun j => by rw [step]; exact Int.le_refl _)
  have high := nonneg (every (a+1))
  omega

/-- In half-log units, A=a+3 and B=b-2 leave the two units of slack
needed by the fixed splitter when b≥2a+9. -/
theorem doubledPackedBand {a b : Nat} (h : 2*a+9 ≤ b) :
    2*(2*(a+3))+2 ≤ 2*(b-2) := by omega

/-- The terms on one final two-level check are the first list, the second
list's input charge, and the twice-slowed final replay. -/
def twoLevelExponent (a b e u v : Int) :=
  max (a+u-b) (max (a+v-b+e) (a-u-v+2*e))

/-- In thirds of an exponent unit, u=e+b/3 and v=b/3 balance all
three terms. -/
theorem twoLevelBalanced (a b e : Int) :
    twoLevelExponent (3*a) (3*b) (3*e) (3*e+b) b = 3*e+3*a-2*b := by
  simp only [twoLevelExponent, Int.max_def]
  split <;> split <;> omega

/-- In twelfths of a unit, b=2a, e=a/4, u=11a/12 and v=2a/3
incur the common exponent -a/12. -/
theorem equalityBandTwoLevels (a : Int) :
    12*a+11*a-24*a = -a ∧
    12*a+8*a-24*a+3*a = -a ∧
    12*a-11*a-8*a+2*(3*a) = -a := by omega

/-- In quarter units: (a,b)=(3,6), two midpoint reductions from 3 to
3/2 to 3/4, then two checkpoints of widths 11/4 and 2. -/
theorem packedEndpoint :
    nextExponent 12 24 12 18 = 6 ∧ nextExponent 12 24 6 15 = 3 ∧
    twoLevelExponent 12 24 3 11 8 = -1 := by decide

/-- One last three-level check uses four input and replay terms. The
branching exponents, expressed in fourths, are b+6e, b+2e, b-2e.
The latter must be nonnegative when applying this algebra to a machine. -/
theorem threeLevelBalanced (a b e : Int) :
    4*a+(b+6*e)-4*b = 4*a-3*b+6*e ∧
    4*a+(b+2*e)-4*b+4*e = 4*a-3*b+6*e ∧
    4*a+(b-2*e)-4*b+8*e = 4*a-3*b+6*e ∧
    4*a-(b+6*e)-(b+2*e)-(b-2*e)+12*e = 4*a-3*b+6*e := by omega

/-- A run exponent e above the one-level fixed point by a gap d still
gives a strictly negative three-level terminal exponent when 6d is below
the stated margin. The same statement holds on every fixed rational grid. -/
theorem threeLevelSlack {a b e d : Int} (he : e ≤ 2*a-b+d)
    (hmargin : 6*d < 9*b-16*a) :
    4*a-3*b+6*e < 0 := by omega

/-- Here the input-dependent part of the direct leaf reduction has its
own cost m*L^p. The two terms pay for preparing the full checkpoint-list
input and for replaying the deterministic segment. No replacement of the
shorter replay clock by m is made. -/
def splitWithInputCost (a b e p u : Int) : Int :=
  max (p+u-b) (a+e-u)

/-- At B=A+p, two successive cuts have widths 3A/2 and 5A/4.
Fourths of an exponent unit avoid division. The first cut uses a direct
leaf with work exponent A even if A>p. -/
theorem separateInputSteps (a p : Int) :
    splitWithInputCost (4*a) (4*(a+p)) (4*a) (4*p) (6*a) = 2*a ∧
    splitWithInputCost (4*a) (4*(a+p)) (2*a) (4*p) (5*a) = a := by
  simp only [splitWithInputCost, Int.max_def]
  constructor <;> split <;> omega

/-- At stage three the exponent A/4 is used twice. The first and second
checkpoint arrays and the final replay all cost t*L^(-A/12). The last
inequality pays for reading the two endpoints even without a nonempty
array at that level. -/
theorem separateInputFinish {a p : Int} (ha : 0 ≤ a) :
    11*a - 12*(a+p) + 12*p = -a ∧
    8*a - 12*(a+p) + 12*p + 3*a = -a ∧
    12*a - 11*a - 8*a + 2*(3*a) = -a ∧
    12*p + 3*a - 12*(a+p) ≤ -a := by omega

/-- In the packed model A=a+3 and p=a+2. Both newly obtained nonnegative
work exponents fit the input guard p. If b≥2a+7, B=b-2 is at least A+p.
Space beyond that bound can be ignored. -/
theorem separateInputPackedBand {a b : Nat} (hb : 2*a+7 ≤ b) :
    a+3 ≤ 2*(a+2) ∧ a+3 ≤ 4*(a+2) ∧ (a+3)+(a+2) ≤ b-2 := by omega

/-- Cost of the final nested elimination, including the endpoint term. -/
def nestedWithInputCost (a b e f u v : Int) : Int :=
  max (f+u-b) (max (f+v-b+e) (max (a-u-v+2*e) (f+e-b)))

/-- H(e,f) denotes a complement simulation with work and input exponents
e/12 and f/12. The machine-specific transfer lemmas are parameters. The
one-level width restriction ensures that replaying a segment can pay to
initialize its selected configuration. -/
structure CheckpointTransfers (H : Int → Int → Prop) (A B p : Int) : Prop where
  directLeaf : ∀ u : Int, 0 ≤ u → u ≤ 12*(A+B) →
    H (splitWithInputCost (12*A) (12*B) (12*A) (12*p) u) (12*p)
  guardedOneLevel : ∀ e f u : Int, 0 ≤ e → e ≤ f → 0 ≤ u → u ≤ 12*(A+B) →
    H e f → H (splitWithInputCost (12*A) (12*B) e f u) f
  nestedTwoLevels : ∀ e f u v : Int, 0 ≤ e → e ≤ f → 0 ≤ u → 0 ≤ v →
    H e f → H (nestedWithInputCost (12*A) (12*B) e f u v) (f+e)

/-- Apply all three transfers. Available extra space saving beyond A+p
only reduces the checkpoint costs; the final replay fixes the maximum. -/
theorem applySeparateInputTransfers {H : Int → Int → Prop} {A B p : Int}
    (ha : 0 < A) (hp : A ≤ 2*p) (hb : A+p ≤ B)
    (rules : CheckpointTransfers H A B p) : H (-A) (12*p+3*A) := by
  have steps := separateInputSteps (3*A) (3*p)
  have hfin := separateInputFinish (p := p) (a := A) (by omega)
  have cost₁ : splitWithInputCost (12*A) (12*B) (12*A) (12*p) (18*A) = 6*A := by
    simp only [splitWithInputCost, Int.max_def] at steps ⊢
    split <;> omega
  have cost₂ : splitWithInputCost (12*A) (12*B) (6*A) (12*p) (15*A) = 3*A := by
    simp only [splitWithInputCost, Int.max_def] at steps ⊢
    split <;> omega
  have cost₃ : nestedWithInputCost (12*A) (12*B) (3*A) (12*p) (11*A) (8*A) = -A := by
    simp only [nestedWithInputCost, Int.max_def]
    split <;> split <;> split <;> omega
  have first := rules.directLeaf (18*A) (by omega) (by omega)
  rw [cost₁] at first
  have second := rules.guardedOneLevel (6*A) (12*p) (15*A)
    (by omega) (by omega) (by omega) (by omega) first
  rw [cost₂] at second
  have last := rules.nestedTwoLevels (3*A) (12*p) (11*A) (8*A)
    (by omega) (by omega) (by omega) (by omega) second
  rwa [cost₃] at last

/-- A two-parameter containment retains the input exponent in its conclusions. -/
def guardedContainment {Language : Type} (Source : Language → Prop)
    (Co : Int → Int → Language → Prop) (e f : Int) : Prop :=
  ∀ lang, Source lang → Co e f lang

/-- At b≥2a+7, the three listed machine-transfer lemmas are inconsistent
with a hierarchy separating every negative work exponent at every fixed input
exponent. All exponents passed to Co are measured in twelfths. -/
theorem packedSevenHierarchyContradiction {Language : Type} (Source : Language → Prop)
    (Co : Int → Int → Language → Prop) {a b : Nat} (hb : 2*a+7 ≤ b)
    (rules : CheckpointTransfers (guardedContainment Source Co)
      ((a : Int)+3) ((b : Int)-2) ((a : Int)+2))
    (hierarchy : ∀ e f : Int, e < 0 → ∃ lang, Source lang ∧ ¬ Co e f lang) : False := by
  have hp := separateInputPackedBand hb
  have fast := applySeparateInputTransfers (by omega) (by omega) (by omega) rules
  obtain ⟨lang, inSource, excluded⟩ := hierarchy (-((a : Int)+3))
    (12*((a : Int)+2)+3*((a : Int)+3)) (by omega)
  exact excluded (fast lang inSource)

end BandTimeSpace
