import Std

/-! Finite replay facts for chronological RAM graphs cut into components.
At one address, a read may use any retained write after the last change away
from its claimed value. The cut and both selected groups have fixed records. -/

namespace SlabProduct

def wordAt (initial : W) (store : Nat → Option W) : Nat → W
  | 0 => initial
  | t+1 => (store t).getD (wordAt initial store t)

/-- If the initial word of a suffix is right and every write on that suffix
agrees with it, the final word is right. -/
theorem stableSuffix (initial value : W) (store : Nat → Option W) {start stop : Nat}
    (order : start ≤ stop) (atStart : wordAt initial store start = value)
    (writes : ∀ j, start ≤ j → j < stop → ∀ v, store j = some v → v = value) :
    wordAt initial store stop = value := by
  induction stop with
  | zero =>
    obtain rfl : start = 0 := by omega
    exact atStart
  | succ t ih =>
    by_cases atEnd : start = t+1
    · simpa [atEnd] using atStart
    · have prev := ih (by omega) (fun j hj ht => writes j hj (by omega))
      cases hs : store t with
      | none => simpa [wordAt, hs] using prev
      | some w => simpa [wordAt, hs] using writes t (by omega) (by omega) w hs

/-- All other groups may be omitted in a replay when its anchor is retained
and the different-value check holds on every group. Set keep identically true
for global soundness, or keep the selected component and cut for completeness. -/
theorem retainedAnchor (initial value : W) (store : Nat → Option W)
    (group : Nat → G) (keep : Nat → Bool) (anchor : Option Nat) (stop : Nat)
    (zero : anchor = none → initial = value)
    (source : ∀ j, anchor = some j → j < stop ∧ store j = some value ∧ keep j = true)
    (eachGroup : ∀ g j, group j = g → j < stop → (∀ i, anchor = some i → i < j) →
      ∀ w, store j = some w → w = value) :
    wordAt initial (fun j => if keep j then store j else none) stop = value := by
  let filtered := fun j => if keep j then store j else none
  change wordAt initial filtered stop = value
  have inherited (j : Nat) (before : j < stop) (after : ∀ i, anchor = some i → i < j)
      (w : W) (hw : filtered j = some w) : w = value := by
    cases hk : keep j with
    | false => simp [filtered, hk] at hw
    | true => exact eachGroup (group j) j rfl before after w (by simpa [filtered, hk] using hw)
  cases ha : anchor with
  | none =>
    apply stableSuffix initial value filtered (start := 0) (Nat.zero_le stop) (zero ha)
    intro j _ hj w hw
    exact inherited j hj (by intro i hi; simp [ha] at hi) w hw
  | some k =>
    obtain ⟨before, atK, kept⟩ := source k ha
    apply stableSuffix initial value filtered (start := k+1) (by omega)
    · simp [wordAt, filtered, kept, atK]
    · intro j hj hstop w hw
      apply inherited j hstop _ w hw
      intro i hi
      have eq : k = i := Option.some.inj (ha.symm.trans hi)
      omega

/-- A component directory needs one label for a chronological interval. -/
theorem intervalLabel (cut : Nat → Bool) (label : Nat → G)
    (edge : ∀ t, cut t = false → cut (t+1) = false → label t = label (t+1))
    {lo hi : Nat} (order : lo ≤ hi)
    (clear : ∀ j, lo ≤ j → j ≤ hi → cut j = false) : label lo = label hi := by
  induction hi with
  | zero =>
    have : lo = 0 := by omega
    simp [this]
  | succ hi ih =>
    by_cases eq : lo = hi+1
    · simp [eq]
    · exact (ih (by omega) (fun j h₁ h₂ => clear j h₁ (by omega))).trans
        (edge hi (clear hi (by omega) (by omega)) (clear (hi+1) order (by omega)))

/-- Unreduced numerator and denominator of the updated exponent. -/
def update (C B D K : Nat) (xy : Nat × Nat) : Nat × Nat :=
  (2*C*D*xy.1, B*(2*K*xy.1+D*xy.2))

def iterate (C B D K : Nat) : Nat → Nat × Nat
  | 0 => (D,K)
  | n+1 => update C B D K (iterate C B D K n)

/-- With c=C/B, d=D/K, the positive fixed point is D(2C-B)/(2BK).
The signed numerator of the reciprocal gap contracts by B/(2C)
after division by the updated numerator. -/
theorem gapStep (C B D K X Y : Int) :
    let gap := fun x y => 2*B*K*x-D*(2*C-B)*y
    gap (2*C*D*X) (B*(2*K*X+D*Y)) = B*D*gap X Y := by
  dsimp
  simp only [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add]
  simp only [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  omega

/-- At c=d=1.28, six iterations are sufficient. -/
theorem exactCrossing :
    (List.range 6).all (fun i =>
      let xy := iterate 32 25 32 25 i
      decide (xy.2 ≤ xy.1)) = true ∧
    (iterate 32 25 32 25 6).1 < (iterate 32 25 32 25 6).2 := by decide

end SlabProduct
