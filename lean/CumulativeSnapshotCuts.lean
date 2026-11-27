import Std

/-! Choose one least-occupied time from each full, strictly internal window.
The initial and terminal configurations are free endpoints. Occupancy is
any natural-valued function on instruction times. -/

namespace CumulativeSnapshotCuts

/-- The sum on the half-open interval [start, start + count). -/
def sumFrom (f : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sumFrom f start n + f (start+n)

theorem splitSum (f : Nat → Nat) (a n k : Nat) :
    sumFrom f a (n+k) = sumFrom f a n + sumFrom f (a+n) k := by
  induction k with
  | zero => simp [sumFrom]
  | succ k ih =>
    rw [Nat.add_succ, sumFrom, ih, sumFrom]
    simp [Nat.add_assoc]

theorem initialSumBound (f : Nat → Nat) {n m : Nat} (le : n ≤ m) :
    sumFrom f 0 n ≤ sumFrom f 0 m := by
  have split := splitSum f 0 n (m-n)
  have eq : n+(m-n)=m := by omega
  rw [eq] at split
  omega

/-- The offset of a minimum over the offsets 0 through n, inclusive. -/
def minOffset (f : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => let old := minOffset f a n
           if f (a+(n+1)) < f (a+old) then n+1 else old

theorem minOffsetSpec (f : Nat → Nat) (a n : Nat) :
    minOffset f a n ≤ n ∧ ∀ j, j ≤ n → f (a+minOffset f a n) ≤ f (a+j) := by
  induction n with
  | zero =>
    simp [minOffset]
  | succ n ih =>
    obtain ⟨within, least⟩ := ih
    simp only [minOffset]
    split <;> rename_i cmp
    · refine ⟨Nat.le_refl _, fun j hj => ?_⟩
      by_cases small : j ≤ n
      · exact Nat.le_trans (Nat.le_of_lt cmp) (least j small)
      · have eq : j=n+1 := by omega
        rw [eq]
        exact Nat.le_refl _
    · refine ⟨by omega, fun j hj => ?_⟩
      by_cases small : j ≤ n
      · exact least j small
      · have eq : j=n+1 := by omega
        rw [eq]
        omega

theorem scaledMinimum (f : Nat → Nat) (a n v : Nat)
    (least : ∀ j, j < n → v ≤ f (a+j)) : n*v ≤ sumFrom f a n := by
  induction n with
  | zero => simp [sumFrom]
  | succ n ih =>
    have prev := ih (fun j hj => least j (by omega))
    have this := least n (by omega)
    simp only [sumFrom, Nat.succ_mul]
    omega

/-- The full window at index i starts at i*w+1 and has exactly w times. -/
def inWindow (w i t : Nat) : Prop := i*w < t ∧ t ≤ i*w+w

def pick (f : Nat → Nat) (w i : Nat) : Nat :=
  (1+i*w)+minOffset f (1+i*w) (w-1)

theorem pickSpec (f : Nat → Nat) {w : Nat} (hw : 0 < w) (i : Nat) :
    inWindow w i (pick f w i) ∧ ∀ t, inWindow w i t → f (pick f w i) ≤ f t := by
  obtain ⟨within, least⟩ := minOffsetSpec f (1+i*w) (w-1)
  refine ⟨?_, ?_⟩
  · unfold inWindow pick
    constructor <;> omega
  · rintro t ⟨ht, bound⟩
    have low := least (t-(1+i*w)) (by omega)
    have eq : 1+i*w+(t-(1+i*w))=t := by omega
    rw [eq] at low
    exact low

theorem selectedMass (f : Nat → Nat) {w : Nat} (hw : 0 < w) (p : Nat) :
    w*sumFrom (fun i => f (pick f w i)) 0 p ≤ sumFrom f 1 (p*w) := by
  induction p with
  | zero => simp [sumFrom]
  | succ p ih =>
    have one := scaledMinimum f (1+p*w) w (f (pick f w p)) (by
      intro j hj
      exact (pickSpec f hw p).2 _ ⟨by omega, by omega⟩)
    rw [Nat.succ_mul, splitSum f 1 (p*w) w, sumFrom, Nat.mul_add, Nat.zero_add]
    exact Nat.add_le_add ih one

structure Chain (E : Nat) where
  segments : Nat
  time : Nat → Nat
  first : time 0 = 0
  last : time segments = E
  advances : ∀ i, i < segments → time i < time (i+1)

def maxGapAtMost (path : Chain E) (cap : Nat) : Prop :=
  ∀ i, i < path.segments → path.time (i+1) ≤ path.time i + cap

def anchors (choice : Nat → Nat) (p E : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => if i < p then choice i else E

private theorem adjacent (choice : Nat → Nat) {p w r E : Nat} (hw : 0 < w) (tail : r < w)
    (endpoint : E = 1+p*w+r) (inside : ∀ i, i < p → inWindow w i (choice i))
    (i : Nat) (hi : i < p+1) :
    anchors choice p E i < anchors choice p E (i+1) ∧
    anchors choice p E (i+1) ≤ anchors choice p E i + (2*w-1) := by
  cases i with
  | zero =>
    by_cases starts : 0 < p
    · obtain ⟨lo,up⟩ := inside 0 starts
      simp only [Nat.zero_mul, Nat.zero_add] at lo up
      simp only [anchors, if_pos starts, Nat.zero_add]
      omega
    · have nop : p=0 := by omega
      subst p
      simp only [Nat.zero_mul, Nat.add_zero] at endpoint
      simp only [anchors, Nat.lt_irrefl, if_false, Nat.zero_add]
      omega
  | succ j =>
    have prior : j < p := by omega
    obtain ⟨lo, up⟩ := inside j prior
    simp only [anchors, if_pos prior]
    by_cases next : j+1 < p
    · obtain ⟨nextLo,nextUp⟩ := inside (j+1) next
      rw [Nat.succ_mul] at nextLo nextUp
      rw [if_pos next]
      omega
    · have eq : p=j+1 := by omega
      rw [eq, Nat.succ_mul] at endpoint
      rw [if_neg next]
      omega

private theorem sumAgree (f g : Nat → Nat) (n : Nat) (eq : ∀ i, i < n → f i = g i) :
    sumFrom f 0 n = sumFrom g 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have prior := ih (fun i hi => eq i (by omega))
    simp only [sumFrom, Nat.zero_add, prior, eq n (by omega)]

/-- For the actual pre-halt mass on 0,...,E-1, the total mass of the
internal checkpoints is at most 1/w of that amount. Each chosen checkpoint
minimizes occupancy on its full internal window. An empty run has no
segments and a nonempty run with no full internal windows has one segment. -/
theorem cumulativeCuts (E w : Nat) (hw : 0 < w) (occ : Nat → Nat) :
    ∃ path : Chain E,
      path.segments = (if E=0 then 0 else (E-1)/w+1) ∧
      maxGapAtMost path (2*w-1) ∧
      (∀ i, i < path.segments-1 → inWindow w i (path.time (i+1)) ∧
        ∀ t, inWindow w i t → occ (path.time (i+1)) ≤ occ t) ∧
      w*sumFrom (fun i => 1+occ (path.time (i+1))) 0 (path.segments-1)
        ≤ sumFrom (fun t => 1+occ t) 0 E := by
  by_cases zero : E=0
  · subst E
    let empty : Chain 0 := ⟨0, fun _ => 0, rfl, rfl, fun _ hi => by omega⟩
    refine ⟨empty, by simp [empty], ?_, ?_, by simp [empty, sumFrom]⟩
    · intro i hi
      exact (Nat.not_lt_zero i hi).elim
    · intro i hi
      exact (Nat.not_lt_zero i hi).elim
  · let f := fun t => 1+occ t
    let p := (E-1)/w
    let r := (E-1)%w
    have tail : r < w := Nat.mod_lt _ hw
    have endpoint : E=1+p*w+r := by
      have h := Nat.div_add_mod (E-1) w
      rw [Nat.mul_comm] at h
      change E=1+((E-1)/w)*w+(E-1)%w
      omega
    let choice := pick f w
    have inside := fun i (_ : i < p) => (pickSpec f hw i).1
    let path : Chain E := ⟨p+1, anchors choice p E, rfl, by simp [anchors],
      fun i hi => (adjacent choice hw tail endpoint inside i hi).1⟩
    refine ⟨path, by simp [path, p, zero], ?_, ?_, ?_⟩
    · intro i hi
      exact (adjacent choice hw tail endpoint inside i hi).2
    · intro i hi
      change i < (p+1)-1 at hi
      have before : i<p := by omega
      change inWindow w i (anchors choice p E (i+1)) ∧ _
      simp only [path, anchors, if_pos before]
      refine ⟨(pickSpec f hw i).1, fun t ht => ?_⟩
      have good := (pickSpec f hw i).2 t ht
      change 1+occ (choice i) ≤ 1+occ t at good
      omega
    · change w*sumFrom (fun i => f (anchors choice p E (i+1))) 0 ((p+1)-1) ≤ sumFrom f 0 E
      rw [Nat.add_sub_cancel]
      rw [sumAgree _ (fun i => f (choice i)) p (fun i hi => by simp [anchors, hi])]
      have internal := selectedMass f hw p
      have upto := initialSumBound f (show 1+p*w ≤ E by omega)
      rw [splitSum f 0 1 (p*w)] at upto
      simp only [Nat.zero_add] at upto
      change w*sumFrom (fun i => f (pick f w i)) 0 p ≤ sumFrom f 0 E
      omega

/-- With c=C/D and e=X/Y, these are the numerator and denominator of
c²e/(c+e), before cancellation. Positive inputs keep both positive. -/
def trade (C D : Nat) (xy : Nat × Nat) : Nat × Nat :=
  (C*C*xy.1, D*(C*xy.2+D*xy.1))

def iterateTrade (C D : Nat) : Nat → Nat × Nat
  | 0 => (C,D)
  | n+1 => trade C D (iterateTrade C D n)

/-- The numerator of the signed gap between 1/[c(c-1)] and 1/e,
up to a fixed positive factor when c>1. Its denominator contains X. -/
def gapNumerator (C D X Y : Int) : Int := D*D*X - C*(C-D)*Y

/-- During a trade the signed numerator is multiplied by CD, while
X is multiplied by C². Thus the normalized reciprocal gap contracts by D/C. -/
theorem reciprocalGapStep (C D X Y : Int) :
    gapNumerator C D (C*C*X) (D*(C*Y+D*X)) = C*D*gapNumerator C D X Y := by
  simp only [gapNumerator, Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add]
  simp only [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  omega

/-- For c=1617/1000 the first strict crossing is at step eleven. -/
theorem elevenTrades :
    (List.range 11).all (fun n =>
      let xy := iterateTrade 1617 1000 n
      decide (xy.2 ≤ xy.1)) = true ∧
    (iterateTrade 1617 1000 11).1 < (iterateTrade 1617 1000 11).2 := by
  decide

end CumulativeSnapshotCuts
