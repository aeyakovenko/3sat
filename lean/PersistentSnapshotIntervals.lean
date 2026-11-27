import Std

/-! Finite checkpoint selection on the *actual* run through time E.
Full windows are contained in the strictly internal times 1,...,E-1.
A path pays for internal checkpoints only; the initial and final states
are endpoints even when the residual tail is nonempty. -/

namespace PersistentSnapshotIntervals

def InWindow (w i t : Nat) : Prop := i*w < t ∧ t ≤ i*w+w

def windowCount (E w : Nat) : Nat := (E-1)/w

structure Path (E : Nat) where
  segments : Nat
  atTime : Nat → Nat
  first : atTime 0 = 0
  last : atTime segments = E
  advances : ∀ i, i < segments → atTime i < atTime (i+1)

def Short (path : Path E) (gap : Nat) : Prop :=
  ∀ i, i < path.segments → path.atTime (i+1) ≤ path.atTime i + gap

def prefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => prefixSum f n + f n

def prefixMax (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => max (prefixMax f n) (f n)

def sumCost (path : Path E) (size : Nat → Nat) : Nat :=
  prefixSum (fun i => size (path.atTime (i+1))) (path.segments-1)

def maxCost (path : Path E) (cost : Nat → Nat) : Nat :=
  prefixMax (fun i => cost (path.atTime (i+1))) (path.segments-1)

theorem sumBound (n cap : Nat) (f : Nat → Nat) (hf : ∀ i, i < n → f i ≤ cap) :
    prefixSum f n ≤ n*cap := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    have old := ih (fun i hi => hf i (by omega))
    have last := hf n (by omega)
    simp only [prefixSum, Nat.succ_mul]
    omega

theorem maxBound (n cap : Nat) (f : Nat → Nat) (hf : ∀ i, i < n → f i ≤ cap) :
    prefixMax f n ≤ cap := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    exact Nat.max_le.mpr ⟨ih (fun i hi => hf i (by omega)), hf n (by omega)⟩

/-- Pick one time from each full window. After the last pick, the next
vertex is the endpoint E, independently of the residual tail length. -/
def anchors (pick : Nat → Nat) (p E : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => if i < p then pick i else E

theorem adjacent (pick : Nat → Nat) {p w r E : Nat} (hw : 0 < w) (tail : r < w)
    (endpoint : E = 1+p*w+r) (inside : ∀ i, i < p → InWindow w i (pick i))
    (i : Nat) (hi : i < p+1) :
    anchors pick p E i < anchors pick p E (i+1) ∧
    anchors pick p E (i+1) ≤ anchors pick p E i + (2*w-1) := by
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

def chosenPath (pick : Nat → Nat) {p w r E : Nat} (hw : 0 < w) (tail : r < w)
    (endpoint : E = 1+p*w+r) (inside : ∀ i, i < p → InWindow w i (pick i)) : Path E where
  segments := p+1
  atTime := anchors pick p E
  first := rfl
  last := by simp [anchors]
  advances := fun i hi => (adjacent pick hw tail endpoint inside i hi).1

def emptyPath : Path 0 where
  segments := 0
  atTime := fun _ => 0
  first := rfl
  last := rfl
  advances := fun _ hi => by omega

/-- No minimum oracle is needed: any choice simultaneously satisfying the
two per-time thresholds suffices. For E=0 the returned path has no segments;
for 0<E≤w it has a single segment and no internal checkpoints. -/
theorem cheapWindowsGivePath (E w s d : Nat) (hw : 0 < w) (size cost : Nat → Nat)
    (cheap : ∀ i, i < windowCount E w →
      ∃ t, InWindow w i t ∧ size t ≤ s ∧ cost t ≤ d) :
    ∃ path : Path E, path.segments-1 = windowCount E w ∧ Short path (2*w-1) ∧
      sumCost path size ≤ windowCount E w*s ∧ maxCost path cost ≤ d := by
  classical
  by_cases zero : E=0
  · subst E
    refine ⟨emptyPath, ?_, ?_, ?_, ?_⟩
    · simp [emptyPath, windowCount]
    · intro _ hi
      exact (Nat.not_lt_zero _ hi).elim
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  · let p := windowCount E w
    let r := (E-1)%w
    have htail : r < w := Nat.mod_lt _ hw
    have eq : E = 1+p*w+r := by
      have h := Nat.div_add_mod (E-1) w
      rw [Nat.mul_comm] at h
      change E = 1+((E-1)/w)*w+(E-1)%w
      omega
    let pick (i : Nat) := if h : i < p then (cheap i h).choose else 0
    have good (i : Nat) (hi : i < p) :
        InWindow w i (pick i) ∧ size (pick i) ≤ s ∧ cost (pick i) ≤ d := by
      simpa only [pick, dif_pos hi] using (cheap i hi).choose_spec
    have inside := fun i (hi : i < p) => (good i hi).1
    let path := chosenPath pick hw htail eq inside
    refine ⟨path, by simp [path, chosenPath, p], ?_, ?_, ?_⟩
    · intro i hi
      exact (adjacent pick hw htail eq inside i hi).2
    · change prefixSum (fun i => size (anchors pick p E (i+1))) ((p+1)-1) ≤ p*s
      rw [Nat.add_sub_cancel]
      exact sumBound p s _ (fun i hi => by simpa [anchors, hi] using (good i hi).2.1)
    · change prefixMax (fun i => cost (anchors pick p E (i+1))) ((p+1)-1) ≤ d
      rw [Nat.add_sub_cancel]
      exact maxBound p d _ (fun i hi => by simpa [anchors, hi] using (good i hi).2.2)

theorem hardWindow (E w s d L budget : Nat) (hw : 0 < w) (size cost : Nat → Nat)
    (budgetFits : windowCount E w*s + L*d ≤ budget)
    (everyPathCostly : ∀ path : Path E, Short path (2*w-1) →
        budget < sumCost path size + L*maxCost path cost) :
    ∃ i, i < windowCount E w ∧ ∀ t, InWindow w i t → s < size t ∨ d < cost t := by
  classical
  apply Classical.byContradiction
  intro noHard
  have cheap (i : Nat) (hi : i < windowCount E w) :
      ∃ t, InWindow w i t ∧ size t ≤ s ∧ cost t ≤ d := by
    apply Classical.byContradiction
    intro missing
    apply noHard
    refine ⟨i, hi, ?_⟩
    intro t ht
    by_cases small : size t ≤ s
    · right
      by_cases fast : cost t ≤ d
      · exact (missing ⟨t, ht, small, fast⟩).elim
      · omega
    · exact Or.inl (by omega)
  obtain ⟨path, _, short, hs, hd⟩ := cheapWindowsGivePath E w s d hw size cost cheap
  have upper := Nat.add_le_add hs (Nat.mul_le_mul_left L hd)
  have lower := everyPathCostly path short
  omega

/-- Every full window consists of actual strictly pre-halt times. -/
theorem internalWindow {E w i t : Nat} (hw : 0 < w) (hi : i < windowCount E w)
    (ht : InWindow w i t) : 0 < t ∧ t < E := by
  obtain ⟨lower, upper⟩ := ht
  change i < (E-1)/w at hi
  have bound := (Nat.le_div_iff_mul_le hw).mp (show i+1 ≤ (E-1)/w from hi)
  rw [Nat.succ_mul] at bound
  omega

theorem disjointWindows {i j w t : Nat} (hij : i < j) (ht : InWindow w i t) :
    ¬InWindow w j t := by
  have bound := Nat.mul_le_mul_right w (show i+1 ≤ j from hij)
  rw [Nat.succ_mul] at bound
  obtain ⟨_, upper⟩ := ht
  rintro ⟨lower, _⟩
  omega

/-- A good start t carries its own jump j. The list records all starts
except the last, whose possibly mostly unused jump is charged separately. -/
inductive JumpChain (E : Nat) (Good : Nat → Nat → Prop) :
    Nat → List (Nat × Nat) → Nat × Nat → Prop where
  | finish {t j} : Good t j → t ≤ E → E ≤ t+j → JumpChain E Good t [] (t,j)
  | step {t u j middle last} : Good t j → t < u → u < E →
      j ≤ 2*(u-t) → u ≤ t+j → JumpChain E Good u middle last →
      JumpChain E Good t ((t,j)::middle) last

/-- Each nonterminal jump covers at least half its proposed length by
actual forward progress. The bound does not charge the final proposal. -/
theorem totalJumps {E t middle last} {Good : Nat → Nat → Prop}
    (chain : JumpChain E Good t middle last) :
    (middle.map Prod.snd).sum ≤ 2*(E-t) := by
  induction chain with
  | finish => simp
  | step hg htu hu half within tail ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

theorem terminalGood {E t middle last} {Good : Nat → Nat → Prop}
    (chain : JumpChain E Good t middle last) : Good last.1 last.2 := by
  induction chain with
  | finish hg _ _ => exact hg
  | step _ _ _ _ _ _ ih => exact ih

/-- A ratio A·charge ≤ B·jump on each description transfers to the sum
of all nonterminal descriptions, with no roundoff per selected time. -/
theorem amortizedCharge {E t middle last} {Good : Nat → Nat → Prop}
    (A B : Nat) (charge : Nat × Nat → Nat)
    (unitBound : ∀ t j, Good t j → A*charge (t,j) ≤ B*j)
    (chain : JumpChain E Good t middle last) :
    A*(middle.map charge).sum ≤ B*(2*(E-t)) := by
  have pointwise : A*(middle.map charge).sum ≤ B*(middle.map Prod.snd).sum := by
    induction chain with
    | finish => simp
    | step hg _ _ _ _ _ ih =>
      simpa only [List.map_cons, List.sum_cons, Nat.mul_add] using
        Nat.add_le_add (unitBound _ _ hg) ih
  exact Nat.le_trans pointwise (Nat.mul_le_mul_left B (totalJumps chain))

/-- Every *sliding* block (b,b+w] entirely before E must have a good
start with some admissible jump. Each step uses the last w times within
the preceding start's jump. A different description may witness each jump. -/
theorem greedyChain (E w : Nat) (Good : Nat → Nat → Prop) (hw : 0 < w)
    (dense : ∀ b, b+w < E → ∃ u k, b < u ∧ u ≤ b+w ∧ 2*w ≤ k ∧ Good u k)
    (t j : Nat) (ht : t ≤ E) (hj : 2*w ≤ j) (good : Good t j) :
    ∃ middle last, JumpChain E Good t middle last := by
  by_cases final : E ≤ t+j
  · exact ⟨[], (t,j), .finish good ht final⟩
  · obtain ⟨u, k, lo, hi, hk, gu⟩ := dense (t+j-w) (by omega)
    have htu : t < u := by omega
    have hu : u < E := by omega
    obtain ⟨middle, last, tail⟩ := greedyChain E w Good hw dense u k (by omega) hk gu
    exact ⟨(t,j)::middle, last, .step good htu hu (by omega) (by omega) tail⟩
termination_by E-t
decreasing_by omega

/-- If every chain violates its nonterminal jump budget, some entire
sliding block has no good description at any permitted jump size. -/
theorem persistentJumpFailure (E w : Nat) (Good : Nat → Nat → Prop) (hw : 0 < w)
    (start : ∃ j, 2*w ≤ j ∧ Good 0 j)
    (obstruction : ∀ middle last, JumpChain E Good 0 middle last →
      2*E < (middle.map Prod.snd).sum) :
    ∃ b, b+w < E ∧ ∀ u, b < u → u ≤ b+w → ∀ j, 2*w ≤ j → ¬Good u j := by
  classical
  apply Classical.byContradiction
  intro noBlock
  have dense (b : Nat) (before : b+w < E) :
      ∃ u k, b < u ∧ u ≤ b+w ∧ 2*w ≤ k ∧ Good u k := by
    apply Classical.byContradiction
    intro empty
    exact noBlock ⟨b, before, fun u lo hi k hk gu => empty ⟨u,k,lo,hi,hk,gu⟩⟩
  obtain ⟨j,hj,good⟩ := start
  obtain ⟨middle,last,chain⟩ := greedyChain E w Good hw dense 0 j (Nat.zero_le _) hj good
  have upper := totalJumps chain
  have lower := obstruction middle last chain
  omega

end PersistentSnapshotIntervals
