import Std

namespace MovingThreshold

/-- The search tests precisely 0,…,N. The sentinel N+1 denotes no hit. -/
structure FirstHit (P : Nat → Prop) (N i : Nat) : Prop where
  bound : i ≤ N + 1
  hit : i ≤ N → P i
  before : ∀ j, j < i → ¬ P j

theorem firstHit_exists (P : Nat → Prop) (N : Nat) :
    ∃ i, FirstHit P N i := by
  classical
  induction N with
  | zero =>
    by_cases h : P 0
    · exact ⟨0, ⟨by omega, fun _ => h, by intro j hj; omega⟩⟩
    · refine ⟨1, ⟨by omega, by omega, ?_⟩⟩
      intro j hj
      have : j = 0 := by omega
      simpa [this] using h
  | succ N ih =>
    obtain ⟨i, hi⟩ := ih
    by_cases old : i ≤ N
    · exact ⟨i, ⟨by omega, fun _ => hi.hit old, hi.before⟩⟩
    · have bound := hi.bound
      have last : i = N + 1 := by omega
      by_cases next : P (N + 1)
      · exact ⟨i, ⟨by omega, fun _ => last ▸ next, hi.before⟩⟩
      · refine ⟨N + 2, ⟨by omega, by omega, ?_⟩⟩
        intro j hj
        by_cases earlier : j < i
        · exact hi.before j earlier
        · have eq : j = N + 1 := by omega
          simpa [eq] using next

private theorem shiftFirst {P Q : Nat → Prop} {N i j : Nat}
    (hp : FirstHit P N i) (hq : FirstHit Q N j)
    (shift : ∀ x, x < N → P x → Q (x + 1)) :
    j ≤ i + 1 := by
  by_cases late : i + 1 < j
  · have bound := hq.bound
    have inside : i < N := by omega
    exact False.elim (hq.before (i+1) late (shift i inside (hp.hit (by omega))))
  · omega

/-- At a common integer scale, an error no greater than one threshold step
suffices. The estimates may oscillate. No empirical monotonicity is needed. -/
theorem crossingWithinOne (F E g : Nat → Int) (error : Int) (N i j : Nat)
    (rises : ∀ x, x < N → F x ≤ F (x+1))
    (falls : ∀ x, x < N → g (x+1) + error ≤ g x)
    (est : ∀ x, x ≤ N → F x - error ≤ E x ∧ E x ≤ F x + error)
    (truth : FirstHit (fun x => g x ≤ F x) N i)
    (sample : FirstHit (fun x => g x ≤ E x) N j) :
    i ≤ j+1 ∧ j ≤ i+1 := by
  constructor
  · apply shiftFirst sample truth
    intro x hx accepted
    have acc : g x ≤ E x := accepted
    have hinc := rises x hx
    have hdec := falls x hx
    have hupper := (est x (by omega)).2
    change g (x+1) ≤ F (x+1)
    omega
  · apply shiftFirst truth sample
    intro x hx accepted
    have acc : g x ≤ F x := accepted
    have hinc := rises x hx
    have hdec := falls x hx
    have hlower := (est (x+1) (by omega)).1
    change g (x+1) ≤ E (x+1)
    omega

/-- The sampling proof only needs correct decisions outside a varying
error band. Both adjacent error radii are paid by the same cutoff drop. -/
theorem movingDecisionWithinOne (F g radius : Nat → Int) (accept : Nat → Prop)
    (N i j : Nat) (rises : ∀ x, x < N → F x ≤ F (x+1))
    (dropHere : ∀ x, x < N → g (x+1) ≤ g x - radius x)
    (dropNext : ∀ x, x < N → g (x+1) + radius (x+1) ≤ g x)
    (rejects : ∀ x, x ≤ N → F x ≤ g x - radius x → ¬ accept x)
    (passes : ∀ x, x ≤ N → g x + radius x ≤ F x → accept x)
    (truth : FirstHit (fun x => g x ≤ F x) N i)
    (sample : FirstHit accept N j) : i ≤ j+1 ∧ j ≤ i+1 := by
  constructor
  · apply shiftFirst sample truth
    intro x hx yes
    have outside : ¬ F x ≤ g x - radius x :=
      fun low => rejects x (by omega) low yes
    have inc := rises x hx
    have drop := dropHere x hx
    change g (x+1) ≤ F (x+1)
    omega
  · apply shiftFirst truth sample
    intro x hx hit
    have actual : g x ≤ F x := hit
    have inc := rises x hx
    have drop := dropNext x hx
    exact passes (x+1) (by omega) (by omega)

/-- With two error radii of fall per step, the crossing indices of two
different empirical arrays are themselves adjacent, even if the arrays
oscillate. One error radius only gives adjacency to the true index. -/
theorem empiricalCrossingsWithinOne (F A B g : Nat → Int) (error : Int)
    (N i j : Nat) (rises : ∀ x, x < N → F x ≤ F (x+1))
    (falls : ∀ x, x < N → g (x+1) + 2*error ≤ g x)
    (estA : ∀ x, x ≤ N → F x - error ≤ A x ∧ A x ≤ F x + error)
    (estB : ∀ x, x ≤ N → F x - error ≤ B x ∧ B x ≤ F x + error)
    (ha : FirstHit (fun x => g x ≤ A x) N i)
    (hb : FirstHit (fun x => g x ≤ B x) N j) :
    i ≤ j+1 ∧ j ≤ i+1 := by
  have shift (X Y : Nat → Int)
      (upper : ∀ x, x ≤ N → X x ≤ F x + error)
      (lower : ∀ x, x ≤ N → F x - error ≤ Y x) :
      ∀ x, x < N → g x ≤ X x → g (x+1) ≤ Y (x+1) := by
    intro x hx accepted
    have hinc := rises x hx
    have hdec := falls x hx
    have hu := upper x (by omega)
    have hl := lower (x+1) (by omega)
    omega
  exact ⟨shiftFirst hb ha (shift B A (fun x h => (estB x h).2) (fun x h => (estA x h).1)),
    shiftFirst ha hb (shift A B (fun x h => (estA x h).2) (fun x h => (estB x h).1))⟩

/-- In common integral units, u represents p/128. The increments arriving
in [4u,8u) carry more than 3u mass when no increment exceeds u.
The interval sum telescopes to F r - F l. -/
theorem bandEntryMass (F : Nat → Nat) (u N : Nat)
    (start : F 0 < 4*u) (finish : 8*u ≤ F N)
    (mono : ∀ x y, x ≤ y → y ≤ N → F x ≤ F y)
    (small : ∀ j, j < N → F (j+1) ≤ F j + u) :
    ∃ l r, l < r ∧ r < N ∧ F l < 4*u ∧
      (∀ j, l < j → j ≤ r → 4*u ≤ F j ∧ F j < 8*u) ∧
      3*u < F r - F l := by
  obtain ⟨i, hi⟩ := firstHit_exists (fun j => 4*u ≤ F j) N
  obtain ⟨k, hk⟩ := firstHit_exists (fun j => 8*u ≤ F j) N
  have iN : i ≤ N := by
    by_cases h : N < i
    · exact False.elim ((hi.before N h) (by omega))
    · omega
  have kN : k ≤ N := by
    by_cases h : N < k
    · exact False.elim ((hk.before N h) finish)
    · omega
  have fi := hi.hit iN
  have fk := hk.hit kN
  change 4*u ≤ F i at fi
  change 8*u ≤ F k at fk
  cases i with
  | zero => omega
  | succ l =>
    cases k with
    | zero => omega
    | succ r =>
      have lo : F l < 4*u := Nat.lt_of_not_ge (hi.before l (by omega))
      have step := small r (by omega)
      have fr : 7*u ≤ F r := by omega
      have lr : l < r := by
        by_cases h : r ≤ l
        · have m := mono r l h (by omega)
          omega
        · omega
      refine ⟨l,r,lr,by omega,lo,?_,by omega⟩
      intro j hj hr
      have low := mono (l+1) j (by omega) (by omega)
      exact ⟨by omega, Nat.lt_of_not_ge (hk.before j (by omega))⟩

end MovingThreshold
