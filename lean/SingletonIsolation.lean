import Std

namespace SingletonIsolation

private def squares (xs : List Nat) : Nat := (xs.map fun a => a*a).sum

private theorem twoProducts (a b : Nat) : a*b + b*a ≤ a*a + b*b := by
  rcases Nat.le_total a b with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.add_mul, Nat.mul_add]
    omega

private theorem crossTerms (a : Nat) (xs : List Nat) :
    a*xs.sum + xs.sum*a ≤ xs.length*(a*a) + squares xs := by
  induction xs with
  | nil => simp [squares]
  | cons b xs ih =>
    have pair := twoProducts a b
    simp only [squares, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul,
      Nat.mul_add, Nat.add_mul] at *
    omega

/-- Integer Cauchy-Schwarz for a finite list of occupancy counts. -/
theorem occupancyMoment (xs : List Nat) : xs.sum*xs.sum ≤ xs.length * squares xs := by
  induction xs with
  | nil => simp [squares]
  | cons a xs ih =>
    have cross := crossTerms a xs
    simp only [squares, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul,
      Nat.mul_add, Nat.add_mul] at *
    omega

/-- There are Q equally likely seeds. The list records competitor counts
    on seeds with at least one competitor. A seeds contain the target and
    P seeds isolate it. There are n+1 competitors. The last two hypotheses
    are the first and second occupancy moment identities from pairwise
    independence with common marginal A/Q. The conclusion clears the
    denominator in the one-sided second-moment bound for the zero event. -/
theorem pairwiseMomentBound (occupied : List Nat) (Q A P n : Nat)
    (target : P ≤ A) (disjoint : P + occupied.length ≤ Q)
    (first : occupied.sum = (n+1)*A)
    (second : Q * (occupied.map (fun x => x*x)).sum = ((n+1)*A)*(Q+n*A)) :
    P*(Q+n*A) + Q*A ≤ Q*Q := by
  by_cases zero : A = 0
  · have pzero : P = 0 := by omega
    simp [zero, pzero]
  have pos : 0 < (n+1)*A := Nat.mul_pos (by omega) (by omega)
  have support : occupied.length ≤ Q-P := by omega
  have cs := occupancyMoment occupied
  rw [first] at cs
  have scaled : ((n+1)*A)*(Q*((n+1)*A)) ≤ ((n+1)*A)*((Q-P)*(Q+n*A)) := calc
    _ = Q*(((n+1)*A)*((n+1)*A)) := by ac_rfl
    _ ≤ Q*(occupied.length*squares occupied) := Nat.mul_le_mul_left Q cs
    _ ≤ Q*((Q-P)*squares occupied) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ support)
    _ = (Q-P)*(Q*(occupied.map (fun x => x*x)).sum) := by unfold squares; ac_rfl
    _ = _ := by rw [second]; ac_rfl
  have bound := Nat.le_of_mul_le_mul_left scaled pos
  have pQ : P ≤ Q := by omega
  have split := congrArg (fun z => z*(Q+n*A)) (Nat.sub_add_cancel pQ)
  simp only [Nat.add_mul, Nat.mul_add, Nat.succ_mul] at bound split ⊢
  omega

/-- The optimized square-root bound in integer form. It states
    (n+1)P² ≤ (Q-P)² for n+1 competitors. -/
theorem squareRootBound (Q A P n : Nat) (target : P ≤ A) (pQ : P ≤ Q)
    (moment : P*(Q+n*A) + Q*A ≤ Q*Q) :
    (n+1)*(P*P) ≤ (Q-P)*(Q-P) := by
  have bound : P*(Q+n*P) + Q*P ≤ Q*Q := Nat.le_trans
    (Nat.add_le_add (Nat.mul_le_mul_left P (Nat.add_le_add_left (Nat.mul_le_mul_left n target) Q))
      (Nat.mul_le_mul_left Q target)) moment
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le pQ
  simp only [Nat.add_sub_cancel_left, Nat.mul_add, Nat.add_mul, Nat.succ_mul,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at bound ⊢
  omega

/-- A finite centered second-moment certificate for the sharper bound. Among
    A target-containing seeds, P singleton seeds have centered deficit w
    each. The listed positive surpluses on the remaining seeds compensate
    those deficits by the conditional first-moment identity. The variance
    budget covers their squares and the singleton deficits. With N rivals,
    choose w=N*A and budget=Q*(Q-A), using the global pairwise variance.
    This proves P*[N*A²+Q*(Q-A)] ≤ A*Q*(Q-A) from that certificate. -/
theorem centeredIsolation (surplus : List Nat) (A P w budget : Nat) (positive : 0 < w)
    (disjoint : P + surplus.length ≤ A) (balance : P*w ≤ surplus.sum)
    (variance : P*(w*w) + (surplus.map (fun x => x*x)).sum ≤ w*budget) :
    P*(A*w+budget) ≤ A*budget := by
  obtain ⟨d, ha⟩ := Nat.exists_eq_add_of_le (show P ≤ A by omega)
  have support : surplus.length ≤ d := by omega
  have cs := occupancyMoment surplus
  have lo : (P*w)*(P*w) ≤ d*squares surplus := Nat.le_trans
    (Nat.mul_le_mul balance balance) (Nat.le_trans cs (Nat.mul_le_mul_right _ support))
  have combined : w*(P*(A*w)) ≤ w*(d*budget) := calc
    _ = d*(P*(w*w)) + (P*w)*(P*w) := by
      rw [ha]; simp only [Nat.add_mul, Nat.mul_add]
      ac_rfl
    _ ≤ d*(P*(w*w)) + d*squares surplus := Nat.add_le_add_left lo _
    _ = d*(P*(w*w)+squares surplus) := (Nat.mul_add ..).symm
    _ ≤ d*(w*budget) := Nat.mul_le_mul_left _ variance
    _ = _ := by ac_rfl
  have canceled := Nat.le_of_mul_le_mul_left combined positive
  calc
    _ = P*(A*w) + P*budget := Nat.mul_add ..
    _ ≤ d*budget + P*budget := Nat.add_le_add_right canceled _
    _ = A*budget := by rw [ha, Nat.add_mul, Nat.add_comm]

/-- Bit zero denotes the distinguished item. Other bits index the pairs
    (a,b), with a<r and b<r/2. Enumerate the entire r³-point seed space. -/
private def exampleBuckets (r : Nat) : List Nat :=
  (List.range (r^3)).map fun seed =>
    let x := seed % r
    let y := (seed / r) % r
    let z := seed / (r*r)
    (List.range (r*(r/2))).foldl (fun mask j =>
      let a := j / (r/2)
      let b := j % (r/2)
      if (z + a*x + b*y) % r == 0 then mask ||| (1 <<< (j+1)) else mask)
      (if x == 0 then 1 else 0)

private def checkExample (r expected : Nat) : Bool := Id.run do
  let buckets := exampleBuckets r
  let items := List.range (1 + r*(r/2))
  let hits := fun mask => buckets.countP (fun row => (row &&& mask) == mask)
  if !(items.all fun i => hits (1 <<< i) == r*r) then return false
  if !(items.all fun i => (List.range i).all fun j =>
    hits ((1 <<< i) ||| (1 <<< j)) == r) then return false
  let singletons := buckets.filter fun row => row != 0 && (row &&& (row-1)) == 0
  return singletons.length == expected && singletons.all (· == 1) &&
    expected == (r-1)*(r-r/2+1)

theorem example5 : checkExample 5 16 = true := by native_decide
theorem example7 : checkExample 7 30 = true := by native_decide
theorem example11 : checkExample 11 70 = true := by native_decide

end SingletonIsolation
