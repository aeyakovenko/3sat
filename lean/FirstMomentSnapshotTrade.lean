import Std

/-! Arithmetic for the first-moment snapshot trade and integrity of a
finite transcript whose queries may depend on earlier answers. -/

namespace FirstMomentSnapshotTrade

/-- For c=C/B, d=D/K and e=X/Y, this gives the unreduced numerator and
denominator of c*d²*e/(d+e). Denominators and parameters are positive
when interpreting these pairs as positive rationals. -/
def trade (C B D K : Nat) (xy : Nat × Nat) : Nat × Nat :=
  (C*D*D*xy.1, B*K*(D*xy.2+K*xy.1))

theorem tradePositive {C B D K X Y : Nat} (hC : 0<C) (hB : 0<B)
    (hD : 0<D) (hK : 0<K) (hX : 0<X) (hY : 0<Y) :
    0 < (trade C B D K (X,Y)).1 ∧ 0 < (trade C B D K (X,Y)).2 := by
  have hDY := Nat.mul_pos hD hY
  have hsum : 0 < D*Y+K*X := by omega
  exact ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hC hD) hD) hX,
    Nat.mul_pos (Nat.mul_pos hB hK) hsum⟩

/-- Up to a fixed positive factor and division by X, this is the signed
gap between 1/[d(cd-1)] and 1/e when cd>1. -/
def gapNumerator (C B D K X Y : Int) : Int :=
  B*K*K*X - D*(C*D-B*K)*Y

/-- The new gap numerator multiplies by BKD while X multiplies by CD².
Consequently the reciprocal gap contracts by BK/(CD)=1/(cd). -/
theorem reciprocalGapStep (C B D K X Y : Int) :
    gapNumerator C B D K (C*D*D*X) (B*K*(D*Y+K*X)) =
      B*K*D*gapNumerator C B D K X Y := by
  simp only [gapNumerator, Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add]
  simp only [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  omega

/-- The seed e_0=d. -/
def iterateTrade (C B D K : Nat) : Nat → Nat × Nat
  | 0 => (D,K)
  | n+1 => trade C B D K (iterateTrade C B D K n)

/-- At c=d=331/250=1.324, the first exponent below one is e_8. -/
theorem firstCrossing :
    (List.range 8).all (fun i =>
      let xy := iterateTrade 331 250 331 250 i
      decide (xy.2 ≤ xy.1)) = true ∧
      (iterateTrade 331 250 331 250 8).1 < (iterateTrade 331 250 331 250 8).2 := by
  decide

/-! In the batched calculation the denominator of the update is
d²+(2−d)e, whereas the individual-query calculation above uses d+e.
Both start from e₀=d. The batched formula below uses 0<d≤2, so its
coefficient 2K−D is nonnegative in the integer representation d=D/K. -/

def batchedTrade (C B D K : Nat) (xy : Nat × Nat) : Nat × Nat :=
  (C*D*D*xy.1, B*(D*D*xy.2 + K*(2*K-D)*xy.1))

def iterateBatched (C B D K : Nat) : Nat → Nat × Nat
  | 0 => (D,K)
  | n+1 => batchedTrade C B D K (iterateBatched C B D K n)

/-- The fixed-point reciprocal gap for batching contracts by B/C=1/c. -/
theorem batchedReciprocalGapStep (C B D K X Y : Int) :
    let gap := fun x y => B*K*(2*K-D)*x - D*D*(C-B)*y
    gap (C*D*D*X) (B*(D*D*Y+K*(2*K-D)*X)) = B*D*D*gap X Y := by
  dsimp
  simp only [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add]
  simp only [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  omega

/-- At c=d=1.353, e₀ through e₁₇ are at least one, and e₁₈ is below one. -/
theorem batchedFirstCrossing :
    (List.range 18).all (fun i =>
      let xy := iterateBatched 1353 1000 1353 1000 i
      decide (xy.2 ≤ xy.1)) = true ∧
      (iterateBatched 1353 1000 1353 1000 18).1 <
        (iterateBatched 1353 1000 1353 1000 18).2 := by
  decide

/-! Logging every read in expensive segments gives the one-level
update 2cde/(d+2e). After this reduces the work exponent below E, the
second phase starts at E with its public-input exponent b fixed at dE. -/

def heavyTrade (C B D K : Nat) (xy : Nat × Nat) : Nat × Nat :=
  (2*C*D*xy.1, B*(D*xy.2+2*K*xy.1))

/-- c=C/B, d=D/K≤2, b=M/V. This pair represents cbe/(b+(2-d)e). -/
def batchWithPublic (C B D K M V : Nat) (xy : Nat × Nat) : Nat × Nat :=
  (C*M*K*xy.1, B*(M*K*xy.2+V*(2*K-D)*xy.1))

def iterateFrom (step : Nat × Nat → Nat × Nat) (seed : Nat × Nat) : Nat → Nat × Nat
  | 0 => seed
  | n+1 => step (iterateFrom step seed n)

/-- Four one-level trades give the stated fraction below E=309/256. The
first twelve batched trades from E use b=dE=3399/2048. The twelfth is the
first exponent below one and both reported fractions are checked exactly. -/
theorem mixedFourThenTwelve :
    let phaseOne := iterateFrom (heavyTrade 11 8 11 8) (11,8)
    let phaseTwo := iterateFrom (batchWithPublic 11 8 11 8 3399 2048) (309,256)
    let first := phaseOne 4
    let last := phaseTwo 12
    11*309=3399 ∧ 8*256=2048 ∧
    0<first.2 ∧ first.1*133568=161051*first.2 ∧ first.1*256<309*first.2 ∧
    (List.range 12).all (fun i => decide ((phaseTwo i).2 ≤ (phaseTwo i).1)) = true ∧
    0<last.2 ∧ last.1*10671453758437376=10667518052474679*last.2 ∧ last.1<last.2 := by
  decide

section AdaptiveCalls

variable {State Request Answer : Type}

/-- A request can include the identity of a row and the address to decode. -/
inductive Wrong (request : State → Request) (decoded : Request → Answer)
    (advance : State → Answer → State) : State → List Answer → Prop where
  | current {s a rest} : a ≠ decoded (request s) →
      Wrong request decoded advance s (a::rest)
  | later {s a rest} : Wrong request decoded advance (advance s a) rest →
      Wrong request decoded advance s (a::rest)

/-- The real answers to n successive requests. Each request can depend
on every answer that the state has consumed so far. -/
def truthful (request : State → Request) (decoded : Request → Answer)
    (advance : State → Answer → State) : Nat → State → List Answer
  | 0, _ => []
  | n+1, s =>
    let a := decoded (request s)
    a::truthful request decoded advance n (advance s a)

/-- No selected request on the guessed transcript has a wrong answer
exactly when the entire guessed transcript equals the genuine one. -/
theorem noWrongIffTruthful (request : State → Request) (decoded : Request → Answer)
    (advance : State → Answer → State) (s : State) (answers : List Answer) :
    (¬Wrong request decoded advance s answers) ↔
      answers = truthful request decoded advance answers.length s := by
  classical
  induction answers generalizing s with
  | nil =>
    constructor
    · intro _
      rfl
    · intro _ bad
      cases bad
  | cons a rest ih =>
    constructor
    · intro valid
      have first : a = decoded (request s) := by
        apply Classical.byContradiction
        intro wrong
        exact valid (.current wrong)
      subst a
      exact congrArg (List.cons _) ((ih _).mp (fun wrong => valid (.later wrong)))
    · intro exactAnswers bad
      obtain ⟨head, tail⟩ := List.cons.inj exactAnswers
      cases bad with
      | current unequal => exact unequal head
      | later badLater =>
        rw [head] at badLater
        exact (ih _).mpr tail badLater

end AdaptiveCalls

end FirstMomentSnapshotTrade
