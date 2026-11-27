import Std

namespace OrdinalBlindQueries

/-- A separate tree is supplied for each ordinary challenge value. The
tree can branch on array symbols but receives no hidden ordinal. -/
inductive Reader where
  | halt (answer : Bool)
  | probe (index : Nat) (next : Nat → Reader)

def decision (arr : Nat → Nat) : Reader → Bool
  | .halt b => b
  | .probe i next => decision arr (next (arr i))

def positions (arr : Nat → Nat) : Reader → List Nat
  | .halt _ => []
  | .probe i next => i :: positions arr (next (arr i))

def firstHidden (hidden : Nat → Bool) (arr : Nat → Nat) : Reader → Option Nat
  | .halt _ => none
  | .probe i next =>
      if hidden i then some i else firstHidden hidden arr (next (arr i))

def OutsideAgreement (hidden : Nat → Bool) (a b : Nat → Nat) : Prop :=
  ∀ i, hidden i = false → a i = b i

/-- A successful path avoiding the erased set is valid on every completion. -/
theorem preserveOutside (hidden : Nat → Bool) (a b : Nat → Nat)
    (equal : OutsideAgreement hidden a b) (reader : Reader)
    (avoids : ∀ i ∈ positions a reader, hidden i = false) :
    decision a reader = decision b reader ∧ positions a reader = positions b reader := by
  induction reader with
  | halt answer => exact ⟨rfl, rfl⟩
  | probe i next ih =>
    have hi : hidden i = false := avoids i (by simp [positions])
    have address := equal i hi
    have tail := ih (a i) (fun j hj => avoids j (by simp [positions, hj]))
    simp only [decision, positions, ← address]
    exact ⟨tail.1, congrArg (List.cons i) tail.2⟩

/-- The first attempted access to an erased address is known before its data arrive. -/
theorem preserveFirst (hidden : Nat → Bool) (a b : Nat → Nat)
    (equal : OutsideAgreement hidden a b) (reader : Reader) :
    firstHidden hidden a reader = firstHidden hidden b reader := by
  induction reader with
  | halt answer => rfl
  | probe i next ih =>
    cases h : hidden i with
    | true => simp [firstHidden, h]
    | false =>
      have address := equal i h
      simpa [firstHidden, h, ← address] using ih (a i)

/-- If the only erased address seen on a path is its own index, it is first. -/
theorem firstIsSelf (hidden : Nat → Bool) (a : Nat → Nat) (self : Nat)
    (member : hidden self = true) (reader : Reader)
    (hit : self ∈ positions a reader)
    (isolated : ∀ j ∈ positions a reader, hidden j = true → j = self) :
    firstHidden hidden a reader = some self := by
  induction reader with
  | halt answer => simp [positions] at hit
  | probe i next ih =>
    cases h : hidden i with
    | true =>
      have eqSelf := isolated i (by simp [positions]) h
      simp [firstHidden, h, eqSelf, member]
    | false =>
      have neq : self ≠ i := by
        intro e
        subst i
        simp [h] at member
      have tailHit : self ∈ positions a (next (a i)) := by
        simpa [positions, neq] using hit
      have tailIsolated := fun j (hj : j ∈ positions a (next (a i))) =>
        isolated j (by simp [positions, hj])
      simpa [firstHidden, h] using ih (a i) tailHit tailIsolated

/-- On a good batch outside the proximity balls, sampled soundness forces
an actual negative input whose rejection was not timely. -/
theorem coverGood {Batch : Type} (timely far good formulaSat : Batch → Prop)
    (outsideTimely : ∀ r, far r → ¬ timely r)
    (sampledSound : ∀ r, good r → far r → ¬ formulaSat r)
    (r : Batch) (ok : good r) :
    ¬ far r ∨ (¬ formulaSat r ∧ ¬ timely r) := by
  by_cases h : far r
  · exact Or.inr ⟨sampledSound r ok h, outsideTimely r h⟩
  · exact Or.inl h

/-- Perfect completeness describes the genuine proof. Passing all tests
via a short description would separately make the explicit formula SAT. -/
theorem hardGenuine {Batch Proof Code : Type}
    (timely formulaSat : Batch → Prop)
    (perfect : Batch → Proof → Prop) (rep : Batch → Code → Proof)
    (actual : ∀ r, timely r → ¬ formulaSat r)
    (complete : ∀ r, timely r → ∃ pi, perfect r pi)
    (compiled : ∀ r z, perfect r (rep r z) → formulaSat r)
    (r : Batch) (h : timely r) :
    (∃ pi, perfect r pi) ∧ ∀ z, ¬ perfect r (rep r z) := by
  exact ⟨complete r h, fun z hz => actual r h (compiled r z hz)⟩

end OrdinalBlindQueries
