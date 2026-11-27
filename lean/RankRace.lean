import Std

namespace RankRace

/-- Expanding a shared min/max circuit as a tree keeps the same environment
at every occurrence of the same worker. -/
inductive Gate where
  | input (worker : Nat)
  | earliest (a b : Gate)
  | latest (a b : Gate)

def value (atWorker : Nat → Nat) : Gate → Nat
  | .input i => atWorker i
  | .earliest a b => min (value atWorker a) (value atWorker b)
  | .latest a b => max (value atWorker a) (value atWorker b)

def above (worker : Nat → Prop) : Gate → Prop
  | .input i => worker i
  | .earliest a b => above worker a ∧ above worker b
  | .latest a b => above worker a ∨ above worker b

def below (worker : Nat → Prop) : Gate → Prop
  | .input i => worker i
  | .earliest a b => below worker a ∨ below worker b
  | .latest a b => below worker a ∧ below worker b

theorem lowerThreshold (atWorker : Nat → Nat) (cut : Nat) (g : Gate) :
    cut ≤ value atWorker g ↔ above (fun i => cut ≤ atWorker i) g := by
  induction g with
  | input => rfl
  | earliest a b ia ib =>
    simp only [value, above, ← ia, ← ib]
    omega
  | latest a b ia ib =>
    simp only [value, above, ← ia, ← ib]
    omega

theorem upperThreshold (atWorker : Nat → Nat) (cut : Nat) (g : Gate) :
    value atWorker g ≤ cut ↔ below (fun i => atWorker i ≤ cut) g := by
  induction g with
  | input => rfl
  | earliest a b ia ib =>
    simp only [value, below, ← ia, ← ib]
    omega
  | latest a b ia ib =>
    simp only [value, below, ← ia, ← ib]
    omega

theorem valueMono (first last : Nat → Nat) (ordered : ∀ i, first i ≤ last i) (g : Gate) :
    value first g ≤ value last g := by
  induction g with
  | input i => exact ordered i
  | earliest a b ia ib => simp only [value]; omega
  | latest a b ia ib => simp only [value]; omega

/-- The interval event computed by the two threshold circuits is equivalent
to inclusion for *every* choice in the product of the local intervals. -/
theorem forcedWindow (first last : Nat → Nat) (ordered : ∀ i, first i ≤ last i)
    (lo hi : Nat) (g : Gate) :
    (above (fun i => lo ≤ first i) g ∧ below (fun i => last i ≤ hi) g) ↔
      ∀ f : Nat → Nat, (∀ i, first i ≤ f i ∧ f i ≤ last i) →
        lo ≤ value f g ∧ value f g ≤ hi := by
  rw [← lowerThreshold, ← upperThreshold]
  constructor
  · rintro ⟨low, high⟩ f hf
    exact ⟨Nat.le_trans low (valueMono _ _ (fun i => (hf i).1) g),
           Nat.le_trans (valueMono _ _ (fun i => (hf i).2) g) high⟩
  · intro hall
    exact ⟨(hall first (fun i => ⟨Nat.le_refl _, ordered i⟩)).1,
           (hall last (fun i => ⟨ordered i, Nat.le_refl _⟩)).2⟩

end RankRace
