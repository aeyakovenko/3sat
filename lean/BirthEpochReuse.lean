import Std

namespace BirthEpochReuse

abbrev Mem := Nat → Nat

def write (m : Mem) (a v : Nat) : Mem :=
  fun b => if b = a then v else m b

inductive Program where
  | halt (answer : Bool)
  | input (pin : Nat) (next : Bool → Program)
  | load (addr : Nat) (next : Nat → Program)
  | store (addr val : Nat) (next : Program)

def run (p : Program) (x : Nat → Bool) (m : Mem) : Bool :=
  match p with
  | .halt a => a
  | .input i k => run (k (x i)) x m
  | .load a k => run (k (m a)) x m
  | .store a v k => run k x (write m a v)

/-- Check only the genuine path. Local stores update both the true machine and its
    simulation from the start-of-epoch memory. -/
def agreesOnRun (p : Program) (x y : Nat → Bool) (m baseline : Mem) : Prop :=
  match p with
  | .halt _ => True
  | .input i k => x i = y i ∧ agreesOnRun (k (x i)) x y m baseline
  | .load a k => m a = baseline a ∧ agreesOnRun (k (m a)) x y m baseline
  | .store a v k => agreesOnRun k x y (write m a v) (write baseline a v)

theorem replay (p : Program) (x y : Nat → Bool) (m baseline : Mem)
    (h : agreesOnRun p x y m baseline) : run p x m = run p y baseline := by
  induction p generalizing m baseline with
  | halt _ => rfl
  | input i k ih =>
    obtain ⟨eq, tail⟩ := h
    simpa only [run, ← eq] using ih (x i) m baseline tail
  | load a k ih =>
    obtain ⟨eq, tail⟩ := h
    simpa only [run, ← eq] using ih (m a) m baseline tail
  | store a v k ih =>
    exact ih _ _ h

/-- An address touched by no write retains its previous value. -/
theorem no_write_preserves (stores : List (Nat × Nat)) (a : Nat) (m : Mem)
    (untouched : ∀ av ∈ stores, av.1 ≠ a) :
    (stores.foldl (fun current av => write current av.1 av.2) m) a = m a := by
  induction stores generalizing m with
  | nil => rfl
  | cons av tail ih =>
    have neq := untouched av (by simp)
    rw [List.foldl_cons, ih (write m av.1 av.2) (by
      intro pair hp
      exact untouched pair (by simp [hp]))]
    simp [write, Ne.symm neq]

/-- A single latest writer cannot be charged to disjoint half-open epochs. -/
theorem distinct_source_slots (lo hi lo' hi' last₁ last₂ : Nat)
    (separated : hi ≤ lo') (endFirst : last₁ < hi) (startSecond : lo' ≤ last₂)
    (_startFirst : lo ≤ last₁) (_endSecond : last₂ < hi') : last₁ ≠ last₂ := by
  omega

/-- Counting version of the conditional probability inequality, after clearing
    denominators and rounding the spectral error upward. -/
theorem mass_lower_bound (rankMass retrieved catalogMass err : Nat)
    (coverage : rankMass ≤ retrieved + catalogMass)
    (predictor : catalogMass ≤ 2 * retrieved + err) :
    rankMass ≤ 3 * retrieved + err := by omega

end BirthEpochReuse
