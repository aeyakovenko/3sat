import Std

namespace BatchAdviceElimination

/-- A checked search either returns a genuine bad advice still in the list or abstains. -/
structure Driver (bad : Nat → Prop) where
  pick : List Nat → Option Nat
  sound : ∀ s a, pick s = some a → a ∈ s ∧ bad a

/-- Stop trying a driver at its first abstention. The counter bounds successful deletions. -/
def drain {bad : Nat → Prop} (d : Driver bad) : Nat → List Nat → List Nat
  | 0, s => s
  | n+1, s => match d.pick s with
    | none => s
    | some a => drain d n (s.erase a)

def complete {bad : Nat → Prop} (d : Driver bad) : Prop :=
  ∀ s, d.pick s = none → ∀ x ∈ s, ¬bad x

theorem retain {bad : Nat → Prop} (d : Driver bad) (n : Nat) (s : List Nat) (x : Nat)
    (good : ¬bad x) : x ∈ drain d n s ↔ x ∈ s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases h : d.pick s with
    | none => simp [drain,h]
    | some a =>
      have neq : x ≠ a := by intro eq; subst x; exact good (d.sound _ _ h).2
      simp [drain,h,ih,List.mem_erase_of_ne neq]

theorem subset {bad : Nat → Prop} (d : Driver bad) (n : Nat) (s : List Nat) :
    drain d n s ⊆ s := by
  induction n generalizing s with
  | zero => exact fun _ h => h
  | succ n ih =>
    cases h : d.pick s with
    | none => simp [drain,h]
    | some a =>
      simp only [drain,h]
      intro x hx
      exact List.mem_of_mem_erase (ih _ hx)

theorem complete_removes {bad : Nat → Prop} (d : Driver bad) (c : complete d)
    (n : Nat) (s : List Nat) (enough : s.length ≤ n) : ∀ x ∈ drain d n s, ¬bad x := by
  induction n generalizing s with
  | zero =>
    have : s = [] := by cases s <;> simp_all
    simp [this,drain]
  | succ n ih =>
    cases h : d.pick s with
    | none => simpa [drain,h] using c s h
    | some a =>
      have m := (d.sound _ _ h).1
      have len := List.length_erase_of_mem m
      exact (by simpa [drain,h] using ih (s.erase a) (by omega))

def run {bad : Nat → Prop} (ds : List (Driver bad)) (s : List Nat) : List Nat :=
  ds.foldl (fun t d => drain d t.length t) s

theorem run_subset {bad : Nat → Prop} (ds : List (Driver bad)) (s : List Nat) : run ds s ⊆ s := by
  induction ds generalizing s with
  | nil => exact fun _ h => h
  | cons d ds ih =>
    intro x hx
    exact subset d s.length s (ih _ hx)

theorem run_retain {bad : Nat → Prop} (ds : List (Driver bad)) (s : List Nat) (x : Nat)
    (good : ¬bad x) : x ∈ run ds s ↔ x ∈ s := by
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih =>
    change x ∈ run ds (drain d s.length s) ↔ x ∈ s
    exact (ih _).trans (retain d s.length s x good)

theorem exact_stage {bad : Nat → Prop} (before after : List (Driver bad))
    (honest : Driver bad) (c : complete honest) (s : List Nat) (x : Nat) :
    x ∈ run (before ++ honest :: after) s ↔ x ∈ s ∧ ¬bad x := by
  constructor
  · intro hx
    refine ⟨run_subset _ _ hx, ?_⟩
    let t := run before s
    have mid : x ∈ run after (drain honest t.length t) := by
      simpa [t,run,List.foldl_append] using hx
    exact complete_removes honest c t.length t (Nat.le_refl _) x (run_subset _ _ mid)
  · intro hx
    exact (run_retain _ _ _ hx.2).mpr hx.1

/-- Number of calls to the larger candidate, including its first failed search if attempted. -/
def attempts {bad : Nat → Prop} (d : Driver bad) : Nat → List Nat → Nat
  | 0, _ => 0
  | n+1, s => match d.pick s with
    | none => 1
    | some a => 1 + attempts d n (s.erase a)

theorem charge_driver {bad : Nat → Prop} (d : Driver bad) (n : Nat) (s : List Nat) :
    attempts d n s + (drain d n s).length ≤ s.length + 1 := by
  induction n generalizing s with
  | zero => simp [attempts,drain]
  | succ n ih =>
    cases h : d.pick s with
    | none => simp [attempts,drain,h]; omega
    | some a =>
      have mem := (d.sound _ _ h).1
      have pos : 0 < s.length := by cases s <;> simp_all
      have len := List.length_erase_of_mem mem
      have prior := ih (s.erase a)
      simp only [attempts,drain,h]
      omega

def totalAttempts {bad : Nat → Prop} : List (Driver bad) → List Nat → Nat
  | [], _ => 0
  | d::ds, s => attempts d s.length s + totalAttempts ds (drain d s.length s)

theorem additive_cost {bad : Nat → Prop} (ds : List (Driver bad)) (s : List Nat) :
    totalAttempts ds s + (run ds s).length ≤ s.length + ds.length := by
  induction ds generalizing s with
  | nil => simp [totalAttempts,run]
  | cons d ds ih =>
    have first := charge_driver d s.length s
    have later := ih (drain d s.length s)
    change attempts d s.length s + totalAttempts ds (drain d s.length s) +
      (run ds (drain d s.length s)).length ≤ s.length + (d::ds).length
    simp only [List.length_cons]
    omega

end BatchAdviceElimination
