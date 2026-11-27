import Std

namespace QuietIntervalCertificates

def advance (step : S → S) : Nat → S → S
  | 0, s => s
  | n+1, s => step (advance step n s)

private theorem advance_add (step : S → S) (a b : Nat) (s : S) :
    advance step (a+b) s = advance step b (advance step a s) := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg step ih

/-- A path has an actual elapsed length, the sum of its edge durations. -/
inductive Path (E : V → Nat → V → Prop) : V → Nat → V → Prop where
  | here (v) : Path E v 0 v
  | add {u v z a b} : Path E u a v → E v b z → Path E u (a+b) z

private theorem appendPath {E : V → Nat → V → Prop}
    (p : Path E u a v) (q : Path E v b z) : Path E u (a+b) z := by
  induction q with
  | here => simpa using p
  | add _ edge ih => simpa [Nat.add_assoc] using Path.add ih edge

private theorem loopPath {E : V → Nat → V → Prop}
    (loop : Path E v d v) (k : Nat) : Path E v (k*d) v := by
  induction k with
  | zero => simpa using Path.here (E := E) v
  | succ k ih => simpa [Nat.succ_mul] using appendPath ih loop

/-- Exact semantic criterion for unparameterized assertions usable on all
states in each source set. The exact reachable sets furnish the converse. -/
theorem assertion_support (E : V → Nat → V → Prop) (step : S → S)
    (initial : S) (start finish : V) (safe : S → Prop) :
    (∃ I : V → S → Prop, I start initial ∧
      (∀ u d v, E u d v → ∀ s, I u s → I v (advance step d s)) ∧
      (∀ s, I finish s → safe s)) ↔
    (∀ d, Path E start d finish → safe (advance step d initial)) := by
  constructor
  · rintro ⟨I, first, closed, last⟩
    have propagate (v : V) (d : Nat) (p : Path E start d v) :
        I v (advance step d initial) := by
      induction p with
      | here => exact first
      | add _ edge ih => rw [advance_add]; exact closed _ _ _ edge _ ih
    intro d p
    exact last _ (propagate finish d p)
  · intro allSafe
    refine ⟨fun v s => ∃ d, Path E start d v ∧ advance step d initial = s, ?_, ?_, ?_⟩
    · exact ⟨0, .here _, rfl⟩
    · rintro u d v edge s ⟨a, p, rfl⟩
      exact ⟨a+d, .add p edge, advance_add step a d initial⟩
    · rintro s ⟨d, p, rfl⟩
      exact allSafe d p

/-- If all sufficiently late genuine states are unsafe, no positive-duration
loop can lie between the source and the asserted safe endpoint. -/
theorem no_productive_loop {E : V → Nat → V → Prop} {step : S → S}
    {initial : S} {start mid finish : V} {safe : S → Prop} {a b d T : Nat}
    (ok : ∀ t, Path E start t finish → safe (advance step t initial))
    (eventual : ∀ t, T ≤ t → ¬ safe (advance step t initial))
    (pre : Path E start a mid) (loop : Path E mid d mid) (post : Path E mid b finish)
    (positive : 0 < d) : False := by
  have p := appendPath (appendPath pre (loopPath loop T)) post
  have long := Nat.le_mul_of_pos_right T positive
  exact eventual _ (by omega) (ok _ p)

/-- Each enabled phase transition is universally valid for its source states.
The cyclic controller can repeat its transitions after the observation time. -/
def PeriodicInvariant (step : S → S) (initial : S) (safe : S → Prop)
    (h H : Nat) : Prop :=
  ∃ I : Nat → S → Prop, I 0 initial ∧
    (∀ a, a < h → ∀ x, I a x → I ((a + 1) % h) (step x)) ∧
    (∀ x, I (H % h) x → safe x)

theorem periodic_invariant_iff (step : S → S) (initial : S) (safe : S → Prop)
    (h H : Nat) (positive : 0 < h) :
    PeriodicInvariant step initial safe h H ↔
      ∀ t, t % h = H % h → safe (advance step t initial) := by
  constructor
  · rintro ⟨I, first, closed, last⟩
    have reachable (t : Nat) : I (t % h) (advance step t initial) := by
      induction t with
      | zero => simpa [advance] using first
      | succ t ih =>
        simpa [advance, Nat.mod_add_mod] using closed _ (Nat.mod_lt _ positive) _ ih
    intro t same
    exact last _ (same ▸ reachable t)
  · intro allSafe
    refine ⟨fun a x => ∃ t, t % h = a ∧ advance step t initial = x, ?_, ?_, ?_⟩
    · exact ⟨0, Nat.zero_mod _, rfl⟩
    · rintro _ _ _ ⟨t, rfl, rfl⟩
      exact ⟨t+1, (Nat.mod_add_mod _ _ _).symm, rfl⟩
    · rintro _ ⟨t, same, rfl⟩
      exact allSafe t same

/-- An unsafe value at every sufficiently late sample H+j*D is also unsafe at
a sample with the observation's residue modulo any proposed positive period. -/
theorem eventually_unsafe_samples_exclude_all_periods
    {step : S → S} {initial : S} {safe : S → Prop} {H D J : Nat}
    (eventual : ∀ j, J ≤ j → ¬ safe (advance step (H+j*D) initial))
    (h : Nat) (positive : 0 < h) : ¬ PeriodicInvariant step initial safe h H := by
  intro certificate
  have allSafe := (periodic_invariant_iff _ _ _ _ _ positive).mp certificate
  have later : J ≤ h * J := Nat.le_mul_of_pos_left J positive
  apply eventual (h * J) later
  apply allSafe
  simp [Nat.mul_assoc]

/-- With a nonwrapping counter, preservation is checked only strictly before
H. Singleton assertions at each elapsed time are a semantic certificate. -/
theorem elapsed_invariant_iff (step : S → S) (initial : S) (safe : S → Prop)
    (H : Nat) :
    (∃ I : Nat → S → Prop, I 0 initial ∧
      (∀ t, t < H → ∀ x, I t x → I (t+1) (step x)) ∧
      (∀ x, I H x → safe x)) ↔ safe (advance step H initial) := by
  constructor
  · rintro ⟨I, first, closed, last⟩
    have reachable (t : Nat) (early : t ≤ H) : I t (advance step t initial) := by
      induction t with
      | zero => exact first
      | succ t ih => exact closed t (by omega) _ (ih (by omega))
    exact last _ (reachable H (Nat.le_refl H))
  · intro finalSafe
    exact ⟨fun t x => advance step t initial = x, rfl, by rintro t _ _ rfl; rfl,
      by rintro _ rfl; exact finalSafe⟩

/-- A fixed certificate can make adaptive raw probes of an offered memory. -/
inductive ProbeTree (Addr Word : Type) where
  | done (accept : Bool)
  | read (a : Addr) (resume : Word → ProbeTree Addr Word)

def answer (t : ProbeTree A W) (m : A → W) : Bool :=
  match t with
  | .done b => b
  | .read a f => answer (f (m a)) m

def queries (t : ProbeTree A W) (m : A → W) : List A :=
  match t with
  | .done _ => []
  | .read a f => a :: queries (f (m a)) m

private theorem same_answers (t : ProbeTree A W) (m n : A → W)
    (agree : ∀ a ∈ queries t m, n a = m a) : answer t n = answer t m := by
  induction t with
  | done => rfl
  | read a f ih =>
    have first : n a = m a := agree a (by simp [queries])
    simp only [answer, first]
    exact ih _ (fun q hq => agree q (List.mem_cons_of_mem a hq))

/-- Any single-address edit that falsifies the verified property forces a
genuine read of that address on this successful path. -/
theorem every_threatened_address [DecidableEq A] (t : ProbeTree A W)
    (real : A → W) (property : (A → W) → Prop) (accept : answer t real = true)
    (sound : ∀ mem, answer t mem = true → property mem)
    (a : A) (changed : W)
    (danger : ¬ property (fun q => if q = a then changed else real q)) :
    a ∈ queries t real := by
  apply Classical.byContradiction
  intro absent
  let alt (q : A) := if q = a then changed else real q
  have same := same_answers t real alt (by
    intro q hq
    have ne : q ≠ a := fun eq => absent (eq ▸ hq)
    simp [alt, ne])
  exact danger (sound alt (same.trans accept))

end QuietIntervalCertificates
