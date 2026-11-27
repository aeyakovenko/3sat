import Std

namespace CommonSolverLevels

/-- The code has no erroneous input of any length through the cap. -/
def Clean {Code : Type} (errorAt : Code → Nat → Prop) (code : Code) (cap : Nat) : Prop :=
  ∀ n, n ≤ cap → ¬ errorAt code n

theorem clean_down {Code : Type} {errorAt : Code → Nat → Prop} {code : Code} {a b : Nat}
    (ab : a ≤ b) (clean : Clean errorAt code b) : Clean errorAt code a :=
  fun n hn => clean n (Nat.le_trans hn ab)

/-- Charge each exceptional level to an exposed candidate. Passing the next
    filter makes it impossible to charge that candidate at an earlier level. -/
theorem exceptional_count {Code : Type} [DecidableEq Code]
    (errorAt : Code → Nat → Prop) (small large : Nat → Nat)
    (separated : ∀ i j, i < j → large i ≤ small j)
    (witness : Nat → Code) (levels : List Nat) (pool : List Code)
    (ordered : levels.Pairwise (· < ·))
    (exceptional : ∀ i ∈ levels,
      witness i ∈ pool ∧ Clean errorAt (witness i) (small i) ∧
        ¬ Clean errorAt (witness i) (large i)) :
    levels.length ≤ pool.length := by
  induction levels generalizing pool with
  | nil => simp
  | cons i tail ih =>
    obtain ⟨before, sorted⟩ := List.pairwise_cons.mp ordered
    obtain ⟨mem, _, fails⟩ := exceptional i (by simp)
    have positive := List.length_pos_of_mem mem
    have bound := ih (pool.erase (witness i)) sorted (by
      intro j hj
      obtain ⟨inPool, passes, failsLater⟩ :=
        exceptional j (List.mem_cons_of_mem i hj)
      have different : witness j ≠ witness i := by
        intro eq
        rw [eq] at passes
        exact fails (clean_down (separated i j (before j hj)) passes)
      exact ⟨(List.mem_erase_of_ne different).mpr inPool, passes, failsLater⟩)
    rw [List.length_erase_of_mem mem] at bound
    simp
    omega

/-- The same count when the test simply retires a code the first time
    it signals. Its signal may abbreviate existence of a witness on any pin. -/
theorem first_signal_count {Code : Type} [DecidableEq Code]
    (signal : Code → Nat → Prop) (witness : Nat → Code)
    (levels : List Nat) (pool : List Code) (ordered : levels.Pairwise (· < ·))
    (charged : ∀ i ∈ levels, witness i ∈ pool ∧
      (∀ j, j < i → ¬ signal (witness i) j) ∧ signal (witness i) i) :
    levels.length ≤ pool.length := by
  let errorAt := fun c n => ∃ j, n = j+1 ∧ signal c j
  apply exceptional_count errorAt id Nat.succ (fun _ _ h => h) witness levels pool ordered
  intro i hi
  obtain ⟨mem, previous, now⟩ := charged i hi
  refine ⟨mem, ?_, ?_⟩
  · intro n hn fault
    obtain ⟨j, rfl, atJ⟩ := fault
    exact previous j hn atJ
  · intro through
    exact through (i+1) (Nat.le_refl _) ⟨i, rfl, now⟩

/-- At a good signed vertex every candidate that signals would force truth
    to equal the prescribed sign, while the equation would flip it. -/
theorem signed_good {Code : Type} {pin truth claimed : Bool}
    {signal : Code → Prop}
    (signed : truth = (pin ^^ claimed))
    (found : claimed = true ↔ ∃ c, signal c)
    (agreement : ∀ c, signal c → truth = pin) :
    truth = pin ∧ ∀ c, ¬ signal c := by
  have no : claimed = false := by
    cases h : claimed with
    | false => rfl
    | true =>
      obtain ⟨c, hc⟩ := found.mp h
      have same := agreement c hc
      cases pin <;> simp_all
  constructor
  · simpa [no] using signed
  · intro c hc
    have yes := found.mpr ⟨c, hc⟩
    simp_all

/-- If a fixed admitted code makes any offer, it has a first seed, even when
    the offer predicate is given only propositionally. Finite seeds can be
    extended to naturals by declaring all out-of-range offers false. -/
private theorem first_seed (offers : Nat → Prop) (r : Nat) (hr : offers r) :
    ∃ s, offers s ∧ ∀ t, t < s → ¬ offers t := by
  classical
  induction r using Nat.strongRecOn with
  | ind r ih =>
    by_cases earlier : ∃ t, t < r ∧ offers t
    · obtain ⟨t, lt, active⟩ := earlier
      exact ih t lt active
    · exact ⟨r, hr, fun t lt active => earlier ⟨t, lt, active⟩⟩

/-- At the first seed, the existential test may select this code itself.
    Correctness on the whole scale therefore excludes all its offers, even
    at seeds where another code generated an exception. -/
theorem sound_code_never_offers {Code : Type} (raw : Code → Nat → Bool → Prop)
    (admitted : Code → Prop) (truth flip : Nat → Bool → Bool)
    (signed : ∀ r b, truth r b = (b ^^ flip r b))
    (first_flips : ∀ e r b, admitted e → raw e r b →
      (∀ t, t < r → ∀ c, ¬ raw e t c) → flip r b = true)
    (code : Code) (present : admitted code)
    (sound : ∀ r b, raw code r b → truth r b = b) :
    ∀ r b, ¬ raw code r b := by
  intro r b active
  obtain ⟨s, ⟨pin, atS⟩, earlier⟩ :=
    first_seed (fun t => ∃ c, raw code t c) r ⟨b, active⟩
  have hit := first_flips code s pin present atS
    (fun t lt c offer => earlier t lt ⟨c, offer⟩)
  have eqn := signed s pin
  have correct := sound s pin atS
  cases pin <;> simp_all

/-- A source accepting exactly on a certified rejection by a surviving
    candidate forces a negative instance and rules out each such certificate,
    provided all survivors are correct on the constructed instance. -/
theorem common_negative {Code : Type} (verdict : Prop)
    (live rejects short : Code → Prop)
    (sound : ∀ c, live c → (rejects c ↔ ¬ verdict))
    (self : verdict ↔ ∃ c, live c ∧ rejects c ∧ short c) :
    ¬ verdict ∧ ∀ c, live c → ¬ short c := by
  have neg : ¬ verdict := by
    intro yes
    obtain ⟨c, active, no, _⟩ := self.mp yes
    exact (sound c active).mp no yes
  refine ⟨neg, ?_⟩
  intro c active cheap
  exact neg (self.mpr ⟨c, active, (sound c active).mpr neg, cheap⟩)

end CommonSolverLevels
