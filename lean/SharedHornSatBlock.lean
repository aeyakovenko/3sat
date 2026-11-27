import Std

/-! A shared decoder supplies atoms to all sites in one block. Each site tests one
ground Horn obligation. Site-dependent rules are permitted after a common target and
cap have been selected. The semantic soundness and running-time bridges to a native
program are hypotheses; the logic does not require the intersection to be encodable. -/

namespace SharedHornSatBlock

abbrev Permission (Atom : Type) := Atom → Prop

structure Horn (Atom : Type) where
  body : List Atom
  head : Option Atom

def Required (head : Option Atom) (p : Permission Atom) : Prop :=
  match head with
  | some a => p a
  | none => False

def Horn.Holds (clause : Horn Atom) (p : Permission Atom) : Prop :=
  (∀ a ∈ clause.body, p a) → Required clause.head p

/-- The semantic table selected by "NO valid chart omits this atom." -/
def omissions (admissible : Chart → Prop) (permit : Chart → Permission Atom) : Permission Atom :=
  fun a => ¬ ∃ c, admissible c ∧ ¬permit c a

theorem omissions_iff (admissible : Chart → Prop) (permit : Chart → Permission Atom) (a : Atom) :
    omissions admissible permit a ↔ ∀ c, admissible c → permit c a := by
  classical
  constructor
  · intro h c hc
    by_cases holds : permit c a
    · exact holds
    · exact False.elim (h ⟨c, hc, holds⟩)
  · intro h bad
    obtain ⟨c, hc, nope⟩ := bad
    exact nope (h c hc)

/-- Nonemptiness matters for a Horn clause with a forbidden (false) head. -/
theorem omissions_closed (admissible : Chart → Prop) (permit : Chart → Permission Atom)
    (inhabited : ∃ c, admissible c) (clause : Horn Atom)
    (valid : ∀ c, admissible c → clause.Holds (permit c)) :
    clause.Holds (omissions admissible permit) := by
  intro body
  have allBody (c : Chart) (hc : admissible c) : ∀ a ∈ clause.body, permit c a :=
    fun a ha => (omissions_iff admissible permit a).1 (body a ha) c hc
  have allHeads (c : Chart) (hc : admissible c) := valid c hc (allBody c hc)
  cases hh : clause.head with
  | none =>
    obtain ⟨c, hc⟩ := inhabited
    simpa only [hh, Required] using allHeads c hc
  | some a =>
    simp only [hh, Required]
    apply (omissions_iff admissible permit a).2
    intro c hc
    simpa only [hh, Required] using allHeads c hc

theorem same_permissions (p q : Permission Atom) (same : ∀ a, p a ↔ q a) : p = q :=
  funext (fun a => propext (same a))

structure Lock (Site Atom : Type) where
  cap : Nat
  target : Site
  table : Permission Atom

/-- Every completing site consults the same lock; a stalled decoder need not supply a target. -/
def LocalPass (decoded : Option (Lock Site Atom)) (rules : Site → Site → Horn Atom)
    (latched : Site → Prop) : Prop :=
  ∀ z, latched z → ∃ d, decoded = some d ∧ (rules d.target z).Holds d.table

/-- The clauses at all sites cover a native semantic chart for the target. A valid
chart proving absence of its return would contradict a latch at that same site. -/
def SemanticSound (rules : Site → Site → Horn Atom) (latched : Site → Prop) : Prop :=
  ∀ y p, (∀ z, (rules y z).Holds p) → ¬latched y

theorem some_quiet [Nonempty Site] (decoded : Option (Lock Site Atom))
    (rules : Site → Site → Horn Atom) (latched : Site → Prop)
    (localPass : LocalPass decoded rules latched) (sound : SemanticSound rules latched) :
    ∃ z, ¬latched z := by
  classical
  obtain ⟨first⟩ := (inferInstance : Nonempty Site)
  by_cases all : ∀ z, latched z
  · obtain ⟨d, hd, _⟩ := localPass first (all first)
    have every (z : Site) : (rules d.target z).Holds d.table := by
      obtain ⟨e, he, pass⟩ := localPass z (all z)
      have eqn : e = d := Option.some.inj (he.symm.trans hd)
      simpa only [eqn] using pass
    exact False.elim (sound d.target d.table every (all d.target))
  · exact Classical.not_forall.mp all

/-- Availability at any affordable cap makes the common search finish at a cap with
a genuine chart (possibly smaller) and choose a target with a nonempty chart set.
Each successful local test must also finish by the actual observation for this
direction. Neither assertion follows merely from equality of the sites' code. -/
def TimelySearch (affordable : Nat → Prop) (admit : Nat → Site → Chart → Prop)
    (permit : Chart → Permission Atom) (decoded : Option (Lock Site Atom))
    (rules : Site → Site → Horn Atom) (latched : Site → Prop) : Prop :=
  (∃ w y c, affordable w ∧ admit w y c) →
    ∃ d, decoded = some d ∧ (∃ c, admit d.cap d.target c) ∧
      (∀ a, d.table a ↔ omissions (admit d.cap d.target) permit a) ∧
      ∀ z, (rules d.target z).Holds d.table → latched z

/-- No affordable chart can exist anywhere in this block when the selected
solver is truthful and timely in precisely the sense of TimelySearch. -/
theorem no_affordable_chart [Nonempty Site] (affordable : Nat → Prop)
    (admit : Nat → Site → Chart → Prop) (permit : Chart → Permission Atom)
    (decoded : Option (Lock Site Atom)) (rules : Site → Site → Horn Atom) (latched : Site → Prop)
    (valid : ∀ w y c, admit w y c → ∀ z, (rules y z).Holds (permit c))
    (localPass : LocalPass decoded rules latched) (sound : SemanticSound rules latched)
    (timely : TimelySearch affordable admit permit decoded rules latched) :
    ¬ ∃ w y c, affordable w ∧ admit w y c := by
  intro available
  obtain ⟨d, _, nonempty, same, finish⟩ := timely available
  obtain ⟨z, quiet⟩ := some_quiet decoded rules latched localPass sound
  apply quiet
  apply finish
  rw [same_permissions _ _ same]
  exact omissions_closed _ permit nonempty _ (fun c hc => valid _ _ c hc z)

end SharedHornSatBlock
