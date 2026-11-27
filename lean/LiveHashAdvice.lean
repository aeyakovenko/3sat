import Std

namespace LiveHashAdvice

variable {Key Cell : Type}

/-- A positive key forces all its bit-table probes to return one. -/
def forced (want : Key → Prop) (reads : Key → Cell → Prop) (c : Cell) : Prop :=
  ∃ y, want y ∧ reads y c

/-- An AND query is true exactly when all its probed bit cells are true. -/
def represents (domain want : Key → Prop) (reads : Key → Cell → Prop)
    (chosen : Cell → Prop) : Prop :=
  ∀ x, domain x → (want x ↔ ∀ c, reads x c → chosen c)

/-- One private probe at every key in the test domain gives exact answers, including
    zeros at keys outside the active support. No promises on keys outside the domain. -/
theorem private_probe_exact (domain support want : Key → Prop) (reads : Key → Cell → Prop)
    (inside : ∀ x, want x → support x)
    (privateAt : ∀ x, domain x → ∃ c, reads x c ∧
      ∀ y, support y → reads y c → y = x) :
    represents domain want reads (forced want reads) := by
  intro x hx
  constructor
  · intro yes c hc
    exact ⟨x, yes, hc⟩
  · intro allTrue
    obtain ⟨c, hc, unique⟩ := privateAt x hx
    obtain ⟨y, hy, hcy⟩ := allTrue c hc
    exact unique y (inside y hy) hcy ▸ hy

/-- A failed representation has a zero query whose every probed cell is
    forced positive by a true query in the same domain. -/
theorem no_representation_iff (domain want : Key → Prop) (reads : Key → Cell → Prop) :
    (¬ ∃ chosen, represents domain want reads chosen) ↔
      ∃ x, domain x ∧ ¬ want x ∧
        ∀ c, reads x c → ∃ y, domain y ∧ want y ∧ reads y c := by
  classical
  constructor
  · intro fail
    apply Classical.byContradiction
    intro noObstruction
    apply fail
    let chosen := fun c => ∃ y, domain y ∧ want y ∧ reads y c
    refine ⟨chosen, fun x hx => ⟨?_, ?_⟩⟩
    · intro h c hc
      exact ⟨x, hx, h, hc⟩
    · intro h
      exact Classical.byContradiction (fun bad => noObstruction ⟨x, hx, bad, h⟩)
  · rintro ⟨x, hx, nx, blocked⟩ ⟨chosen, good⟩
    apply nx
    apply (good x hx).mpr
    intro c hc
    obtain ⟨y, hy, yes, consumes⟩ := blocked c hc
    exact (good y hy).mp yes c consumes

/-- For an ordered list of L hash probes, choose one true key per probe of
    the bad zero. Repeated witness keys and repeated cells are permitted. -/
theorem ordered_obstruction {L : Nat} (domain want : Key → Prop) (cell : Key → Fin L → Cell)
    (fail : ¬ ∃ chosen, represents domain want (fun x c => ∃ j, cell x j = c) chosen) :
    ∃ x, domain x ∧ ¬ want x ∧ ∃ witness : Fin L → Key,
      ∀ j, domain (witness j) ∧ want (witness j) ∧ ∃ i, cell (witness j) i = cell x j := by
  classical
  obtain ⟨x, hx, nx, allProbes⟩ := (no_representation_iff _ _ _).mp fail
  have h (j : Fin L) := allProbes (cell x j) ⟨j, rfl⟩
  exact ⟨x, hx, nx, fun j => Classical.choose (h j), fun j => Classical.choose_spec (h j)⟩

/-- In a secondary bucket with one support key, each table tests its own digit.
    The full word bit is retrieved only at the original key. -/
theorem singleton_product_mask {Digit Key Value : Type} (coordinate : Key → Digit → Value)
    (x y : Key) (firstDigit : Digit) (label : Prop)
    (injective : (∀ j, coordinate x j = coordinate y j) → x=y) :
    (∀ j, coordinate x j = coordinate y j ∧ label) ↔ x=y ∧ label := by
  constructor
  · intro all
    exact ⟨injective (fun j => (all j).1), (all firstDigit).2⟩
  · rintro ⟨rfl, h⟩ j
    exact ⟨rfl, h⟩

end LiveHashAdvice
