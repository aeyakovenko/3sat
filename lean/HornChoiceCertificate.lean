import Std

namespace HornChoiceCertificate

abbrev Assignment (V : Type) := V → Prop

inductive Literal (V : Type) where
  | pos (var : V)
  | neg (var : V)

def Literal.Holds {V} (x : Assignment V) : Literal V → Prop
  | .pos v => x v
  | .neg v => ¬x v

structure WeightedClause (V : Type) where
  weight : Nat
  literals : List (Literal V)

def ClauseAt {V} (c : WeightedClause V) (t : Nat) (x : Assignment V) : Prop :=
  c.weight ≤ t → ∃ l ∈ c.literals, l.Holds x

def ModelsAt {V} (rows : List (WeightedClause V)) (t : Nat) (x : Assignment V) : Prop :=
  ∀ c ∈ rows, ClauseAt c t x

/-- A negative query specifies a family of forbidden all-true bodies.
    Over finitely many variables this has the expressive power of finite negative CNF. -/
abbrev NegativeQuery (V : Type) := List V → Prop

def Meets {V} (q : NegativeQuery V) (x : Assignment V) : Prop :=
  ∀ body, q body → ¬ (∀ v ∈ body, x v)

/-- A row of alternatives is nonempty, including when it is inactive. -/
structure Alternative (V : Type) where
  weight : Nat
  first : Literal V
  rest : List (Literal V)

def Alternative.options {V} (row : Alternative V) := row.first :: row.rest

abbrev Choice {V I} (exception : I → Alternative V) :=
  (i : I) → {l : Literal V // l ∈ (exception i).options}

def AlternativesAt {V I} (exception : I → Alternative V) (t : Nat) (x : Assignment V) :=
  ∀ i, (exception i).weight ≤ t → ∃ l ∈ (exception i).options, l.Holds x

/-- Selected signed units retain exactly their originating weights. -/
def UnitsAt {V I} (exception : I → Alternative V) (s : Choice exception)
    (t : Nat) (x : Assignment V) :=
  ∀ i, (exception i).weight ≤ t → (s i).val.Holds x

theorem selectAt {V I} (exception : I → Alternative V) (t : Nat) (x : Assignment V) :
    AlternativesAt exception t x ↔ ∃ s, UnitsAt exception s t x := by
  classical
  constructor
  · intro h
    have available (i : I) :
        ∃ l : {l : Literal V // l ∈ (exception i).options},
          (exception i).weight ≤ t → l.val.Holds x := by
      by_cases active : (exception i).weight ≤ t
      · obtain ⟨l, member, truth⟩ := h i active
        exact ⟨⟨l, member⟩, fun _ => truth⟩
      · exact ⟨⟨(exception i).first, List.mem_cons_self⟩, fun hi => (active hi).elim⟩
    exact ⟨fun i => Classical.choose (available i), fun i => Classical.choose_spec (available i)⟩
  · rintro ⟨s, h⟩ i active
    exact ⟨(s i).val, (s i).property, h i active⟩

def FullAt {V I} (ordinary : List (WeightedClause V)) (exception : I → Alternative V)
    (t : Nat) (x : Assignment V) :=
  ModelsAt ordinary t x ∧ AlternativesAt exception t x

/-- The union of the retained original rows of all branches, plus all original alternatives. -/
def KeptAt {V I} (exception : I → Alternative V)
    (keep : Choice exception → List (WeightedClause V)) (t : Nat) (x : Assignment V) :=
  (∀ s, ModelsAt (keep s) t x) ∧ AlternativesAt exception t x

def SatWith {V} (formula : Assignment V → Prop) (q : NegativeQuery V) :=
  ∃ x, formula x ∧ Meets q x

def BranchAt {V I} (ordinary : List (WeightedClause V)) (exception : I → Alternative V)
    (s : Choice exception) (t : Nat) (x : Assignment V) :=
  ModelsAt ordinary t x ∧ UnitsAt exception s t x

/-- The first-firing construction supplies this hypothesis when ordinary rows are Horn.
    All selected auxiliary units can be kept on the branch at their original weights. -/
def BranchCertificates {V I} (ordinary : List (WeightedClause V)) (exception : I → Alternative V)
    (keep : Choice exception → List (WeightedClause V)) :=
  ∀ s t (q : NegativeQuery V),
    SatWith (BranchAt (keep s) exception s t) q ↔ SatWith (BranchAt ordinary exception s t) q

def OriginalRows {V I} (ordinary : List (WeightedClause V)) (exception : I → Alternative V)
    (keep : Choice exception → List (WeightedClause V)) :=
  ∀ s c, c ∈ keep s → c ∈ ordinary

theorem fullModelIsKept {V I} {ordinary : List (WeightedClause V)}
    {exception : I → Alternative V} {keep : Choice exception → List (WeightedClause V)}
    (original : OriginalRows ordinary exception keep) (t : Nat) (x : Assignment V)
    (model : FullAt ordinary exception t x) : KeptAt exception keep t x :=
  ⟨fun s c hc => model.1 c (original s c hc), model.2⟩

theorem thresholdQueryEquivalence {V I} {ordinary : List (WeightedClause V)}
    {exception : I → Alternative V} {keep : Choice exception → List (WeightedClause V)}
    (original : OriginalRows ordinary exception keep)
    (cert : BranchCertificates ordinary exception keep) (t : Nat) (q : NegativeQuery V) :
    SatWith (KeptAt exception keep t) q ↔ SatWith (FullAt ordinary exception t) q := by
  constructor
  · rintro ⟨x, hx, hq⟩
    obtain ⟨s, units⟩ := (selectAt exception t x).mp hx.2
    obtain ⟨y, hy, hyq⟩ := (cert s t q).mp ⟨x, ⟨hx.1 s, units⟩, hq⟩
    exact ⟨y, ⟨hy.1, (selectAt exception t y).mpr ⟨s, hy.2⟩⟩, hyq⟩
  · rintro ⟨x, hx, hq⟩
    exact ⟨x, fullModelIsKept original t x hx, hq⟩

def Included {V} (x y : Assignment V) := ∀ v, x v → y v

def outsideUnits {V} (x : Assignment V) : NegativeQuery V :=
  fun body => ∃ v, ¬ x v ∧ body = [v]

theorem outsideIffIncluded {V} (x y : Assignment V) :
    Meets (outsideUnits x) y ↔ Included y x := by
  classical
  constructor
  · intro h v hv
    apply Classical.byContradiction
    intro absent
    apply h [v] ⟨v, absent, rfl⟩
    simpa using hv
  · intro h body hb allTrue
    obtain ⟨v, absent, rfl⟩ := hb
    exact absent (h v (allTrue v List.mem_cons_self))

def Minimal {V} (formula : Assignment V → Prop) (x : Assignment V) :=
  formula x ∧ ∀ y, formula y → Included y x → Included x y

theorem thresholdMinimalModels {V I} {ordinary : List (WeightedClause V)}
    {exception : I → Alternative V} {keep : Choice exception → List (WeightedClause V)}
    (original : OriginalRows ordinary exception keep)
    (cert : BranchCertificates ordinary exception keep) (t : Nat) (x : Assignment V) :
    Minimal (KeptAt exception keep t) x ↔ Minimal (FullAt ordinary exception t) x := by
  have down (a : Assignment V) (ha : KeptAt exception keep t a) :
      ∃ b, FullAt ordinary exception t b ∧ Included b a := by
    have trivialUnits := (outsideIffIncluded a a).mpr (fun _ hv => hv)
    obtain ⟨b, hb, hu⟩ :=
      (thresholdQueryEquivalence original cert t (outsideUnits a)).mp ⟨a, ha, trivialUnits⟩
    exact ⟨b, hb, (outsideIffIncluded a b).mp hu⟩
  constructor
  · rintro ⟨hx, least⟩
    obtain ⟨b, hb, below⟩ := down x hx
    have above := least b (fullModelIsKept original t b hb) below
    have eq : b = x := funext fun v => propext ⟨below v, above v⟩
    exact ⟨eq ▸ hb, fun y hy => least y (fullModelIsKept original t y hy)⟩
  · rintro ⟨hx, least⟩
    refine ⟨fullModelIsKept original t x hx, ?_⟩
    intro y hy below
    obtain ⟨b, hb, inside⟩ := down y hy
    have above := least b hb (fun v hv => below v (inside v hv))
    exact fun v hv => inside v (above v hv)

/-- A witness satisfying all original rows other than its own forces that row
    into every rejecting subset, including a subset chosen with unbounded computation. -/
theorem privateWitnessForcesRow {V} {ordinary core : List (WeightedClause V)} (t : Nat)
    (row : WeightedClause V) (witness : Assignment V)
    (others : ∀ c ∈ ordinary, c ≠ row → ClauseAt c t witness)
    (sub : ∀ c ∈ core, c ∈ ordinary) (reject : ¬ ∃ x, ModelsAt core t x) :
    row ∈ core := by
  classical
  apply Classical.byContradiction
  intro missing
  apply reject
  refine ⟨witness, fun c hc => others c (sub c hc) ?_⟩
  exact fun h => missing (h ▸ hc)

end HornChoiceCertificate
