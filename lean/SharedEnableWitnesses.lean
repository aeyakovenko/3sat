import Std

/-! Witness sharing for required positive enable coordinates. The index sets
and witness type can be infinite. The row model at the end permits arbitrary
dependence on frozen bits and at most one free positive guard per row. -/
namespace SharedEnableWitnesses

universe u v w z
abbrev Mask (ι : Type u) := ι → Prop

def Included {ι : Type u} (E F : Mask ι) : Prop := ∀ i, E i → F i
def inter {ι : Type u} (E F : Mask ι) : Mask ι := fun i => E i ∧ F i

structure System (ι : Type u) (H : Type v) where
  good : H → Prop
  required : H → Mask ι

namespace System

variable {ι : Type u} {H : Type v} (P : System ι H)

def Holds (E : Mask ι) (h : H) : Prop := P.good h ∧ Included (P.required h) E
def Accepted (E : Mask ι) : Prop := ∃ h, P.Holds E h
def Minimal (E : Mask ι) : Prop :=
  P.Accepted E ∧ ∀ F, Included F E → P.Accepted F → Included E F

theorem mono {E G : Mask ι} {h : H} (eg : Included E G) (hw : P.Holds E h) :
    P.Holds G h := ⟨hw.1, fun i hi => eg i (hw.2 i hi)⟩

theorem holds_inter_iff {E F : Mask ι} {h : H} :
    P.Holds (inter E F) h ↔ P.Holds E h ∧ P.Holds F h := by
  constructor
  · intro he
    exact ⟨P.mono (fun _ h => h.1) he, P.mono (fun _ h => h.2) he⟩
  · intro ⟨he, hf⟩
    exact ⟨he.1, fun i hi => ⟨he.2 i hi, hf.2 i hi⟩⟩

/-- A witness at a minimal input uniquely determines that entire input. -/
theorem required_eq_minimal {E : Mask ι} {h : H} (hE : P.Minimal E)
    (hh : P.Holds E h) : P.required h = E := by
  have hr : P.Accepted (P.required h) := ⟨h, hh.1, fun _ hi => hi⟩
  have reverse := hE.2 (P.required h) hh.2 hr
  exact funext fun i => propext ⟨hh.2 i, reverse i⟩

theorem distinct_minimal_witnesses {E F : Mask ι} {h k : H}
    (he : P.Minimal E) (hf : P.Minimal F) (hne : E ≠ F)
    (hw : P.Holds E h) (kw : P.Holds F k) : h ≠ k := by
  rintro rfl
  exact hne ((P.required_eq_minimal he hw).symm.trans (P.required_eq_minimal hf kw))

abbrev MinimalBelow (G : Mask ι) := {E : Mask ι // P.Minimal E ∧ Included E G}
abbrev WitnessAt (G : Mask ι) := {h : H // P.Holds G h}

/-- All witnesses at all the minima survive at G with disjoint images. This
injection of the disjoint union uses no choice of representative witnesses. -/
theorem all_minimal_fibers_embed (G : Mask ι) :
    ∃ embed : (Σ E : P.MinimalBelow G, P.WitnessAt E.val) → P.WitnessAt G,
      ∀ a b, embed a = embed b → a = b := by
  let embed : (Σ E : P.MinimalBelow G, P.WitnessAt E.val) → P.WitnessAt G :=
    fun ⟨E, w⟩ => ⟨w.val, P.mono E.property.2 w.property⟩
  refine ⟨embed, ?_⟩
  rintro ⟨E, a⟩ ⟨F, b⟩ eq
  have hab : a.val = b.val := congrArg Subtype.val eq
  have hEF : E = F := Subtype.ext <|
    (P.required_eq_minimal E.property.1 a.property).symm.trans <|
      (congrArg P.required hab).trans (P.required_eq_minimal F.property.1 b.property)
  subst F
  exact congrArg (fun w => Sigma.mk E w) (Subtype.ext hab)

/-- Any choice of one witness per minimal mask below G yields an injection.
Moreover the requirement set of each image recovers its source mask. -/
theorem chosen_injection (G : Mask ι) (choose : P.MinimalBelow G → H)
    (works : ∀ E, P.Holds E.val (choose E)) :
    ∃ embed : P.MinimalBelow G → P.WitnessAt G,
      (∀ E, (embed E).val = choose E ∧ P.required (embed E).val = E.val) ∧
      (∀ E F, embed E = embed F → E = F) := by
  let embed : P.MinimalBelow G → P.WitnessAt G :=
    fun E => ⟨choose E, P.mono E.property.2 (works E)⟩
  have recovers (E : P.MinimalBelow G) : P.required (embed E).val = E.val :=
    P.required_eq_minimal E.property.1 (works E)
  refine ⟨embed, fun E => ⟨rfl, recovers E⟩, ?_⟩
  intro E F eq
  apply Subtype.ext
  exact (recovers E).symm.trans ((congrArg (fun w => P.required w.val) eq).trans (recovers F))

theorem minimal_witness_injection (G : Mask ι) :
    ∃ embed : P.MinimalBelow G → P.WitnessAt G,
      ∀ E F, embed E = embed F → E = F := by
  let choose : P.MinimalBelow G → H := fun E => Classical.choose E.property.1.1
  have works (E : P.MinimalBelow G) : P.Holds E.val (choose E) :=
    Classical.choose_spec E.property.1.1
  obtain ⟨embed, _, inj⟩ := P.chosen_injection G choose works
  exact ⟨embed, inj⟩

end System

/-- Each row has at most one free positive enable. Everything else in the row
can depend arbitrarily on the fixed signed coordinates and the hidden witness.
For a specified set S of coordinates use S and its complement as the types of
signed and free coordinates respectively. -/
structure GuardedRows (Row : Type u) (Signed : Type v) (Free : Type w) (H : Type z) where
  localPass : Row → Mask Signed → H → Prop
  enable : Row → Option Free

namespace GuardedRows

variable {Row : Type u} {Signed : Type v} {Free : Type w} {H : Type z}
variable (R : GuardedRows Row Signed Free H)

def Holds (fixed : Mask Signed) (E : Mask Free) (h : H) : Prop :=
  ∀ r, R.localPass r fixed h ∨ ∃ i, R.enable r = some i ∧ E i

def specialize (fixed : Mask Signed) : System Free H where
  good h := ∀ r, R.enable r = none → R.localPass r fixed h
  required h i := ∃ r, R.enable r = some i ∧ ¬ R.localPass r fixed h

theorem holds_iff_specialize (fixed : Mask Signed) (E : Mask Free) (h : H) :
    R.Holds fixed E h ↔ (R.specialize fixed).Holds E h := by
  constructor
  · intro allPass
    constructor
    · intro r hn
      rcases allPass r with hr | ⟨_, hi, _⟩
      · exact hr
      · simp [hn] at hi
    · intro i hi
      obtain ⟨r, hri, hfalse⟩ := hi
      obtain ⟨j, hrj, hj⟩ := (allPass r).resolve_left hfalse
      exact (Option.some.inj (hrj.symm.trans hri)) ▸ hj
  · intro hw r
    by_cases hr : R.localPass r fixed h
    · exact Or.inl hr
    · cases hg : R.enable r with
      | none => exact Or.inl (hw.1 r hg)
      | some i => exact Or.inr ⟨i, rfl, hw.2 i ⟨r, hg, hr⟩⟩

theorem fixed_slice_inter (fixed : Mask Signed) (E F : Mask Free) (h : H) :
    R.Holds fixed (inter E F) h ↔ R.Holds fixed E h ∧ R.Holds fixed F h := by
  simp only [R.holds_iff_specialize, System.holds_inter_iff]

end GuardedRows

end SharedEnableWitnesses
