import Std

namespace PrivateTripleAnchors

variable {V : Type}
abbrev Assignment (V : Type) := V → Bool

structure Cube (V : Type) where
  has : V → Prop
  bit : V → Bool

def Violates (e : Cube V) (s : Assignment V) : Prop :=
  ∀ i, e.has i → s i = e.bit i

def PrivateAt (family : Cube V → Prop) (e : Cube V) (w : Assignment V) : Prop :=
  Violates e w ∧ ∀ f, family f → f ≠ e → ¬ Violates f w

def IsModel (family : Cube V → Prop) (s : Assignment V) : Prop :=
  ∀ e, family e → ¬ Violates e s

/-- If the anchor variables in a coherent clause have attained the forbidden signs,
    satisfaction fixes its only remaining variable. -/
theorem forced_away (e : Cube V) (s w : Assignment V) (d : V)
    (unsatCube : ¬ Violates e w)
    (coherent : ∀ i, e.has i → e.bit i = s i)
    (onAnchors : ∀ i, e.has i → i ≠ d → w i = s i) :
    w d = !(s d) := by
  have different : w d ≠ s d := by
    intro equal
    apply unsatCube
    intro i member
    rw [coherent i member]
    by_cases h : i = d
    · simpa [h] using equal
    · exact onAnchors i member h
  cases h : w d <;> cases t : s d <;> simp_all

/-- The local hypotheses supplied by a clean anchor set already give a total model.
    For each proposed conflicting clause D, t is a distinct private anchor cube.
    Its witness meets all the forbidden anchor bits of each coherent mixed cube f. -/
theorem anchor_model (family : Cube V → Prop) (s : Assignment V)
    (anchors : ∀ D, family D → ∃ t w,
      t ≠ D ∧ PrivateAt family t w ∧
      ∀ d, D.has d → ∃ f, family f ∧ f ≠ t ∧
        (∀ i, f.has i → f.bit i = s i) ∧
        ∀ i, f.has i → i ≠ d → w i = s i) :
    IsModel family (fun i => !(s i)) := by
  intro D inFamily opposite
  obtain ⟨t, w, diff, privateT, mixed⟩ := anchors D inFamily
  apply privateT.2 D inFamily (Ne.symm diff)
  intro d onD
  obtain ⟨f, inF, notT, coherent, onAnchors⟩ := mixed d onD
  exact (forced_away f s w d (privateT.2 f inF notT) coherent onAnchors).trans
    (opposite d onD)

/-- Every private cube intersects the variables touched by representatives of an
    unsatisfiable residual, if its witness agrees off that cube with the base on
    all variables that may differ between the witness and its base extension. -/
theorem hits_representatives (family reps : Cube V → Prop)
    (ordinary touched : V → Prop) (e : Cube V) (w base : Assignment V)
    (isPrivate : PrivateAt family e w)
    (outside : ∀ i, ordinary i → ¬ e.has i → w i = base i)
    (sameAux : ∀ i, ¬ ordinary i → w i = base i)
    (everyRep : ∀ f, reps f → family f ∧ f ≠ e ∧ ∀ i, f.has i → ordinary i → touched i)
    (blocked : ∃ f, reps f ∧ Violates f base) :
    ∃ i, e.has i ∧ touched i := by
  classical
  apply Classical.byContradiction
  intro empty
  obtain ⟨f, hr, hit⟩ := blocked
  obtain ⟨hf, diff, tags⟩ := everyRep f hr
  apply isPrivate.2 f hf diff
  intro i hi
  have same : w i = base i := by
    by_cases ho : ordinary i
    · apply outside i ho
      intro he
      exact empty ⟨i, he, tags i hi ho⟩
    · exact sameAux i ho
  exact same.trans (hit i hi)

def tally {X : Type} (f : X → Bool) : List X → Nat
  | [] => 0
  | x :: xs => (if f x then 1 else 0) + tally f xs

/-- A finite union bound with an explicit list of witnesses. -/
theorem four_event_cover {X : Type} (xs : List X) (a b c bad : X → Bool)
    (cover : ∀ x, a x = false → b x = false → c x = false → bad x = true) :
    xs.length ≤ tally a xs + tally b xs + tally c xs + tally bad xs := by
  induction xs with
  | nil => simp [tally]
  | cons x xs ih =>
    cases ha : a x <;> cases hb : b x <;> cases hc : c x <;> cases hd : bad x <;>
      simp [tally,ha,hb,hc,hd] <;> first | omega | have hh := cover x ha hb hc; simp [hd] at hh

structure SignedTriple (V : Type) where
  a : V
  b : V
  c : V
  va : Bool
  vb : Bool
  vc : Bool

def badTriple (d : SignedTriple V) (w : Assignment V) : Bool :=
  (w d.a == d.va) && (w d.b == d.vb) && (w d.c == d.vc)

/-- The 216 witnesses of a six by six by six private grid yield a total model
    as soon as each variable differs from its majority at most 69 times. -/
theorem majority_216 (family : SignedTriple V → Prop) (xs : List (Assignment V))
    (majority : Assignment V) (count : xs.length = 216)
    (rare : ∀ i, tally (fun w => w i != majority i) xs ≤ 69)
    (privateGrid : ∀ d, family d → tally (badTriple d) xs ≤ 1) :
    ∀ d, family d → badTriple d majority = false := by
  intro d hd
  cases h : badTriple d majority with
  | false => rfl
  | true =>
    have cover : ∀ w : Assignment V,
        (w d.a != majority d.a) = false → (w d.b != majority d.b) = false →
        (w d.c != majority d.c) = false → badTriple d w = true := by
      intro w ha hb hc
      have a : w d.a = majority d.a := by simpa using ha
      have b : w d.b = majority d.b := by simpa using hb
      have c : w d.c = majority d.c := by simpa using hc
      simpa [badTriple,a,b,c] using h
    have bound := four_event_cover xs _ _ _ _ cover
    have aa := rare d.a
    have bb := rare d.b
    have cc := rare d.c
    have dd := privateGrid d hd
    omega

end PrivateTripleAnchors
