import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/- Semantic transport of a word-valued signal under relabelling of a structure.
   Each clause has at most a fixed number of observed words (a fixed arity also
   permits unused arguments). The predicate on their values can include tests
   for particular values and equalities between words. -/
namespace SupportedWordTransition

variable {Atom Structure Word Witness : Type*} [MulAction (Equiv.Perm Atom) Structure]

/-- A permutation fixing the support pointwise does not change the signal. -/
def Supported (s : Finset Atom) (signal : Structure → Word) : Prop :=
  ∀ g : Equiv.Perm Atom, (∀ a ∈ s, g a = a) → ∀ X, signal (g • X) = signal X

def Agree (s : Finset Atom) (p q : Equiv.Perm Atom) : Prop := ∀ a ∈ s, p a = q a

def transported (signal : Structure → Word) (p : Equiv.Perm Atom) (X : Structure) : Word :=
  signal (p⁻¹ • X)

/-- All completions of the same placement of the support give the same value. -/
theorem agree_transport {s : Finset Atom} {signal : Structure → Word}
    (hs : Supported s signal) {p q : Equiv.Perm Atom} (agree : Agree s p q) (X : Structure) :
    transported signal p X = transported signal q X := by
  have fixes (a : Atom) (ha : a ∈ s) : (p⁻¹ * q) a = a := by
    simp [Equiv.Perm.mul_apply, ← agree a ha]
  simpa [transported, mul_smul] using hs (p⁻¹ * q) fixes (q⁻¹ • X)

/-- A bounded-arity disjunctive transition can be evaluated under any
    permutation agreeing on the output support, provided its one chosen
    conjunct uses a *common* permutation for all observations. -/
theorem transported_dnf {arity : ℕ} (out : Structure → Word) (target : Word)
    (inputs : Witness → Fin arity → Structure → Word)
    (accept : Witness → (Fin arity → Word) → Prop)
    (spec : ∀ X, out X = target ↔ ∃ w, accept w (fun j => inputs w j X))
    (s : Finset Atom) (hs : Supported s out) (p : Equiv.Perm Atom) (X : Structure) :
    transported out p X = target ↔ ∃ w q, Agree s p q ∧
      accept w (fun j => transported (inputs w j) q X) := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := (spec _).mp h
    exact ⟨w, p, fun _ _ => rfl, hw⟩
  · rintro ⟨w, q, hq, hw⟩
    rw [agree_transport hs hq X]
    exact (spec _).mpr ⟨w, hw⟩

/-- Every injective placement of a finite set of atom slots extends to a
    whole-domain permutation, including when the ambient type is infinite. -/
theorem exists_extension {s : Finset Atom} (slots : s ↪ Atom) :
    ∃ q : Equiv.Perm Atom, ∀ a : s, q a = slots a :=
  Equiv.Perm.exists_extending_pair ((↑) : s → Atom) slots Subtype.val_injective slots.injective

noncomputable def extension {s : Finset Atom} (slots : s ↪ Atom) : Equiv.Perm Atom :=
  (exists_extension slots).choose

theorem extension_at {s : Finset Atom} (slots : s ↪ Atom) (a : s) :
    extension slots a = slots a := (exists_extension slots).choose_spec a

def subslots {s t : Finset Atom} (h : s ⊆ t) (slots : t ↪ Atom) : s ↪ Atom where
  toFun a := slots ⟨a.val, h a.prop⟩
  inj' := fun _ _ he => Subtype.ext (congrArg (fun a : t => (a : Atom)) (slots.injective he))

/-- Evaluate an observation from only its own slots. A canonical completion is
    used to define the value; `agree_transport` proves its independence. -/
noncomputable def readSlots {s : Finset Atom} (signal : Structure → Word) (slots : s ↪ Atom)
    (X : Structure) : Word := transported signal (extension slots) X

/-- The joint slots can contain just the union of the output support and the
    supports of the words in the chosen disjunct. The same injected atom is
    used at every occurrence, including when two input supports overlap. -/
theorem injected_dnf {arity : ℕ} (out : Structure → Word) (target : Word)
    (inputs : Witness → Fin arity → Structure → Word)
    (accept : Witness → (Fin arity → Word) → Prop)
    (spec : ∀ X, out X = target ↔ ∃ w, accept w (fun j => inputs w j X))
    (so : Finset Atom) (ho : Supported so out)
    (si : Witness → Fin arity → Finset Atom) (hi : ∀ w j, Supported (si w j) (inputs w j))
    (joint : Witness → Finset Atom) (incOut : ∀ w, so ⊆ joint w)
    (incIn : ∀ w j, si w j ⊆ joint w) (p : Equiv.Perm Atom) (X : Structure) :
    transported out p X = target ↔ ∃ (w : Witness) (slots : joint w ↪ Atom),
      (∀ a : so, slots ⟨a.val, incOut w a.prop⟩ = p a) ∧
      accept w (fun j => readSlots (inputs w j) (subslots (incIn w j) slots) X) := by
  rw [transported_dnf out target inputs accept spec so ho p X]
  constructor
  · rintro ⟨w, q, agrees, hw⟩
    let slots : joint w ↪ Atom := ⟨fun a => q a.val,
      fun _ _ he => Subtype.ext (q.injective he)⟩
    refine ⟨w, slots, fun a => (agrees a a.prop).symm, ?_⟩
    have each (j : Fin arity) : readSlots (inputs w j) (subslots (incIn w j) slots) X =
        transported (inputs w j) q X := by
      apply agree_transport (hi w j)
      intro a ha
      exact extension_at (subslots (incIn w j) slots) ⟨a, ha⟩
    simpa only [each] using hw
  · rintro ⟨w, slots, hout, hw⟩
    let q := extension slots
    have agrees : Agree so p q := by
      intro a ha
      exact (hout ⟨a, ha⟩).symm.trans (extension_at slots ⟨a, incOut w ha⟩).symm
    refine ⟨w, q, agrees, ?_⟩
    have each (j : Fin arity) : readSlots (inputs w j) (subslots (incIn w j) slots) X =
        transported (inputs w j) q X := by
      apply agree_transport (hi w j)
      intro a ha
      exact (extension_at (subslots (incIn w j) slots) ⟨a, ha⟩).trans
        (extension_at slots ⟨a, incIn w j ha⟩).symm
    simpa only [each] using hw

/-- Number of atom slots sufficient for one clause of the transition. -/
theorem joint_support_card [DecidableEq Atom] {arity b : ℕ} (so : Finset Atom)
    (si : Fin arity → Finset Atom) (small : ∀ j, (si j).card ≤ b) :
    (so ∪ Finset.univ.biUnion si).card ≤ so.card + arity * b := by
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add_left
  simpa using Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin arity)) si b
    (fun j _ => small j)

/-- The images of the named atoms label a fixed underlying structure. A winning
    position records only the two partial injections, independent of their
    completions. `forth` and `back` are the usual repeated moves within capacity. -/
structure PartialGame (Atom : Type*) (capacity : ℕ) where
  win : (s : Finset Atom) → (s ↪ Atom) → (s ↪ Atom) → Prop
  forget {s t : Finset Atom} (st : s ⊆ t) (x y : t ↪ Atom) :
    win t x y → win s (subslots st x) (subslots st y)
  forth {s t : Finset Atom} (st : s ⊆ t) (room : t.card ≤ capacity)
      (x : t ↪ Atom) (y : s ↪ Atom) : win s (subslots st x) y →
    ∃ y' : t ↪ Atom, (∀ a : s, y' ⟨a.val, st a.prop⟩ = y a) ∧ win t x y'
  back {s t : Finset Atom} (st : s ⊆ t) (room : t.card ≤ capacity)
      (x : s ↪ Atom) (y : t ↪ Atom) : win s x (subslots st y) →
    ∃ x' : t ↪ Atom, (∀ a : s, x' ⟨a.val, st a.prop⟩ = x a) ∧ win t x' y

def naming (s : Finset Atom) (p : Equiv.Perm Atom) : s ↪ Atom :=
  ⟨fun a => p a.val, fun _ _ h => Subtype.ext (p.injective h)⟩

def PartialGame.aligned {k} (G : PartialGame Atom k) (s : Finset Atom)
    (p q : Equiv.Perm Atom) := G.win s (naming s p) (naming s q)

private theorem naming_extension {s : Finset Atom} (u : s ↪ Atom) :
    naming s (extension u) = u := by ext a; exact extension_at u a

theorem PartialGame.alignForth {k} (G : PartialGame Atom k) {s t : Finset Atom}
    (st : s ⊆ t) (ht : t.card ≤ k) {p q : Equiv.Perm Atom} (hw : G.aligned s p q) :
    ∃ q', Agree s q q' ∧ G.aligned t p q' := by
  obtain ⟨u, agrees, win⟩ := G.forth st ht (naming t p) (naming s q) hw
  refine ⟨extension u, fun a ha => (agrees ⟨a, ha⟩).symm.trans ?_, ?_⟩
  · exact (extension_at u ⟨a, st ha⟩).symm
  · simpa only [aligned, naming_extension] using win

theorem PartialGame.alignBack {k} (G : PartialGame Atom k) {s t : Finset Atom}
    (st : s ⊆ t) (ht : t.card ≤ k) {p q : Equiv.Perm Atom} (hw : G.aligned s p q) :
    ∃ p', Agree s p p' ∧ G.aligned t p' q := by
  obtain ⟨u, agrees, win⟩ := G.back st ht (naming s p) (naming t q) hw
  refine ⟨extension u, fun a ha => (agrees ⟨a, ha⟩).symm.trans ?_, ?_⟩
  · exact (extension_at u ⟨a, st ha⟩).symm
  · simpa only [aligned, naming_extension] using win

def LocallySupports (event : Equiv.Perm Atom → Prop) (p : Equiv.Perm Atom) (s : Finset Atom) :=
  ∀ q, Agree s p q → (event p ↔ event q)

private theorem local_persists {event : Equiv.Perm Atom → Prop} {p q : Equiv.Perm Atom}
    {s : Finset Atom} (h : LocallySupports event p s) (hq : Agree s p q) :
    LocallySupports event q s := fun r hr => (h q hq).symm.trans
      (h r (fun a ha => (hq a ha).trans (hr a ha)))

/-- Transfer one true conjunction. Local supports of the right children are
    chosen only after relabelling the right structure. The second game move
    relabels the left structure, preserving the already chosen true witnesses. -/
theorem local_term_transfer [DecidableEq Atom] {k b h : ℕ} (G : PartialGame Atom k)
    (room : (2 + 2 * b) * h ≤ k) {p q : Equiv.Perm Atom} {sx sy : Finset Atom}
    (hx : sx.card ≤ h) (hy : sy.card ≤ h) (start : G.aligned (sx ∪ sy) p q)
    (parent : Equiv.Perm Atom → Prop) (sparent : LocallySupports parent q sy)
    (x y : Fin b → Equiv.Perm Atom → Prop) (xs : Fin b → Finset Atom)
    (xsmall : ∀ j, (xs j).card ≤ h) (xloc : ∀ j, LocallySupports (x j) p (xs j))
    (ysup : ∀ j q', ∃ s : Finset Atom, s.card ≤ h ∧ LocallySupports (y j) q' s)
    (recur : ∀ j p' q' sl sr, sl.card ≤ h → sr.card ≤ h →
      LocallySupports (x j) p' sl → LocallySupports (y j) q' sr →
      G.aligned (sl ∪ sr) p' q' → x j p' → y j q')
    (term : ∀ q', (∀ j, y j q') → parent q') (trueHere : ∀ j, x j p) : parent q := by
  classical
  let u := sx ∪ sy
  let v := u ∪ Finset.univ.biUnion xs
  have incU : u ⊆ v := Finset.subset_union_left
  have countU : u.card ≤ 2 * h := (Finset.card_union_le sx sy).trans (by omega)
  have countV : v.card ≤ 2 * h + b * h :=
    (joint_support_card u xs xsmall).trans (Nat.add_le_add_right countU _)
  have combined : 2 * h + b * h + b * h ≤ k := by
    simpa [Nat.add_mul, Nat.mul_assoc, Nat.two_mul, Nat.add_assoc] using room
  obtain ⟨q', qAgrees, vWins⟩ := G.alignForth incU (countV.trans (by omega)) start
  choose ys ysmall yloc using fun j => ysup j q'
  let z := v ∪ Finset.univ.biUnion ys
  have incV : v ⊆ z := Finset.subset_union_left
  have countZ : z.card ≤ k := (joint_support_card v ys ysmall).trans
    ((Nat.add_le_add_right countV _).trans combined)
  obtain ⟨p', pAgrees, zWins⟩ := G.alignBack incV countZ vWins
  apply (sparent q' (fun a ha => qAgrees a (Finset.mem_union_right _ ha))).mpr
  apply term
  intro j
  have xsV : xs j ⊆ v := fun a ha => Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩)
  have ysZ : ys j ⊆ z := fun a ha => Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩)
  have fixes : Agree (xs j) p p' := fun a ha => pAgrees a (xsV ha)
  have smallWin : G.aligned (xs j ∪ ys j) p' q' :=
    G.forget (Finset.union_subset (xsV.trans incV) ysZ) (naming z p') (naming z q') zWins
  exact recur j p' q' (xs j) (ys j) (xsmall j) (ysmall j)
    (local_persists (xloc j) fixes) (yloc j) smallWin ((xloc j p' fixes).mp (trueHere j))

/-- The tuple of physical atom coordinates may depend on the actual labeling
    and the true input observation. Only the left labeling remains fixed. -/
private theorem atomic_transfer [DecidableEq Atom] {k h a : ℕ} (G : PartialGame Atom k)
    {p q : Equiv.Perm Atom} {sx sy t : Finset Atom} (hx : sx.card ≤ h) (hy : sy.card ≤ h)
    (ht : t.card ≤ a) (room : 2 * h + a ≤ k) (start : G.aligned (sx ∪ sy) p q)
    (right : Equiv.Perm Atom → Prop) (syLoc : LocallySupports right q sy)
    (atoms : ∀ v, G.aligned t p v → right v) : right q := by
  let s := sx ∪ sy
  let all := s ∪ t
  have sizeS : s.card ≤ 2 * h := (Finset.card_union_le sx sy).trans (by omega)
  have sizeAll : all.card ≤ k := (Finset.card_union_le s t).trans (by omega)
  obtain ⟨q', agrees, win⟩ := G.alignForth (t := all) Finset.subset_union_left sizeAll start
  apply (syLoc q' (fun i hi => agrees i (Finset.mem_union_right _ hi))).mpr
  apply atoms q'
  exact G.forget Finset.subset_union_right (naming all p) (naming all q') win

/-- An acyclic computation whose internal events are disjunctions of
    fixed-arity conjunctions of preceding events. Different numbers of
    alternatives or shorter conjunctions can be modelled by Boolean constants. -/
structure GateSystem (Gate Choice : Type*) (arity : ℕ) where
  rank : Gate → ℕ
  atomic : Gate → Prop
  child : Gate → Choice → Fin arity → Gate
  earlier (g : Gate) (internal : ¬ atomic g) (w : Choice) (j : Fin arity) :
    rank (child g w j) < rank g

structure Evaluation {Gate Choice : Type*} {b : ℕ} (C : GateSystem Gate Choice b) (Atom : Type*) where
  holds : Gate → Equiv.Perm Atom → Prop
  internal (g : Gate) (internal : ¬ C.atomic g) (p : Equiv.Perm Atom) :
    holds g p ↔ ∃ w, ∀ j, holds (C.child g w j) p

private def GivesLocalSupports {Gate Choice : Type*} {b : ℕ} {C : GateSystem Gate Choice b}
    (X : Evaluation C Atom) (h : ℕ) : Prop :=
  ∀ g p, ∃ s, s.card ≤ h ∧ LocallySupports (X.holds g) p s

private theorem acyclic_imp [DecidableEq Atom] {Gate Choice : Type*} {b k h a : ℕ}
    (C : GateSystem Gate Choice b) (G : PartialGame Atom k) (X Y : Evaluation C Atom)
    (xloc : GivesLocalSupports X h) (yloc : GivesLocalSupports Y h)
    (leafRoom : 2 * h + a ≤ k) (nodeRoom : (2 + 2 * b) * h ≤ k)
    (base : ∀ g, C.atomic g → ∀ p, X.holds g p → ∃ t : Finset Atom, t.card ≤ a ∧
      ∀ q, G.aligned t p q → Y.holds g q) :
    ∀ g p q (sx sy : Finset Atom), sx.card ≤ h → sy.card ≤ h →
      LocallySupports (X.holds g) p sx → LocallySupports (Y.holds g) q sy →
      G.aligned (sx ∪ sy) p q → X.holds g p → Y.holds g q := by
  intro g
  induction g using (measure C.rank).wf.induction with
  | h g ih =>
    intro p q sx sy hsx hsy _ syLoc aligned left
    by_cases atomic : C.atomic g
    · obtain ⟨t, ht, atoms⟩ := base g atomic p left
      exact atomic_transfer G hsx hsy ht leafRoom aligned _ syLoc atoms
    · obtain ⟨w, trueTerm⟩ := (X.internal g atomic p).mp left
      choose xs sizes supports using fun j => xloc (C.child g w j) p
      exact local_term_transfer G nodeRoom hsx hsy aligned _ syLoc _ _ xs sizes supports
        (fun j => yloc (C.child g w j))
        (fun j => ih (C.child g w j) (C.earlier g atomic w j))
        (fun q' truths => (Y.internal g atomic q').mpr ⟨w, truths⟩) trueTerm

def PartialGame.flip {k : ℕ} (G : PartialGame Atom k) : PartialGame Atom k where
  win s x y := G.win s y x
  forget st x y := G.forget st y x
  forth st ht x y := G.back st ht y x
  back st ht x y := G.forth st ht y x

/-- The full bounded-witness induction on arbitrary acyclic gates evaluated on
    two reference orbits. A true atom at any labeling on either side supplies
    its own determining tuple; the opposite labeling is quantified afterwards. All other agreement is derived by back-and-forth. -/
theorem local_circuit_agreement [DecidableEq Atom] {Gate Choice : Type*} {b k h a : ℕ}
    (C : GateSystem Gate Choice b) (G : PartialGame Atom k) (X Y : Evaluation C Atom)
    (xloc : ∀ g p, ∃ s, s.card ≤ h ∧ LocallySupports (X.holds g) p s)
    (yloc : ∀ g p, ∃ s, s.card ≤ h ∧ LocallySupports (Y.holds g) p s)
    (leafRoom : 2 * h + a ≤ k) (nodeRoom : (2 + 2 * b) * h ≤ k)
    (baseX : ∀ g, C.atomic g → ∀ p, X.holds g p → ∃ t : Finset Atom, t.card ≤ a ∧
      ∀ q, G.aligned t p q → Y.holds g q)
    (baseY : ∀ g, C.atomic g → ∀ q, Y.holds g q → ∃ t : Finset Atom, t.card ≤ a ∧
      ∀ p, G.aligned t p q → X.holds g p)
    (g : Gate) (p q : Equiv.Perm Atom) (sx sy : Finset Atom) (hsx : sx.card ≤ h)
    (hsy : sy.card ≤ h) (lx : LocallySupports (X.holds g) p sx)
    (ly : LocallySupports (Y.holds g) q sy) (aligned : G.aligned (sx ∪ sy) p q) :
    X.holds g p ↔ Y.holds g q := by
  constructor
  · exact acyclic_imp C G X Y xloc yloc leafRoom nodeRoom baseX g p q sx sy hsx hsy lx ly aligned
  · have reverse : G.flip.aligned (sy ∪ sx) q p := by
      rw [Finset.union_comm sy sx]
      exact aligned
    exact acyclic_imp C G.flip Y X yloc xloc leafRoom nodeRoom baseY g q p sy sx hsy hsx ly lx reverse

/-- An orbitwise constant output distinguishing the two reference structures
    forces a single labeling and a single event there for which every proposed
    support of at most `h` atoms fails. -/
theorem distinguishing_output_forces_local_support [DecidableEq Atom] {Gate Choice : Type*}
    {b k h a : ℕ} (C : GateSystem Gate Choice b) (G : PartialGame Atom k)
    (X Y : Evaluation C Atom) (leafRoom : 2 * h + a ≤ k) (nodeRoom : (2 + 2 * b) * h ≤ k)
    (baseX : ∀ g, C.atomic g → ∀ p, X.holds g p → ∃ t : Finset Atom, t.card ≤ a ∧
      ∀ q, G.aligned t p q → Y.holds g q)
    (baseY : ∀ g, C.atomic g → ∀ q, Y.holds g q → ∃ t : Finset Atom, t.card ≤ a ∧
      ∀ p, G.aligned t p q → X.holds g p)
    (emptyWins : G.aligned ∅ 1 1) (output : Gate)
    (yes : ∀ p, X.holds output p) (no : ∀ q, ¬ Y.holds output q) :
    (∃ g p, ∀ s : Finset Atom, s.card ≤ h → ¬ LocallySupports (X.holds g) p s) ∨
    (∃ g p, ∀ s : Finset Atom, s.card ≤ h → ¬ LocallySupports (Y.holds g) p s) := by
  classical
  by_contra neither
  have xloc : GivesLocalSupports X h := by
    intro g p
    by_contra fail
    exact neither (.inl ⟨g, p, fun s hs hp => fail ⟨s, hs, hp⟩⟩)
  have yloc : GivesLocalSupports Y h := by
    intro g p
    by_contra fail
    exact neither (.inr ⟨g, p, fun s hs hp => fail ⟨s, hs, hp⟩⟩)
  have l : LocallySupports (X.holds output) 1 ∅ := fun q _ => iff_of_true (yes _) (yes q)
  have r : LocallySupports (Y.holds output) 1 ∅ := fun q _ => iff_of_false (no _) (no q)
  have agree := local_circuit_agreement C G X Y xloc yloc leafRoom nodeRoom baseX baseY output 1 1
    ∅ ∅ (by simp) (by simp) l r (by simpa only [Finset.empty_union] using emptyWins)
  exact no 1 (agree.mp (yes 1))

#print axioms distinguishing_output_forces_local_support
#print axioms local_circuit_agreement
#print axioms local_term_transfer
#print axioms transported_dnf
#print axioms injected_dnf
#print axioms joint_support_card

end SupportedWordTransition
