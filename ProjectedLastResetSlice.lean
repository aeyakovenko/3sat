import Std

namespace ProjectedLastResetSlice

/-- Ternary addition on an affine binary space. Only the cancellation law below
    is needed in the projection argument. -/
structure Space (X : Type) where
  add : X → X → X → X
  cancel : ∀ a x, add a a x = x

def B : Space Bool where
  add a b c := (a ^^ b) ^^ c
  cancel := by intro a x; cases a <;> cases x <;> rfl

def Flat (X : Space α) (S : α → Prop) : Prop :=
  ∀ a b c, S a → S b → S c → S (X.add a b c)

def AffOn (X : Space α) (Y : Space β) (S : α → Prop) (f : α → β) : Prop :=
  ∀ a b c, S a → S b → S c → f (X.add a b c) = Y.add (f a) (f b) (f c)

def Image (p : α → β) (S : α → Prop) (x : β) : Prop :=
  ∃ a, S a ∧ p a = x

private theorem flip_value (a b c k : Bool) : a ≠ b → c ≠ k → B.add a b c = k := by
  cases a <;> cases b <;> cases c <;> cases k <;> decide

private theorem affine_const (X : Space α) (S : α → Prop) (b : Bool) :
    AffOn X B S (fun _ => b) := by
  intro a c d _ _ _
  exact (B.cancel b b).symm

private theorem affine_not {X : Space α} {S : α → Prop} {f : α → Bool}
    (hf : AffOn X B S f) : AffOn X B S (fun a => !(f a)) := by
  intro a b c ha hb hc
  simp only [hf a b c ha hb hc]
  cases f a <;> cases f b <;> cases f c <;> rfl

theorem flat_cut {X : Space α} {S : α → Prop} (hs : Flat X S) {f : α → Bool}
    (hf : AffOn X B S f) (value : Bool) : Flat X (fun a => S a ∧ f a = value) := by
  rintro a b c ⟨ha, ea⟩ ⟨hb, eb⟩ ⟨hc, ec⟩
  refine ⟨hs a b c ha hb hc, ?_⟩
  rw [hf a b c ha hb hc, ea, eb, ec, B.cancel]

private theorem aff_mono {X : Space α} {Y : Space β} {S T : α → Prop} {f : α → β}
    (hf : AffOn X Y S f) (h : ∀ a, T a → S a) : AffOn X Y T f :=
  fun a b c ha hb hc => hf a b c (h a ha) (h b hb) (h c hc)

theorem flat_image {X : Space α} {Y : Space β} {S : α → Prop} {p : α → β}
    (hs : Flat X S) (hp : AffOn X Y S p) : Flat Y (Image p S) := by
  rintro _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
  exact ⟨X.add a b c, hs _ _ _ ha hb hc, hp _ _ _ ha hb hc⟩

/-- Either both values of the guard occur in every public fiber, or the
    guard descends to a public form affine on V. The conclusion includes
    an arbitrary total extension as a function, affine only on V. -/
theorem split_fibers {X : Space α} {Y : Space β} {S : α → Prop} {V : β → Prop}
    {p : α → β} {g : α → Bool} (hs : Flat X S) (hp : AffOn X Y S p)
    (hg : AffOn X B S g) (onto : ∀ x, Image p S x ↔ V x) :
    (∀ x, V x → ∀ k : Bool, Image p (fun a => S a ∧ g a = k) x) ∨
    (∃ f : β → Bool, AffOn Y B V f ∧ ∀ a, S a → g a = f (p a)) := by
  classical
  by_cases vary : ∃ a b, S a ∧ S b ∧ p a = p b ∧ g a ≠ g b
  · left
    obtain ⟨a,b,ha,hb,ep,eg⟩ := vary
    intro x hx k
    obtain ⟨c,hc,rfl⟩ := (onto x).mpr hx
    by_cases eq : g c = k
    · exact ⟨c, ⟨hc,eq⟩, rfl⟩
    · refine ⟨X.add a b c, ⟨hs _ _ _ ha hb hc, ?_⟩, ?_⟩
      · rw [hg _ _ _ ha hb hc]
        exact flip_value _ _ _ _ eg eq
      · rw [hp _ _ _ ha hb hc, ep, Y.cancel]
  · right
    have unique (a b : α) (ha : S a) (hb : S b) (eq : p a = p b) : g a = g b := by
      by_cases he : g a = g b
      · exact he
      · exact False.elim (vary ⟨a,b,ha,hb,eq,he⟩)
    let f := fun x => if hx : Image p S x then g hx.choose else false
    have desc (a : α) (ha : S a) : g a = f (p a) := by
      have hz : Image p S (p a) := ⟨a,ha,rfl⟩
      simp only [f, dif_pos hz]
      exact unique _ _ ha hz.choose_spec.1 hz.choose_spec.2.symm
    refine ⟨f, ?_, desc⟩
    intro a b c ha hb hc
    obtain ⟨u,hu,rfl⟩ := (onto a).mpr ha
    obtain ⟨v,hv,rfl⟩ := (onto b).mpr hb
    obtain ⟨w,hw,rfl⟩ := (onto c).mpr hc
    rw [← hp _ _ _ hu hv hw, ← desc _ (hs _ _ _ hu hv hw), ← desc _ hu,
      ← desc _ hv, ← desc _ hw, hg _ _ _ hu hv hw]

/-- The existentially projected truth of one affine leaf is an affine public bit
    on the active domain: a varying vertical bit produces constant true. -/
theorem project_leaf {X : Space α} {Y : Space β} {S : α → Prop} {V : β → Prop}
    {p : α → β} {h : α → Bool} (hs : Flat X S) (hp : AffOn X Y S p)
    (hh : AffOn X B S h) (onto : ∀ x, Image p S x ↔ V x) :
    ∃ f : β → Bool, AffOn Y B V f ∧
      ∀ x, V x → (Image p (fun a => S a ∧ h a = true) x ↔ f x = true) := by
  rcases split_fibers hs hp hh onto with both | ⟨f,hf,desc⟩
  · exact ⟨fun _ => true, affine_const _ _ _, fun x hx => ⟨fun _ => rfl, fun _ => both x hx true⟩⟩
  · refine ⟨f, hf, ?_⟩
    intro x hx
    constructor
    · rintro ⟨a,⟨ha,he⟩,rfl⟩
      rw [← desc a ha, he]
    · intro he
      obtain ⟨a,ha,rfl⟩ := (onto x).mpr hx
      exact ⟨a, ⟨ha, (desc _ ha).trans he⟩, rfl⟩


/-- The guard falls through on true and returns the leaf bit on false. -/
inductive Program (α : Type) where
  | leaf (answer : α → Bool)
  | test (guard answer : α → Bool) (later : Program α)

def Accept : Program α → α → Prop
  | .leaf h, a => h a = true
  | .test g h tail, a =>
    (g a = false ∧ h a = true) ∨ (g a = true ∧ Accept tail a)

def tests : Program α → Nat
  | .leaf _ => 0
  | .test _ _ later => tests later + 1

/-- A public form need only be affine on the current flat. A branch leaf
    is needed only where its guard returns false. -/
def ValidOn (X : Space α) (S : α → Prop) : Program α → Prop
  | .leaf h => AffOn X B S h
  | .test g h later => AffOn X B S g ∧
      AffOn X B (fun a => S a ∧ g a = false) h ∧
      ValidOn X (fun a => S a ∧ g a = true) later

private theorem valid_mono {X : Space α} (l : Program α) {S T : α → Prop}
    (valid : ValidOn X S l) (sub : ∀ a, T a → S a) : ValidOn X T l := by
  induction l generalizing S T with
  | leaf h => exact aff_mono valid sub
  | test g h rest ih =>
    exact ⟨aff_mono valid.1 sub, aff_mono valid.2.1 (fun a ha => ⟨sub _ ha.1, ha.2⟩),
      ih valid.2.2 (fun a ha => ⟨sub _ ha.1, ha.2⟩)⟩

private theorem image_desc {S : α → Prop} {V : β → Prop} {p : α → β}
    {g : α → Bool} {f : β → Bool} (onto : ∀ x, Image p S x ↔ V x)
    (desc : ∀ a, S a → g a = f (p a)) (k : Bool) (x : β) :
    Image p (fun a => S a ∧ g a = k) x ↔ V x ∧ f x = k := by
  constructor
  · rintro ⟨a,⟨ha,he⟩,rfl⟩
    exact ⟨(onto _).mp ⟨a,ha,rfl⟩, (desc a ha).symm.trans he⟩
  · rintro ⟨hx,he⟩
    obtain ⟨a,ha,rfl⟩ := (onto _).mpr hx
    exact ⟨a,⟨ha,(desc a ha).trans he⟩,rfl⟩

private theorem pull_aff {X : Space α} {Y : Space β} {V : β → Prop} {S : α → Prop}
    {p : α → β} (hp : AffOn X Y S p) (within : ∀ a, S a → V (p a))
    {f : β → Bool} (hf : AffOn Y B V f) : AffOn X B S (fun a => f (p a)) := by
  intro a b c ha hb hc
  change f (p (X.add a b c)) = B.add (f (p a)) (f (p b)) (f (p c))
  rw [hp _ _ _ ha hb hc, hf _ _ _ (within _ ha) (within _ hb) (within _ hc)]

/-- Existential elimination for an entire affine decision list, with at most one
    output guard per input guard (including constant, dispensable guards).
    In an ordinary finite-dimensional binary space each relative affine form
    extends to the full public space by extending a basis. This theorem states
    the relative form directly. -/
theorem project_list {X : Space α} {Y : Space β} (l : Program α)
    {S : α → Prop} {V : β → Prop} {p : α → β}
    (hs : Flat X S) (hp : AffOn X Y S p) (onto : ∀ x, Image p S x ↔ V x)
    (valid : ValidOn X S l) :
    ∃ out : Program β, tests out = tests l ∧ ValidOn Y V out ∧
      ∀ x, V x → (Image p (fun a => S a ∧ Accept l a) x ↔ Accept out x) := by
  induction l generalizing S V with
  | leaf h =>
    obtain ⟨f,hf,equiv⟩ := project_leaf hs hp valid onto
    exact ⟨.leaf f, rfl, hf, equiv⟩
  | test g h tail ih =>
    let T := fun a => S a ∧ g a = false
    let U := fun a => S a ∧ g a = true
    have ht : Flat X T := flat_cut hs valid.1 false
    have hu : Flat X U := flat_cut hs valid.1 true
    have pt : AffOn X Y T p := aff_mono hp (fun _ ha => ha.1)
    have pu : AffOn X Y U p := aff_mono hp (fun _ ha => ha.1)
    rcases split_fibers hs hp valid.1 onto with both | ⟨f,hf,desc⟩
    · have same (b : Bool) (x : β) :
          Image p (fun a => S a ∧ g a = b) x ↔ V x := by
        constructor
        · rintro ⟨a,⟨ha,_⟩,rfl⟩
          exact (onto _).mp ⟨a,ha,rfl⟩
        · intro hx
          exact both x hx b
      obtain ⟨early,hearly,early_spec⟩ := project_leaf ht pt valid.2.1 (same false)
      let f := fun x => !(early x)
      have hf : AffOn Y B V f := affine_not hearly
      have inc : ∀ a, U a → V (p a) := fun a ha => (same true _).mp ⟨a, ha, rfl⟩
      let U' := fun a => U a ∧ f (p a) = true
      have hu' : Flat X U' := flat_cut hu (pull_aff pu inc hf) true
      have pu' : AffOn X Y U' p := aff_mono pu (fun _ ha => ha.1)
      have onto' : ∀ x, Image p U' x ↔ V x ∧ f x = true :=
        image_desc (same true) (fun _ _ => rfl) true
      obtain ⟨rest,hlen,hvalid,heq⟩ :=
        ih hu' pu' onto' (valid_mono tail valid.2.2 (fun _ ha => ha.1))
      refine ⟨.test f (fun _ => true) rest, congrArg (fun n => n+1) hlen,
        ⟨hf, affine_const _ _ _, hvalid⟩, ?_⟩
      intro x hx
      cases ee : early x with
      | true =>
        have hfx : f x = false := by simp [f,ee]
        have accepted : Image p (fun a => S a ∧ Accept (.test g h tail) a) x := by
          obtain ⟨a,⟨⟨ha,eg⟩,eh⟩,e⟩ := (early_spec x hx).mpr ee
          exact ⟨a,⟨ha,Or.inl ⟨eg,eh⟩⟩,e⟩
        exact ⟨fun _ => Or.inl ⟨hfx,rfl⟩, fun _ => accepted⟩
      | false =>
        have hfx : f x = true := by simp [f,ee]
        change _ ↔ (f x = false ∧ true = true) ∨ (f x = true ∧ Accept rest x)
        simp only [hfx, Bool.true_eq_false, false_and, true_and, false_or, eq_self]
        rw [← heq x ⟨hx,hfx⟩]
        constructor
        · rintro ⟨a,⟨ha,acc⟩,rfl⟩
          rcases acc with ⟨eg,eh⟩ | ⟨eg,ea⟩
          · have no := (early_spec _ hx).mp ⟨a,⟨⟨ha,eg⟩,eh⟩,rfl⟩
            rw [ee] at no
            contradiction
          · exact ⟨a,⟨⟨⟨ha,eg⟩,hfx⟩,ea⟩,rfl⟩
        · rintro ⟨a,⟨⟨⟨ha,eg⟩,_⟩,ea⟩,e⟩
          exact ⟨a,⟨ha,Or.inr ⟨eg,ea⟩⟩,e⟩
    · obtain ⟨hit,hhit,ehit⟩ := project_leaf ht pt valid.2.1 (image_desc onto desc false)
      obtain ⟨rest,hlen,hvalid,heq⟩ := ih hu pu (image_desc onto desc true) valid.2.2
      refine ⟨.test f hit rest, congrArg (fun n => n+1) hlen, ⟨hf,hhit,hvalid⟩, ?_⟩
      intro x hx
      constructor
      · rintro ⟨a,⟨ha,acc⟩,rfl⟩
        rcases acc with ⟨eg,eh⟩ | ⟨eg,ea⟩
        · have ef := (desc _ ha).symm.trans eg
          exact Or.inl ⟨ef, (ehit _ ⟨hx,ef⟩).mp ⟨a,⟨⟨ha,eg⟩,eh⟩,rfl⟩⟩
        · have ef := (desc _ ha).symm.trans eg
          exact Or.inr ⟨ef, (heq _ ⟨hx,ef⟩).mp ⟨a,⟨⟨ha,eg⟩,ea⟩,rfl⟩⟩
      · rintro (⟨eg,eh⟩ | ⟨eg,ea⟩)
        · obtain ⟨a,⟨⟨ha,ef⟩,eh'⟩,e⟩ := (ehit x ⟨hx,eg⟩).mpr eh
          exact ⟨a,⟨ha,Or.inl ⟨ef,eh'⟩⟩,e⟩
        · obtain ⟨a,⟨⟨ha,ef⟩,ea'⟩,e⟩ := (heq x ⟨hx,eg⟩).mpr ea
          exact ⟨a,⟨ha,Or.inr ⟨ef,ea'⟩⟩,e⟩


structure Row (α : Type) where
  low : α → Bool
  high : α → Bool

/-- The head is the last executed row. Its transition always has two defined
    destinations, one for each prior state, on the same fixed valuation. -/
def execute : List (Row α) → (α → Bool) → α → Bool
  | [], initial, x => initial x
  | r :: rs, initial, x => if execute rs initial x then r.high x else r.low x

/-- On a permutation row, low is the toggle. On a reset row, low is the
    forced state. The accumulated affine suffix phase is added in both cases. -/
def compile (initial : α → Bool) : List (Row α) → (α → Bool) → Program α
  | [], phase => .leaf (fun x => initial x ^^ phase x)
  | r :: rs, phase =>
    let nextPhase := fun x => r.low x ^^ phase x
    .test (fun x => r.low x ^^ r.high x) nextPhase (compile initial rs nextPhase)

private theorem next_equiv (lo hi prev ph : Bool) :
    (((lo ^^ hi) = false ∧ (lo ^^ ph) = true) ∨
      ((lo ^^ hi) = true ∧ (prev ^^ (lo ^^ ph)) = true)) ↔
    (((if prev then hi else lo) ^^ ph) = true) := by
  cases lo <;> cases hi <;> cases prev <;> cases ph <;> decide

theorem compile_correct (rs : List (Row α)) (initial phase : α → Bool) (x : α) :
    Accept (compile initial rs phase) x ↔ (execute rs initial x ^^ phase x) = true := by
  induction rs generalizing phase with
  | nil => rfl
  | cons r rs ih =>
    simp only [compile, Accept, execute, ih]
    exact next_equiv _ _ _ _

private theorem xor_aff {X : Space α} {S : α → Prop} {f g : α → Bool}
    (hf : AffOn X B S f) (hg : AffOn X B S g) : AffOn X B S (fun x => f x ^^ g x) := by
  intro a b c ha hb hc
  change (f (X.add a b c) ^^ g (X.add a b c)) = B.add (f a ^^ g a) (f b ^^ g b) (f c ^^ g c)
  rw [hf _ _ _ ha hb hc, hg _ _ _ ha hb hc]
  cases f a <;> cases f b <;> cases f c <;> cases g a <;> cases g b <;> cases g c <;> rfl

theorem compile_valid {X : Space α} {S : α → Prop} (rs : List (Row α))
    {initial phase : α → Bool} (hi : AffOn X B S initial) (hf : AffOn X B S phase)
    (forms : ∀ r ∈ rs, AffOn X B S r.low ∧ AffOn X B S r.high) :
    ValidOn X S (compile initial rs phase) := by
  induction rs generalizing phase with
  | nil => exact xor_aff hi hf
  | cons r rs ih =>
    obtain ⟨lo,high⟩ := forms r (by simp)
    have next := xor_aff lo hf
    exact ⟨xor_aff lo high, aff_mono next (fun _ h => h.1),
      valid_mono _ (ih next (fun s hs => forms s (List.mem_cons_of_mem _ hs))) (fun _ h => h.1)⟩

theorem compile_length (rs : List (Row α)) (initial phase : α → Bool) :
    tests (compile initial rs phase) = rs.length := by
  induction rs generalizing phase with
  | nil => rfl
  | cons r rs ih => simp [compile, tests, ih]


/-- Four public bits, grouped in two binary clauses. -/
def Cube4 : Space (BitVec 4) where
  add a b c := (a ^^^ b) ^^^ c
  cancel := by simp

def twoClauses (x : BitVec 4) : Bool := (x &&& 3 != 0) && (x &&& 12 != 0)

private def form (z a b c d : Bool) (x : BitVec 4) : Bool :=
  B.add (if x.getLsbD 0 then a else z) z
    (B.add (if x.getLsbD 1 then b else z) z
      (B.add (if x.getLsbD 2 then c else z) z (if x.getLsbD 3 then d else z)))

private theorem form_rep (f : BitVec 4 → Bool) (hf : AffOn Cube4 B (fun _ => True) f) (x : BitVec 4) :
    f x = form (f 0) (f 1) (f 2) (f 4) (f 8) x := by
  have add (a b : BitVec 4) : f (a ^^^ b) = B.add (f a) (f 0) (f b) := by
    simpa [Cube4] using hf a 0 b trivial trivial trivial
  have exp : x = (if x.getLsbD 0 then 1 else 0) ^^^
      ((if x.getLsbD 1 then 2 else 0) ^^^
      ((if x.getLsbD 2 then 4 else 0) ^^^ (if x.getLsbD 3 then 8 else 0))) := by
    revert x
    decide
  calc
    f x = f _ := congrArg f exp
    _ = _ := by
      rw [add, add, add]
      simp only [form, apply_ite f]

/-- One ternary-addition counterexample for each nonempty false fiber.
    Index bits give the values of the public guard at zero and the four
    coordinate unit vectors. The last index has an empty false fiber. -/
private def badTriple (z a b c d : Bool) : BitVec 4 × BitVec 4 × BitVec 4 :=
  match z.toNat + 2*a.toNat + 4*b.toNat + 8*c.toNat + 16*d.toNat with
  | 0 => ⟨0,1,4⟩
  | 1 => ⟨1,2,4⟩
  | 2 => ⟨0,2,4⟩
  | 3 => ⟨2,3,4⟩
  | 4 => ⟨0,1,4⟩
  | 5 => ⟨1,3,4⟩
  | 6 => ⟨0,3,4⟩
  | 7 => ⟨4,5,6⟩
  | 8 => ⟨0,1,8⟩
  | 9 => ⟨1,2,8⟩
  | 10 => ⟨0,2,8⟩
  | 11 => ⟨2,3,8⟩
  | 12 => ⟨0,1,8⟩
  | 13 => ⟨1,3,8⟩
  | 14 => ⟨0,3,8⟩
  | 15 => ⟨8,9,10⟩
  | 16 => ⟨0,1,4⟩
  | 17 => ⟨1,2,4⟩
  | 18 => ⟨0,2,4⟩
  | 19 => ⟨2,3,4⟩
  | 20 => ⟨0,1,4⟩
  | 21 => ⟨1,3,4⟩
  | 22 => ⟨0,3,4⟩
  | 23 => ⟨4,5,6⟩
  | 24 => ⟨0,1,12⟩
  | 25 => ⟨1,5,9⟩
  | 26 => ⟨0,2,12⟩
  | 27 => ⟨2,6,10⟩
  | 28 => ⟨0,1,12⟩
  | 29 => ⟨1,5,9⟩
  | 30 => ⟨0,3,12⟩
  | _ => ⟨0,0,0⟩

private theorem checked_triples :
    ∀ z a b c d : Bool, (∀ x : BitVec 4, form z a b c d x = true) ∨
      let t := badTriple z a b c d
      form z a b c d t.1 = false ∧ form z a b c d t.2.1 = false ∧
        form z a b c d t.2.2 = false ∧ twoClauses (Cube4.add t.1 t.2.1 t.2.2) ≠
          B.add (twoClauses t.1) (twoClauses t.2.1) (twoClauses t.2.2) := by decide

private theorem four_bit_certificate (z a b c d : Bool)
    (h : ∃ x : BitVec 4, form z a b c d x = false) :
    ∃ x y w : BitVec 4, form z a b c d x = false ∧ form z a b c d y = false ∧
        form z a b c d w = false ∧ twoClauses (Cube4.add x y w) ≠
          B.add (twoClauses x) (twoClauses y) (twoClauses w) := by
  rcases checked_triples z a b c d with empty | cert
  · obtain ⟨x,hx⟩ := h
    have := empty x
    simp_all
  · let t := badTriple z a b c d
    exact ⟨t.1,t.2.1,t.2.2,cert⟩

theorem no_affine_slice (f : BitVec 4 → Bool) (hf : AffOn Cube4 B (fun _ => True) f)
    (nonempty : ∃ x, f x = false) : ¬ AffOn Cube4 B (fun x => f x = false) twoClauses := by
  intro affine
  obtain ⟨x,hx⟩ := nonempty
  have lift := (form_rep f hf x).symm.trans hx
  obtain ⟨u,v,w,hu,hv,hw,bad⟩ :=
    four_bit_certificate (f 0) (f 1) (f 2) (f 4) (f 8) ⟨x,lift⟩
  exact bad (affine u v w ((form_rep f hf u).trans hu) ((form_rep f hf v).trans hv)
    ((form_rep f hf w).trans hw))


private theorem affine_congr {X : Space α} {S : α → Prop} {f g : α → Bool}
    (hs : Flat X S) (hf : AffOn X B S f) (eq : ∀ a, S a → f a = g a) : AffOn X B S g := by
  intro a b c ha hb hc
  rw [← eq _ (hs _ _ _ ha hb hc), ← eq _ ha, ← eq _ hb, ← eq _ hc, hf _ _ _ ha hb hc]

/-- No public affine decision list, of any length, recognizes the conjunction
    of the two binary clauses. Constant guard tests may precede the first real
    test. The argument rejects them or removes them by induction. -/
theorem two_clauses_not_a_list (l : Program (BitVec 4)) (hl : ValidOn Cube4 (fun _ => True) l) :
    ¬ ∀ x, Accept l x ↔ twoClauses x = true := by
  induction l with
  | leaf h =>
    intro eq
    apply no_affine_slice (fun _ => false) (affine_const _ _ _) ⟨0,rfl⟩
    apply affine_congr (fun _ _ _ _ _ _ => rfl) (aff_mono hl (fun _ _ => trivial))
    exact fun x _ => Bool.eq_iff_iff.mpr (eq x)
  | test g h later ih =>
    intro eq
    by_cases nonempty : ∃ x, g x = false
    · apply no_affine_slice g hl.1 nonempty
      have flat : Flat Cube4 (fun x => g x = false) := by
        intro a b c ha hb hc
        rw [hl.1 _ _ _ trivial trivial trivial, ha,hb,hc,B.cancel]
      apply affine_congr flat (aff_mono hl.2.1 (fun _ hx => ⟨trivial,hx⟩))
      intro x hx
      apply Bool.eq_iff_iff.mpr
      simpa [Accept,hx] using eq x
    · have always (x) : g x = true := by
        cases he : g x
        · exact False.elim (nonempty ⟨x,he⟩)
        · rfl
      apply ih (valid_mono _ hl.2.2 (fun x _ => ⟨trivial,always x⟩))
      intro x
      simpa [Accept,always x] using eq x

/-- Fully projected reader separation. The hidden space and number of rows are
    arbitrary. A row's two state-dependent next bits must be affine functions
    on the lift flat. The initial state and final output flip may also be affine. -/
theorem two_clauses_not_a_projected_reader {X : Space α} {S : α → Prop} {p : α → BitVec 4}
    (hs : Flat X S) (hp : AffOn X Cube4 S p) (onto : ∀ x, Image p S x)
    (rs : List (Row α)) {initial phase : α → Bool} (hi : AffOn X B S initial)
    (hf : AffOn X B S phase) (forms : ∀ r ∈ rs, AffOn X B S r.low ∧ AffOn X B S r.high) :
    ¬ ∀ x, Image p (fun a => S a ∧ (execute rs initial a ^^ phase a) = true) x ↔
      twoClauses x = true := by
  intro decides
  obtain ⟨out,_,valid,equiv⟩ := project_list (compile initial rs phase) hs hp
    (V := fun _ => True) (fun x => ⟨fun _ => trivial, fun _ => onto x⟩) (compile_valid rs hi hf forms)
  apply two_clauses_not_a_list out valid
  intro x
  rw [← equiv x trivial, ← decides x]
  constructor
  · rintro ⟨a,⟨ha,hy⟩,e⟩
    exact ⟨a,⟨ha,(compile_correct _ _ _ _).mp hy⟩,e⟩
  · rintro ⟨a,⟨ha,hy⟩,e⟩
    exact ⟨a,⟨ha,(compile_correct _ _ _ _).mpr hy⟩,e⟩

end ProjectedLastResetSlice
