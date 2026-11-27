import Std

namespace EpochDictionary

/-- One addressed block per tape. Metadata may include the finite control,
    offsets and directions in the chronological record. -/
structure Epoch (Tape Addr Value Meta : Type) where
  address : Tape → Addr
  before : Tape → Value
  after : Tape → Value
  meta : Meta

def decode (word : Name → Value) (r : Epoch Tape Addr Name Meta) :
    Epoch Tape Addr Value Meta :=
  ⟨r.address, fun i => word (r.before i), fun i => word (r.after i), r.meta⟩

def store [DecidableEq Addr] (mem : Tape → Addr → Value)
    (r : Epoch Tape Addr Value Meta) : Tape → Addr → Value :=
  fun i a => if a = r.address i then r.after i else mem i a

def consistent [DecidableEq Addr] (valid : Epoch Tape Addr Value Meta → Prop)
    (mem : Tape → Addr → Value) : List (Epoch Tape Addr Value Meta) → Prop
  | [] => True
  | r :: rest =>
      valid r ∧ (∀ i, mem i (r.address i) = r.before i) ∧
      consistent valid (store mem r) rest

/-- Coherent repeated names transport a whole trace to decoded blocks even
    with aliases. The semantic local predicate may hide an existential witness. -/
theorem realize [DecidableEq Addr] (word : Name → Value)
    (allowed : Epoch Tape Addr Name Meta → Prop)
    (semantic : Epoch Tape Addr Value Meta → Prop)
    (localSound : ∀ r, allowed r → semantic (decode word r))
    (trace : List (Epoch Tape Addr Name Meta)) (mem : Tape → Addr → Name)
    (h : consistent allowed mem trace) :
    consistent semantic (fun i a => word (mem i a)) (trace.map (decode word)) := by
  induction trace generalizing mem with
  | nil => trivial
  | cons r rest ih =>
    obtain ⟨ok, linked, tail⟩ := h
    refine ⟨localSound r ok, fun i => congrArg word (linked i), ?_⟩
    have agree : store (fun i a => word (mem i a)) (decode word r) =
        fun i a => word (store mem r i a) := by
      funext i a
      by_cases eq : a = r.address i <;> simp [store, decode, eq]
    rw [agree]
    exact ih (store mem r) tail

def concretize (r : Epoch Tape Addr Name Meta) (inputs outputs : Tape → Value) :
    Epoch Tape Addr Value Meta := ⟨r.address, inputs, outputs, r.meta⟩

/-- At each step the concrete input is the actual current block. The
    existential output is stored for later visits at the same address. -/
def canFollow [DecidableEq Addr] (semantic : Epoch Tape Addr Value Meta → Prop)
    (mem : Tape → Addr → Value) : List (Epoch Tape Addr Name Meta) → Prop
  | [] => True
  | r :: rest => ∃ out : Tape → Value,
      let step := concretize r (fun i => mem i (r.address i)) out
      semantic step ∧ canFollow semantic (store mem step) rest

theorem realize_regions [DecidableEq Addr] (region : Name → Value → Prop)
    (allowed : Epoch Tape Addr Name Meta → Prop)
    (semantic : Epoch Tape Addr Value Meta → Prop)
    (localLift : ∀ r, allowed r → ∀ inputs : Tape → Value,
      (∀ i, region (r.before i) (inputs i)) →
      ∃ out : Tape → Value, semantic (concretize r inputs out) ∧
        ∀ i, region (r.after i) (out i))
    (trace : List (Epoch Tape Addr Name Meta))
    (names : Tape → Addr → Name) (mem : Tape → Addr → Value)
    (h : consistent allowed names trace)
    (fits : ∀ i a, region (names i a) (mem i a)) :
    canFollow semantic mem trace := by
  induction trace generalizing names mem with
  | nil => trivial
  | cons r rest ih =>
    obtain ⟨ok, linked, tail⟩ := h
    have localFit (i : _) : region (r.before i) (mem i (r.address i)) := by
      rw [← linked i]
      exact fits i (r.address i)
    obtain ⟨out, sem, outputFit⟩ :=
      localLift r ok (fun i => mem i (r.address i)) localFit
    refine ⟨out, sem, ih (store names r) _ tail ?_⟩
    intro i a
    by_cases eq : a = r.address i
    · simpa [store, concretize, eq] using outputFit i
    · simpa [store, concretize, eq] using fits i a

/-- Independent nonempty regions certified inside an equality test must
    each be the same singleton. -/
theorem equality_regions {P Q : α → Prop} {a b : α}
    (ha : P a) (hb : Q b) (diagonal : ∀ x y, P x → Q y → x = y) :
    a = b ∧ (∀ x, P x → x = a) ∧ (∀ y, Q y → y = a) := by
  have eq := diagonal a b ha hb
  exact ⟨eq, fun x hx => (diagonal x b hx hb).trans eq.symm,
    fun y hy => (diagonal a y ha hy).symm⟩

/-- Any omitted literal can be flipped inside its named region. -/
theorem free_literal {ι : Type} [DecidableEq ι] (pattern : ι → Option Bool)
    (word : ι → Bool) (i : ι) (free : pattern i = none)
    (fits : ∀ j b, pattern j = some b → word j = b) :
    ∃ other : ι → Bool, other ≠ word ∧ ∀ j b, pattern j = some b → other j = b := by
  let other := fun j => if j = i then !(word i) else word j
  refine ⟨other, ?_, ?_⟩
  · intro eq
    have bad := congrFun eq i
    cases h : word i <;> simp [other, h] at bad
  · intro j b pin
    by_cases eq : j = i
    · subst j
      simp [free] at pin
    · simpa [other, eq] using fits j b pin

end EpochDictionary
