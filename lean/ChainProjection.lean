import Std

namespace ChainProjection

abbrev Edge := Bool × Bool
abbrev Relation := Bool → Bool → Prop

/-- The signed clause whose only forbidden endpoint assignment is e. -/
def clause (e : Edge) (x y : Bool) : Prop := ¬ (x = e.1 ∧ y = e.2)

def full : Relation := fun _ _ => True

def compose (R S : Relation) (x z : Bool) : Prop := ∃ y, R x y ∧ S y z

theorem twoClauses (e f : Edge) :
    compose (clause e) (clause f) =
      if e.2 = f.1 then full else clause (e.1, f.2) := by
  obtain ⟨a,b⟩ := e
  obtain ⟨c,d⟩ := f
  funext x z
  apply propext
  cases b <;> cases c <;> by_cases h : x = a <;> simp [compose, clause, full, Bool.exists_bool, h]

theorem composeFull (e : Edge) : compose (clause e) full = full := by
  funext x z
  apply propext
  exact ⟨fun _ => trivial, fun _ => ⟨!e.2, by simp [clause], trivial⟩⟩

/-- Every internal vertex is independently existentially quantified. -/
def project (e : Edge) : List Edge → Relation
  | [] => clause e
  | f :: fs => compose (clause e) (project f fs)

def hasBreak (e : Edge) : List Edge → Bool
  | [] => false
  | f :: fs => (e.2 == f.1) || hasBreak f fs

def lastRight (e : Edge) : List Edge → Bool
  | [] => e.2
  | f :: fs => lastRight f fs

/-- A nonempty path eliminates to one clause, unless an internal variable
    has the same forbidden bit in both adjacent clauses. -/
theorem pathProjection (e : Edge) (es : List Edge) :
    project e es = if hasBreak e es then full else clause (e.1, lastRight e es) := by
  induction es generalizing e with
  | nil => simp [project, hasBreak, lastRight]
  | cons f fs ih =>
    simp only [project, ih f]
    cases h : hasBreak f fs with
    | true => simp [hasBreak, h, composeFull]
    | false =>
      by_cases join : e.2 = f.1 <;> simp [hasBreak, lastRight, h, twoClauses, join]

theorem breakRemovesConstraint (e : Edge) (es : List Edge) (h : hasBreak e es = true) :
    ∀ x z, project e es x z := by
  rw [pathProjection, h]
  exact fun _ _ => trivial

theorem breakAfterPrefix (start left right : Edge) (before after : List Edge)
    (same : left.2 = right.1) : hasBreak start (before ++ left :: right :: after) = true := by
  induction before generalizing start with
  | nil => simp [hasBreak, same]
  | cons e es ih => simp [hasBreak, ih]

/-- Switches need not commute. Repeating the same involutions in the opposite
    order reverses the first traversal. -/
theorem mirrorUndo (step : ι → α → α) (undo : ∀ i x, step i (step i x) = x)
    (stages : List ι) (x : α) :
    stages.reverse.foldl (fun y i => step i y) (stages.foldl (fun y i => step i y) x) = x := by
  induction stages generalizing x with
  | nil => rfl
  | cons i stages ih =>
    simp [List.reverse_cons, List.foldl_append, ih, undo]

def xorMask (mask x : ι → Bool) : ι → Bool := fun i => Bool.xor (x i) (mask i)

/-- Paired addresses share a switch setting, so a controlled XOR mask is
    an involution even when the setting depends on the address. -/
theorem pairedXorUndo (mask : ι → Bool) (setting : (ι → Bool) → Bool)
    (paired : ∀ x, setting (xorMask mask x) = setting x) (x : ι → Bool) :
    let step := fun y => if setting y then xorMask mask y else y
    step (step x) = x := by
  dsimp only
  cases h : setting x with
  | false => simp [h]
  | true =>
    simp [h, paired]
    funext i
    cases hx : x i <;> cases hm : mask i <;> simp [xorMask, hx, hm]

end ChainProjection
