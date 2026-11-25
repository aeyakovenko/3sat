import Std

namespace DenseAsciiCircuitTransfer

/-- A row may be selected only if all the flags named by its chunks are on.
    At least two distinct rows must be selected and each bank is one-hot or empty. -/
def FlagConstraints (rows : Row → Bank → Value) (selected : Row → Bool)
    (flags : Bank → Value → Bool) : Prop :=
  (∃ i j, i ≠ j ∧ selected i = true ∧ selected j = true) ∧
  (∀ i, selected i = true → ∀ b, flags b (rows i b) = true) ∧
  ∀ b u v, flags b u = true → flags b v = true → u = v

/-- The selectors and bank flags have an extension exactly when two distinct
    source rows have identical chunks at every bank. -/
theorem flag_extension_iff_duplicate [DecidableEq Row] [DecidableEq Value]
    (rows : Row → Bank → Value) :
    (∃ selected flags, FlagConstraints rows selected flags) ↔
    ∃ i j, i ≠ j ∧ rows i = rows j := by
  constructor
  · rintro ⟨selected, flags, ⟨i, j, different, hi, hj⟩, required, oneHot⟩
    exact ⟨i, j, different, funext fun b => oneHot b _ _ (required i hi b) (required j hj b)⟩
  · rintro ⟨i, j, different, equalRows⟩
    refine ⟨fun k => decide (k = i ∨ k = j), fun b v => decide (v = rows i b),
      ⟨i, j, different, by simp, by simp⟩, ?_, ?_⟩
    · intro k selected b
      rcases of_decide_eq_true selected with rfl | rfl
      · simp
      · simp [equalRows]
    · intro b u v hu hv
      exact (of_decide_eq_true hu).trans (of_decide_eq_true hv).symm

/-- An operand can refer to any earlier result or input, with no bound on reuse. -/
inductive Wire (n : Nat) where
  | index (i : Fin n)
  | literal (x : Bool)

def Wire.read (w : Wire n) (values : Fin n → Bool) : Bool :=
  match w with
  | .index i => values i
  | .literal x => x

/-- A topological ordering of arbitrary binary Boolean gates. A newly
    produced value gets index zero in the environment for the remaining gates. -/
inductive Circuit : Nat → Type where
  | output (w : Wire n) : Circuit n
  | gate (op : Bool → Bool → Bool) (a b : Wire n) (tail : Circuit (n+1)) : Circuit n

def evaluate : Circuit n → (Fin n → Bool) → List Bool × Bool
  | .output w, values => ([], w.read values)
  | .gate op a b tail, values =>
    let v := op (a.read values) (b.read values)
    let rest := evaluate tail (Fin.cases v values)
    (v :: rest.1, rest.2)

/-- Each local relation is the gate's truth table. The output wire is pinned to true. -/
def pinned : Circuit n → (Fin n → Bool) → List Bool → Prop
  | .output w, values, ws => ws = [] ∧ w.read values = true
  | .gate _ _ _ _, _, [] => False
  | .gate op a b tail, values, v :: ws =>
    v = op (a.read values) (b.read values) ∧ pinned tail (Fin.cases v values) ws

/-- A one-valued output has exactly one consistent vector of gate outputs;
    a zero-valued output has none. The operand references may have arbitrary fanout. -/
theorem pinned_iff_canonical (c : Circuit n) (values : Fin n → Bool) (ws : List Bool) :
    pinned c values ws ↔ ws = (evaluate c values).1 ∧ (evaluate c values).2 = true := by
  induction c generalizing ws with
  | output w => rfl
  | gate op a b tail ih =>
    cases ws with
    | nil => simp [pinned, evaluate]
    | cons v ws =>
      simp only [pinned, evaluate, List.cons.injEq]
      constructor
      · rintro ⟨rfl, valid⟩
        obtain ⟨rest, out⟩ := (ih _ _).mp valid
        exact ⟨⟨rfl, rest⟩, out⟩
      · rintro ⟨⟨rfl, rest⟩, out⟩
        exact ⟨rfl, (ih _ _).mpr ⟨rest, out⟩⟩

/-- Explicit equality trees can distribute a value to its multiple uses. -/
inductive CopyTree where
  | leaf
  | fork (left right : CopyTree)

def CopyValues : CopyTree → Type
  | .leaf => Bool
  | .fork l r => Bool × CopyValues l × CopyValues r

def copyValues : (tree : CopyTree) → Bool → CopyValues tree
  | .leaf, x => x
  | .fork l r, x => (x, copyValues l x, copyValues r x)

def copiesAgree : (tree : CopyTree) → Bool → CopyValues tree → Prop
  | .leaf, x, v => v = x
  | .fork l r, x, (v, a, b) => v = x ∧ copiesAgree l v a ∧ copiesAgree r v b

theorem copies_iff_canonical (tree : CopyTree) (x : Bool) (values : CopyValues tree) :
    copiesAgree tree x values ↔ values = copyValues tree x := by
  induction tree generalizing x with
  | leaf => rfl
  | fork l r il ir =>
    rcases values with ⟨v, a, b⟩
    simp only [copiesAgree, copyValues, Prod.mk.injEq, il, ir]
    constructor <;> rintro ⟨rfl, rfl, rfl⟩ <;> simp

end DenseAsciiCircuitTransfer
