import Std

namespace SplitOverlapDiamond

inductive Name (α : Type) where
  | x | y | other (v : α)
  deriving DecidableEq

structure Lit (α : Type) where
  name : α
  neg : Bool
  deriving DecidableEq

abbrev CNF (α : Type) := List (List (Lit α))

def litVal (v : α → Bool) (l : Lit α) : Bool := v l.name ^^ l.neg

def eval (v : α → Bool) (f : CNF α) : Bool := f.all fun c => c.any (litVal v)

def lift (l : Lit α) : Lit (Name α) := ⟨.other l.name, l.neg⟩

def common (ctx : CNF α) : CNF (Name α) := ctx.map fun c => c.map lift

def xn (neg : Bool) : Lit (Name α) := ⟨.x, neg⟩
def yn (neg : Bool) : Lit (Name α) := ⟨.y, neg⟩

/-- The normalizations below take the central pivot literals positive, with
their opposite literals in their separate companion clauses. -/
def source (a b c : Lit α) (ctx : CNF α) : CNF (Name α) :=
  [xn false, yn false, lift b] :: [xn true, lift b, lift a] ::
    [yn true, lift b, lift c] :: common ctx

def reducedX (a b c : Lit α) (ctx : CNF α) : CNF (Name α) :=
  [yn false, lift b, lift a] :: [yn true, lift b, lift c] :: common ctx

def reducedY (a b c : Lit α) (ctx : CNF α) : CNF (Name α) :=
  [xn false, lift b, lift c] :: [xn true, lift b, lift a] :: common ctx

def rename : Lit (Name α) → Lit (Name α)
  | ⟨.x, s⟩ => yn (!s)
  | ⟨.y, s⟩ => xn (!s)
  | ⟨.other n, s⟩ => ⟨.other n, s⟩

theorem rename_twice (l : Lit (Name α)) : rename (rename l) = l := by
  obtain ⟨n, s⟩ := l
  cases n <;> cases s <;> rfl

def renameCNF (f : CNF (Name α)) := f.map fun c => c.map rename

@[simp] theorem fixed_other (l : Lit α) : rename (lift l) = lift l := rfl

@[simp] theorem fixed_context (ctx : CNF α) : renameCNF (common ctx) = common ctx := by
  induction ctx with
  | nil => rfl
  | cons c ctx ih =>
    have fixed : (c.map lift).map rename = c.map lift := by
      induction c with
      | nil => rfl
      | cons l c hi => simp [hi]
    change (c.map lift).map rename :: renameCNF (common ctx) = c.map lift :: common ctx
    rw [fixed, ih]

/-- The renamed left CNF is exactly the right CNF after exchanging its first two
clauses. This is structural, and includes every signed literal in the context. -/
theorem structural_diamond (a b c : Lit α) (ctx : CNF α) :
    renameCNF (reducedX a b c ctx) =
      [xn true, lift b, lift a] :: [xn false, lift b, lift c] :: common ctx := by
  change _ :: _ :: renameCNF (common ctx) = _
  rw [fixed_context]
  rfl

theorem residual_permutation (a b c : Lit α) (ctx : CNF α) :
    (renameCNF (reducedX a b c ctx)).Perm (reducedY a b c ctx) := by
  rw [structural_diamond]
  exact List.Perm.swap _ _ _

def transform (v : Name α → Bool) : Name α → Bool
  | .x => !(v .y)
  | .y => !(v .x)
  | .other n => v (.other n)

theorem transform_twice (v : Name α → Bool) : transform (transform v) = v := by
  funext z
  cases z <;> simp [transform]

private theorem lit_rename (l : Lit (Name α)) (v : Name α → Bool) :
    litVal (transform v) (rename l) = litVal v l := by
  obtain ⟨n, s⟩ := l
  cases n with
  | x => cases s <;> cases hx : v .x <;> simp [rename, yn, litVal, transform, hx]
  | y => cases s <;> cases hy : v .y <;> simp [rename, xn, litVal, transform, hy]
  | other _ => rfl

theorem evaluation_commutes (f : CNF (Name α)) (v : Name α → Bool) :
    eval (transform v) (renameCNF f) = eval v f := by
  induction f with
  | nil => rfl
  | cons c f ih =>
    have clause : (c.map rename).any (litVal (transform v)) = c.any (litVal v) := by
      induction c with
      | nil => rfl
      | cons l ls h => simp only [List.map_cons, List.any_cons, lit_rename, h]
    change ((c.map rename).any (litVal (transform v)) && eval (transform v) (renameCNF f)) =
        (c.any (litVal v) && eval v f)
    rw [clause, ih]

theorem residual_values (a b c : Lit α) (ctx : CNF α) (v : Name α → Bool) :
    eval (transform v) (reducedY a b c ctx) = eval v (reducedX a b c ctx) := by
  rw [← evaluation_commutes (reducedX a b c ctx) v, structural_diamond]
  unfold reducedY eval
  simp only [List.all_cons]
  exact Bool.and_left_comm _ _ _

/-- Only the surviving pivot and background variables need assigning: left
retains y, right retains x. The absent variable is never a free model multiplier. -/
abbrev ResidualAssignment (α : Type) := Bool × (α → Bool)

def leftVal (v : ResidualAssignment α) : Name α → Bool
  | .x => false | .y => v.1 | .other k => v.2 k

def rightVal (v : ResidualAssignment α) : Name α → Bool
  | .x => v.1 | .y => true | .other k => v.2 k

def swapResidual (v : ResidualAssignment α) : ResidualAssignment α := (!v.1, v.2)

theorem swapResidual_twice (v : ResidualAssignment α) : swapResidual (swapResidual v) = v := by
  cases v <;> simp [swapResidual]

theorem model_bijection (a b c : Lit α) (ctx : CNF α) (v : ResidualAssignment α) :
    eval (rightVal (swapResidual v)) (reducedY a b c ctx) =
    eval (leftVal v) (reducedX a b c ctx) := by
  have eq : rightVal (swapResidual v) = transform (leftVal v) := by
    funext z
    cases z <;> rfl
  rw [eq]
  exact residual_values _ _ _ _ _

theorem unique_model_preimage (a b c : Lit α) (ctx : CNF α)
    (w : ResidualAssignment α) (hw : eval (rightVal w) (reducedY a b c ctx) = true) :
    ∃ v, eval (leftVal v) (reducedX a b c ctx) = true ∧
      swapResidual v = w ∧ ∀ u, swapResidual u = w → u = v := by
  refine ⟨swapResidual w, ?_, swapResidual_twice w, ?_⟩
  · have eq := model_bijection a b c ctx (swapResidual w)
    rw [swapResidual_twice] at eq
    exact eq.symm.trans hw
  · intro u hu
    have eq := congrArg swapResidual hu
    simpa only [swapResidual_twice] using eq

def assign (x y : Bool) (v : α → Bool) : Name α → Bool
  | .x => x | .y => y | .other k => v k

theorem common_value (ctx : CNF α) (x y : Bool) (v : α → Bool) :
    eval (assign x y v) (common ctx) = eval v ctx := by
  induction ctx with
  | nil => rfl
  | cons c ctx ih =>
    have clause : (c.map lift).any (litVal (assign x y v)) = c.any (litVal v) := by
      induction c with
      | nil => rfl
      | cons l c hc => simp only [List.map_cons, List.any_cons, hc]; rfl
    change ((c.map lift).any (litVal (assign x y v)) && eval (assign x y v) (common ctx)) =
      (c.any (litVal v) && eval v ctx)
    rw [clause, ih]

private theorem source_value (a b c : Lit α) (ctx : CNF α) (x y : Bool) (v : α → Bool) :
    eval (assign x y v) (source a b c ctx) =
    ((x || y || litVal v b) && ((!x || litVal v b || litVal v a) &&
      ((!y || litVal v b || litVal v c) && eval v ctx))) := by
  unfold source
  change (_ && (_ && (_ && eval (assign x y v) (common ctx)))) = _
  rw [common_value]
  simp [litVal, assign, xn, yn, lift, Bool.or_assoc]

private theorem left_value (a b c : Lit α) (ctx : CNF α) (x y : Bool) (v : α → Bool) :
    eval (assign x y v) (reducedX a b c ctx) =
    ((y || litVal v b || litVal v a) && ((!y || litVal v b || litVal v c) && eval v ctx)) := by
  unfold reducedX
  change (_ && (_ && eval (assign x y v) (common ctx))) = _
  rw [common_value]
  simp [litVal, assign, xn, yn, lift, Bool.or_assoc]

private theorem right_value (a b c : Lit α) (ctx : CNF α) (x y : Bool) (v : α → Bool) :
    eval (assign x y v) (reducedY a b c ctx) =
    ((x || litVal v b || litVal v c) && ((!x || litVal v b || litVal v a) && eval v ctx)) := by
  unfold reducedY
  change (_ && (_ && eval (assign x y v) (common ctx))) = _
  rw [common_value]
  simp [litVal, assign, xn, yn, lift, Bool.or_assoc]

theorem eliminate_x (a b c : Lit α) (ctx : CNF α) (x y : Bool) (v : α → Bool) :
    eval (assign x y v) (reducedX a b c ctx) =
      (eval (assign false y v) (source a b c ctx) || eval (assign true y v) (source a b c ctx)) := by
  simp only [left_value, source_value]
  cases y <;> cases litVal v a <;> cases litVal v b <;> cases litVal v c <;> cases eval v ctx <;> decide

theorem eliminate_y (a b c : Lit α) (ctx : CNF α) (x y : Bool) (v : α → Bool) :
    eval (assign x y v) (reducedY a b c ctx) =
      (eval (assign x false v) (source a b c ctx) || eval (assign x true v) (source a b c ctx)) := by
  simp only [right_value, source_value]
  cases x <;> cases litVal v a <;> cases litVal v b <;> cases litVal v c <;> cases eval v ctx <;> decide

/- Generic normal-form induction. Applying it to signed-renaming classes
requires a rule on the quotient and a classification of *all* its local peaks. -/
namespace NormalForm

inductive Steps (r : α → α → Prop) : α → α → Prop
  | refl (x) : Steps r x x
  | more {x y z} : r x y → Steps r y z → Steps r x z

def terminal (r : α → α → Prop) (x : α) := ∀ y, ¬ r x y

theorem exists_terminal {r : α → α → Prop} (size : α → Nat)
    (decreases : ∀ a b, r a b → size b < size a) (a : α) :
    ∃ n, Steps r a n ∧ terminal r n := by
  by_cases h : ∃ b, r a b
  · obtain ⟨b, hab⟩ := h
    obtain ⟨n, hbn, hn⟩ := exists_terminal size decreases b
    exact ⟨n, .more hab hbn, hn⟩
  · exact ⟨a, .refl a, fun b hab => h ⟨b,hab⟩⟩
termination_by size a
decreasing_by exact decreases _ _ hab

theorem unique_terminal {r : α → α → Prop} (size : α → Nat)
    (decreases : ∀ a b, r a b → size b < size a)
    (join : ∀ a b c, r a b → r a c → ∃ d, Steps r b d ∧ Steps r c d)
    (a u v : α) (hu : Steps r a u) (hv : Steps r a v)
    (tu : terminal r u) (tv : terminal r v) : u = v := by
  cases hu with
  | refl =>
    cases hv with
    | refl => rfl
    | more h _ => exact (tu _ h).elim
  | @more b _ _ hab bu =>
    cases hv with
    | refl => exact (tv _ hab).elim
    | @more _ c _ hac cv =>
      obtain ⟨d, bd, cd⟩ := join _ _ _ hab hac
      obtain ⟨n, dn, tn⟩ := exists_terminal size decreases d
      have append {j k l : α} (jk : Steps r j k) (kl : Steps r k l) : Steps r j l := by
        induction jk with
        | refl => exact kl
        | more h _ ih => exact .more h (ih kl)
      have left := unique_terminal size decreases join _ u n bu (append bd dn) tu tn
      have right := unique_terminal size decreases join _ v n cv (append cd dn) tv tn
      exact left.trans right.symm
termination_by size a
decreasing_by all_goals first | exact decreases _ _ hab | exact decreases _ _ hac

end NormalForm

end SplitOverlapDiamond
