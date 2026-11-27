import Std

namespace TransferMinorBranches

/-- Extend each abstention to one constant bit.  The number of correct
answers from the two extensions counts every covered position twice. -/
def extensionHits (default : Bool) : List (Bool × Option Bool) → Nat
  | [] => 0
  | (bit, answer) :: rest =>
      (if answer.getD default == bit then 1 else 0) + extensionHits default rest

def supplied : List (Bool × Option Bool) → Nat
  | [] => 0
  | (_, answer) :: rest => (if answer.isSome then 1 else 0) + supplied rest

theorem soundExtensionSum (rows : List (Bool × Option Bool))
    (sound : ∀ row ∈ rows, ∀ v, row.2 = some v → v = row.1) :
    extensionHits false rows + extensionHits true rows = rows.length + supplied rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have tail := ih (fun x hx => sound x (List.mem_cons_of_mem _ hx))
    have head := sound row (List.mem_cons_self)
    rcases row with ⟨bit, answer⟩
    cases answer with
    | none =>
      cases bit <;> simp [extensionHits, supplied] at * <;> omega
    | some v =>
      have h : v = bit := head v rfl
      subst v
      cases bit <;> simp [extensionHits, supplied] at * <;> omega

inductive Vertex (L R : Type) where
  | left (x : L)
  | right (y : R)

def Edge (adj : L → R → Prop) : Vertex L R → Vertex L R → Prop
  | .left l, .right r | .right r, .left l => adj l r
  | _, _ => False

inductive Reaches {V : Type} (edge : V → V → Prop) (inside : V → Prop) : V → V → Prop where
  | stay {u} : inside u → Reaches edge inside u u
  | step {u v w} : inside u → edge u v → Reaches edge inside v w → Reaches edge inside u w

def branch (group : I → L → Prop) (center tip : I → R) (i : I) : Vertex L R → Prop
  | .left l => group i l
  | .right r => r = center i ∨ r = tip i

/-- A common neighbor connects each group. A private right vertex touching
every group attaches to its own group and supplies its edges to the others. -/
theorem cliqueBranches (adj : L → R → Prop) (group : I → L → Prop) (center tip : I → R)
    (groupsSeparate : ∀ i j l, group i l → group j l → i = j)
    (centerUnique : ∀ i j, center i = center j → i = j)
    (tipUnique : ∀ i j, tip i = tip j → i = j)
    (separate : ∀ i j, center i ≠ tip j)
    (star : ∀ i l, group i l → adj l (center i))
    (touch : ∀ i j, ∃ l, group i l ∧ adj l (tip j)) :
    (∀ i v, branch group center tip i v →
      Reaches (Edge adj) (branch group center tip i) v (.right (center i))) ∧
    (∀ i j v, branch group center tip i v → branch group center tip j v → i = j) ∧
    (∀ i j, ∃ v w, branch group center tip i v ∧ branch group center tip j w ∧ Edge adj v w) := by
  constructor
  · intro i v hv
    have hub : branch group center tip i (.right (center i)) := Or.inl rfl
    cases v with
    | left l =>
      have link : Edge adj (.left l) (.right (center i)) := star i l hv
      exact Reaches.step hv link (.stay hub)
    | right r =>
      rcases hv with h | h
      · subst r
        exact .stay hub
      · subst r
        obtain ⟨l, hl, hadj⟩ := touch i i
        have first : Edge adj (.right (tip i)) (.left l) := hadj
        have second : Edge adj (.left l) (.right (center i)) := star i l hl
        have member : branch group center tip i (.left l) := hl
        exact Reaches.step (Or.inr rfl) first (Reaches.step member second (.stay hub))
  constructor
  · intro i j v hi hj
    cases v with
    | left l => exact groupsSeparate i j l hi hj
    | right r =>
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact centerUnique i j (hi.symm.trans hj)
      · exact False.elim (separate i j (hi.symm.trans hj))
      · exact False.elim (separate j i (hj.symm.trans hi))
      · exact tipUnique i j (hi.symm.trans hj)
  · intro i j
    obtain ⟨l, hl, hadj⟩ := touch i j
    exact ⟨.left l, .right (tip j), hl, Or.inr rfl, hadj⟩

end TransferMinorBranches
