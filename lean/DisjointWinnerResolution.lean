import Std

namespace DisjointWinnerResolution

abbrev Lit (V : Type) := V × Bool
abbrev Clause (V : Type) := Lit V → Prop

/-- The positive occurrence is removed only from the left parent, the
    negative occurrence only from the right. Clauses are sets of literals. -/
def resolvent {V} (a b : Clause V) (pivot : V) : Clause V := fun l =>
  (a l ∧ l ≠ (pivot, true)) ∨ (b l ∧ l ≠ (pivot, false))

/-- Source tags distinguish input groups even if two groups contain the
    empty axiom. The only non-axiom rule is binary resolution. -/
inductive Proof {V G : Type} (source : G → Clause V → Prop) : Clause V → Type 1 where
  | ax {c} (group : G) (input : source group c) : Proof source c
  | step {a b : Clause V} (pivot : V) (left : Proof source a) (right : Proof source b)
      (pos : a (pivot, true)) (neg : b (pivot, false)) : Proof source (resolvent a b pivot)

def AllFrom {V G} {source : G → Clause V → Prop} (g : G) :
    {c : Clause V} → Proof source c → Prop
  | _, .ax h _ => h = g
  | _, .step _ left right _ _ => AllFrom g left ∧ AllFrom g right

def nodes {V G} {source : G → Clause V → Prop} :
    {c : Clause V} → Proof source c → Nat
  | _, .ax _ _ => 1
  | _, .step _ left right _ _ => 1 + nodes left + nodes right

/-- Every ancestor axiom in a resolution tree belongs to the same group.
    A common pivot forces agreement of the two groups at every inference. -/
theorem one_group {V G} {source : G → Clause V → Prop} (owner : V → G)
    (locality : ∀ g c, source g c → ∀ l, c l → owner l.1 = g)
    {c} (p : Proof source c) :
    ∃ g, AllFrom g p ∧ ∀ l, c l → owner l.1 = g := by
  induction p with
  | ax g h => exact ⟨g, rfl, locality g _ h⟩
  | step pivot left right pos neg ih jh =>
    obtain ⟨g, hl, cl⟩ := ih
    obtain ⟨h, hr, cr⟩ := jh
    have gh : g = h := (cl (pivot, true) pos).symm.trans (cr (pivot, false) neg)
    subst h
    refine ⟨g, ⟨hl, hr⟩, ?_⟩
    intro l mem
    rcases mem with lmem | rmem
    · exact cl l lmem.1
    · exact cr l rmem.1

/-- Reuse every inference with its original pivot to obtain a refutation
    from the chosen group's axioms alone. -/
def restrictProof {V G} {source : G → Clause V → Prop} (g : G) :
    {c : Clause V} → (p : Proof source c) → AllFrom g p →
      Proof (fun _ : Unit => source g) c
  | _, .ax _ input, all => .ax () (all ▸ input)
  | _, .step pivot left right pos neg, all =>
    .step pivot (restrictProof g left all.1) (restrictProof g right all.2) pos neg

theorem nodes_restrict {V G} {source : G → Clause V → Prop} (g : G)
    {c} (p : Proof source c) (all : AllFrom g p) :
    nodes (restrictProof g p all) = nodes p := by
  induction p with
  | ax => rfl
  | step _ _ _ _ _ ih jh =>
    simp only [restrictProof, nodes]
    rw [ih, jh]

def Satisfies {V} (w : V → Bool) (c : Clause V) : Prop :=
  ∃ l, c l ∧ w l.1 = l.2

theorem resolution_sound {V} (w : V → Bool) (a b : Clause V) (pivot : V)
    (left : Satisfies w a) (right : Satisfies w b) :
    Satisfies w (resolvent a b pivot) := by
  cases h : w pivot with
  | false =>
    obtain ⟨l, al, sat⟩ := left
    refine ⟨l, Or.inl ⟨al, ?_⟩, sat⟩
    rintro rfl
    simp [h] at sat
  | true =>
    obtain ⟨l, bl, sat⟩ := right
    refine ⟨l, Or.inr ⟨bl, ?_⟩, sat⟩
    rintro rfl
    simp [h] at sat

theorem proof_sound {V G} {source : G → Clause V → Prop} (w : V → Bool)
    (all : ∀ g c, source g c → Satisfies w c) {c} (p : Proof source c) :
    Satisfies w c := by
  induction p with
  | ax g input => exact all g _ input
  | step pivot _ _ _ _ left right => exact resolution_sound w _ _ pivot left right

/-- With a satisfying assignment for each other group, the entire empty-clause
    tree is a winner-only refutation of exactly the given size. -/
theorem extract_winner {V G} {source : G → Clause V → Prop} (owner : V → G)
    (locality : ∀ g c, source g c → ∀ l, c l → owner l.1 = g) (winner : G)
    (others : ∀ g, g ≠ winner → ∃ w, ∀ c, source g c → Satisfies w c)
    (p : Proof source (fun _ => False)) :
    AllFrom winner p ∧ ∃ q : Proof (fun _ : Unit => source winner) (fun _ => False),
      nodes q = nodes p := by
  obtain ⟨g, all, _⟩ := one_group owner locality p
  have q := restrictProof g p all
  have same : g = winner := by
    apply Classical.byContradiction
    intro ne
    obtain ⟨w, hw⟩ := others g ne
    obtain ⟨_, bad, _⟩ := proof_sound w (fun _ => hw) q
    exact bad
  subst g
  exact ⟨all, restrictProof winner p all, nodes_restrict winner p all⟩


/-- A shared derivation stores each line once at its original Fin n index.
    The keep parameter restricts which earlier indices can be used as parents. -/
inductive Row {V G : Type} {n : Nat} (source : G → Clause V → Prop)
    (clauses : Fin n → Clause V) (keep : Fin n → Prop) (i : Fin n) : Type 1 where
  | ax (group : G) (input : source group (clauses i))
  | step (left right : Fin n) (leftLt : left.val < i.val) (rightLt : right.val < i.val)
      (keepLeft : keep left) (keepRight : keep right) (pivot : V)
      (pos : clauses left (pivot, true)) (neg : clauses right (pivot, false))
      (out : clauses i = resolvent (clauses left) (clauses right) pivot)

abbrev Rows {V G n} (source : G → Clause V → Prop) (clauses : Fin n → Clause V) :=
  ∀ i, Row source clauses (fun _ => True) i

def rowGroup {V G n} {source : G → Clause V → Prop} {clauses : Fin n → Clause V}
    {keep i} (owner : V → G) : Row source clauses keep i → G
  | .ax g _ => g
  | .step _ _ _ _ _ _ pivot _ _ _ => owner pivot

def parentOf {V G n} {source : G → Clause V → Prop} {clauses : Fin n → Clause V}
    {keep i} : Row source clauses keep i → Fin n → Prop
  | .ax _ _, _ => False
  | .step left right _ _ _ _ _ _ _ _, j => j = left ∨ j = right

theorem dag_homogeneous {V G n} {source : G → Clause V → Prop}
    {clauses : Fin n → Clause V} (owner : V → G)
    (locality : ∀ g c, source g c → ∀ l, c l → owner l.1 = g)
    (rows : Rows source clauses) (i : Fin n) :
    ∀ l, clauses i l → owner l.1 = rowGroup owner (rows i) := by
  suffices stages : ∀ k, ∀ j : Fin n, j.val = k →
      ∀ l, clauses j l → owner l.1 = rowGroup owner (rows j) from stages i.val i rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro j hk l hl
    cases eq : rows j with
    | ax g input => exact locality g _ input l hl
    | step a b aLt bLt _ _ pivot pos neg out =>
      have ha := ih a.val (hk ▸ aLt) a rfl
      have hb := ih b.val (hk ▸ bLt) b rfl
      rw [out] at hl
      rcases hl with left | right
      · exact (ha l left.1).trans (ha (pivot, true) pos).symm
      · exact (hb l right.1).trans (hb (pivot, false) neg).symm

theorem parent_same_group {V G n} {source : G → Clause V → Prop}
    {clauses : Fin n → Clause V} (owner : V → G)
    (locality : ∀ g c, source g c → ∀ l, c l → owner l.1 = g)
    (rows : Rows source clauses) {i j : Fin n} (parent : parentOf (rows i) j) :
    rowGroup owner (rows j) = rowGroup owner (rows i) := by
  cases eq : rows i with
  | ax g input => rw [eq] at parent; contradiction
  | step a b _ _ _ _ pivot pos neg _ =>
    rw [eq] at parent
    rcases parent with rfl | rfl
    · exact (dag_homogeneous owner locality rows _ (pivot, true) pos).symm
    · exact (dag_homogeneous owner locality rows _ (pivot, false) neg).symm

inductive Ancestor {V G n} {source : G → Clause V → Prop} {clauses : Fin n → Clause V}
    (rows : Rows source clauses) (root : Fin n) : Fin n → Prop where
  | self : Ancestor rows root root
  | prior {i j} : Ancestor rows root i → parentOf (rows i) j → Ancestor rows root j

theorem ancestor_same_group {V G n} {source : G → Clause V → Prop}
    {clauses : Fin n → Clause V} (owner : V → G)
    (locality : ∀ g c, source g c → ∀ l, c l → owner l.1 = g)
    (rows : Rows source clauses) {root i : Fin n} (reachable : Ancestor rows root i) :
    rowGroup owner (rows i) = rowGroup owner (rows root) := by
  induction reachable with
  | self => rfl
  | prior _ edge ih => exact (parent_same_group owner locality rows edge).trans ih

inductive LineShape (V : Type) (n : Nat) : Type where
  | ax
  | step (left right : Fin n) (pivot : V)

def rowShape {V G n} {source : G → Clause V → Prop} {clauses : Fin n → Clause V}
    {keep i} : Row source clauses keep i → LineShape V n
  | .ax _ _ => .ax
  | .step left right _ _ _ _ pivot _ _ _ => .step left right pivot

/-- Keep exactly the ancestors of any chosen conclusion. Each kept line is
    derivable from its original parent indices, and every kept axiom belongs
    to the root's group. An empty conclusion thus gives a component DAG
    refutation on a subset of the original indices, without unfolding it.
    Several components may be unsatisfiable. -/
theorem extract_component_dag {V G n} {source : G → Clause V → Prop}
    {clauses : Fin n → Clause V} (owner : V → G)
    (locality : ∀ g c, source g c → ∀ l, c l → owner l.1 = g)
    (rows : Rows source clauses) (root : Fin n) (i : Fin n) (reach : Ancestor rows root i) :
    ∃ q : Row (fun _ : Unit => source (rowGroup owner (rows root)))
      clauses (Ancestor rows root) i, rowShape q = rowShape (rows i) := by
  have groupEq := ancestor_same_group owner locality rows reach
  cases eq : rows i with
  | ax g input =>
    rw [eq] at groupEq
    change g = rowGroup owner (rows root) at groupEq
    exact ⟨.ax () (groupEq ▸ input), rfl⟩
  | step a b aLt bLt _ _ pivot pos neg out =>
    have left : parentOf (rows i) a := by rw [eq]; exact Or.inl rfl
    have right : parentOf (rows i) b := by rw [eq]; exact Or.inr rfl
    exact ⟨.step a b aLt bLt (.prior reach left) (.prior reach right) pivot pos neg out, rfl⟩

end DisjointWinnerResolution
