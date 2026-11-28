import Std

namespace GuardedAffineSubdivision

def correction (δ off α β b x y : Bool) : Bool :=
  (((δ && b) ^^ off) ^^ (α && x)) ^^ (β && y)

def physical (x y t : Bool) : Bool := (x || t) && (t || y)

/-- The supplied correction is relative to the ordinary XOR insertion. -/
def fiber (off α β : Bool) : Prop :=
  ∀ x y : Bool, physical x y ((x ^^ y) ^^ ((off ^^ (α && x)) ^^ (β && y))) = (x || y)

theorem fiber_iff (off α β : Bool) :
    fiber off α β ↔ off = false ∧ α = false ∧ β = false := by
  unfold fiber
  cases off <;> cases α <;> cases β <;> decide

/-- The same context guards both the old and new edge clauses. If it is false,
both conjunctions are false independently of the inserted bit. -/
def Valid {Z : Type} (active : Bool → Z → Prop) (δ : Bool)
    (misc : Z → Bool) (α β : Bool) : Prop :=
  ∀ b z, active b z → fiber ((δ && b) ^^ misc z) α β

def guard {Z : Type} (F : Z → Prop) (b : Bool) (z : Z) : Prop :=
  b = false ∨ F z

/-- The arbitrary offset misc includes the affine constant and all old-input
terms. The whole b=0 slice is active; the statement even allows a nonlinear
offset on these inputs. -/
theorem only_delta {Z : Type} {F : Z → Prop} {δ α β : Bool} {misc : Z → Bool}
    (h : Valid (guard F) δ misc α β) (b : Bool) (z : Z) (x y : Bool) :
    correction δ (misc z) α β b x y = (δ && b) := by
  have hz := (fiber_iff _ _ _).mp (h false z (Or.inl rfl))
  have clean : misc z = false ∧ α = false ∧ β = false := by simpa using hz
  simp [correction, clean.1, clean.2.1, clean.2.2]

theorem delta_valid_iff {Z : Type} (active : Bool → Z → Prop) (δ : Bool) :
    Valid active δ (fun _ => false) false false ↔
      (δ = false ∨ ∀ z, ¬active true z) := by
  constructor
  · intro h
    cases δ with
    | false => exact Or.inl rfl
    | true =>
      right
      intro z hz
      have bad := ((fiber_iff _ _ _).mp (h true z hz)).1
      contradiction
  · intro h b z hz
    apply (fiber_iff _ _ _).mpr
    rcases h with h|h
    · simp [h]
    · cases b with
      | false => simp
      | true => exact False.elim (h z hz)

theorem second_rule_iff_unsatisfiable {Z : Type} (F : Z → Prop) :
    Valid (guard F) true (fun _ => false) false false ↔ ¬∃ z, F z := by
  rw [delta_valid_iff]
  simp [guard]

/-- Standard ternary split of (¬b ∨ l ∨ r ∨ s). The variables w_i are fresh. -/
def splitClause (b l r s w : Bool) : Bool :=
  ((!b || l) || w) && ((!w || r) || s)

def splitActive {Z : Type} (m : Nat) (L R S : Nat → Z → Bool)
    (b : Bool) (p : Z × (Nat → Bool)) : Prop :=
  ∀ i, i < m → splitClause b (L i p.1) (R i p.1) (S i p.1) (p.2 i) = true

def original {Z : Type} (m : Nat) (L R S : Nat → Z → Bool) (z : Z) : Prop :=
  ∀ i, i < m → (L i z || R i z || S i z) = true

private theorem split_implies (l r s w : Bool) :
    splitClause true l r s w = true → (l || r || s) = true := by
  cases l <;> cases r <;> cases s <;> cases w <;> decide

private theorem split_choice (l r s : Bool) :
    (l || r || s) = true → splitClause true l r s (!l) = true := by
  cases l <;> cases r <;> cases s <;> decide

theorem split_projection {Z : Type} (m : Nat) (L R S : Nat → Z → Bool) (z : Z) :
    (∃ w, splitActive m L R S true (z,w)) ↔ original m L R S z := by
  constructor
  · rintro ⟨w,h⟩ i hi
    exact split_implies _ _ _ _ (h i hi)
  · intro h
    exact ⟨fun j => !(L j z), fun i hi => split_choice _ _ _ (h i hi)⟩

/-- Actual GF(2) linear form on the m fresh split bits. -/
def dot (weights w : Nat → Bool) : Nat → Bool
  | 0 => false
  | n+1 => dot weights w n ^^ (weights n && w n)

private theorem dot_zero (weights : Nat → Bool) (n : Nat) :
    dot weights (fun _ => false) n = false := by
  induction n <;> simp [dot, *]

private theorem dot_unit (weights : Nat → Bool) (i n : Nat) :
    dot weights (fun j => decide (j=i)) n = if i<n then weights i else false := by
  induction n with
  | zero => simp [dot]
  | succ n ih =>
    rcases Nat.lt_trichotomy i n with h|h|h
    · simp [dot, ih, h, Nat.lt_trans h (Nat.lt_succ_self n), (Nat.ne_of_lt h).symm]
    · subst i
      simp [dot, ih]
    · simp [dot, ih, Nat.not_lt.mpr (Nat.le_of_lt h), Nat.not_lt.mpr h,
        Nat.ne_of_lt h]

private theorem dot_zero_weights (weights w : Nat → Bool) (n : Nat)
    (h : ∀ i, i < n → weights i = false) : dot weights w n = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [dot, h n (by omega), ih (fun i hi => h i (by omega))]

/-- Each split auxiliary can participate in the proposed affine rule. Provided
the final two literals of each old clause are simultaneously not both false
on some input, the guarded slice at b=0 rules out every such coefficient.
This holds for ordinary disjunctions of literals on unrestricted inputs. -/
theorem split_only_delta {Z : Type} {m : Nat} {L R S : Nat → Z → Bool}
    {δ α β : Bool} {misc : Z → Bool} {weights : Nat → Bool}
    (canTurnOn : ∀ i, i < m → ∃ z, (R i z || S i z) = true)
    (h : Valid (splitActive m L R S) δ (fun p => misc p.1 ^^ dot weights p.2 m) α β)
    (b : Bool) (z : Z) (w : Nat → Bool) (x y : Bool) :
    correction δ (misc z ^^ dot weights w m) α β b x y = (δ && b) := by
  have allZero (u : Z) : splitActive m L R S false (u, fun _ => false) := by
    intro i hi
    simp [splitClause]
  have base (u : Z) : misc u = false ∧ α = false ∧ β = false := by
    simpa [dot_zero] using (fiber_iff _ _ _).mp (h false _ (allZero u))
  have wc (i : Nat) (hi : i < m) : weights i = false := by
    obtain ⟨u, hu⟩ := canTurnOn i hi
    have active : splitActive m L R S false (u, fun j => decide (j=i)) := by
      intro j hj
      by_cases he : j=i
      · subst j
        simpa [splitClause] using hu
      · simp [splitClause, he]
    have hz := ((fiber_iff _ _ _).mp (h false _ active)).1
    simpa [dot_unit, hi, (base u).1] using hz
  simp [correction, dot_zero_weights weights w m wc, (base z).1, (base z).2.1, (base z).2.2]

theorem split_second_rule_iff_unsatisfiable {Z : Type} (m : Nat) (L R S : Nat → Z → Bool) :
    Valid (splitActive m L R S) true (fun _ => false) false false ↔
      ¬ ∃ z, original m L R S z := by
  rw [delta_valid_iff]
  constructor
  · rintro (h|none) ⟨z,hz⟩
    · contradiction
    · obtain ⟨w,hw⟩ := (split_projection m L R S z).mpr hz
      exact none (z,w) hw
  · intro none
    right
    rintro ⟨z,w⟩ hw
    exact none ⟨z,(split_projection m L R S z).mp ⟨w,hw⟩⟩

/-- For any Boolean context the origin and the individual unit vectors on its
b=0 slice suffice to eliminate all affine corrections except δ·b. -/
theorem radius_one_only_delta {m : Nat} {active : Bool → (Nat → Bool) → Prop}
    {δ constant α β : Bool} {weights : Nat → Bool}
    (zeroActive : active false (fun _ => false))
    (unitActive : ∀ i, i < m → active false (fun j => decide (j=i)))
    (h : Valid active δ (fun z => constant ^^ dot weights z m) α β)
    (b : Bool) (z : Nat → Bool) (x y : Bool) :
    correction δ (constant ^^ dot weights z m) α β b x y = (δ && b) := by
  have base : constant = false ∧ α = false ∧ β = false := by
    simpa [dot_zero] using (fiber_iff _ _ _).mp (h false _ zeroActive)
  have hz (i : Nat) (hi : i < m) : weights i = false := by
    have hh := ((fiber_iff _ _ _).mp (h false _ (unitActive i hi))).1
    simpa [base.1, dot_unit, hi] using hh
  simp [correction, dot_zero_weights weights z m hz, base.1, base.2.1, base.2.2]

/-- An all-negative proper ternary holds throughout the radius-two ball. -/
theorem negative_triple_on_two {I : Type} (v : I → Bool) {i j k a b : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (small : ∀ u, v u = true → u=a ∨ u=b) :
    ((!v i || !v j) || !v k) = true := by
  by_cases hi : v i = true
  · by_cases hj : v j = true
    · by_cases hk : v k = true
      · rcases small i hi with h|h <;> rcases small j hj with h'|h' <;>
          rcases small k hk with h''|h'' <;> simp_all
      · simp [hk]
    · simp [hj]
  · simp [hi]

/-- The width boundary. Any condition depending on at most k coordinates
which holds for every assignment supported on at most k coordinates holds
everywhere. In particular this applies to each clause of a width-three CNF. -/
theorem local_from_ball {I : Type} [DecidableEq I] (P : (I → Bool) → Prop)
    (vars : List I) (k : Nat) (arity : vars.length ≤ k)
    (locality : ∀ v w, (∀ i, i ∈ vars → v i = w i) → (P v ↔ P w))
    (ball : ∀ v, (∃ s : List I, s.length ≤ k ∧ ∀ i, v i = true → i ∈ s) → P v)
    (v : I → Bool) : P v := by
  let w : I → Bool := fun i => if i ∈ vars then v i else false
  apply (locality v w (fun i hi => by simp [w, hi])).mpr
  apply ball w
  refine ⟨vars, arity, ?_⟩
  intro i hi
  by_cases hm : i ∈ vars
  · exact hm
  · simp [w, hm] at hi

end GuardedAffineSubdivision
