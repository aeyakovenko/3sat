import Std

/-! A first-escape certificate for exact XOR/AND synthesis. Truth tables below
keep their constant bits. Constants can be included among the free tables. -/
namespace OneExtraGateClosure

abbrev Table (X : Type) := X → Bool
abbrev Family (X : Type) := Table X → Prop

def zero {X : Type} : Table X := fun _ => false
def add {X : Type} (a b : Table X) : Table X := fun x => xor (a x) (b x)
def mul {X : Type} (a b : Table X) : Table X := fun x => a x && b x
def Le {X : Type} (U W : Family X) := ∀ ⦃a⦄, U a → W a

structure Space {X : Type} (W : Family X) : Prop where
  hasZero : W zero
  plus : ∀ ⦃a b⦄, W a → W b → W (add a b)

/-- Linear span after adjoining one binary vector to an existing space. -/
def Adjoin {X : Type} (W : Family X) (h : Table X) : Family X :=
  fun v => W v ∨ ∃ w, W w ∧ v = add w h

private theorem zero_add {X : Type} (b : Table X) : add zero b = b := by
  funext x
  simp [add, zero]

private theorem adjoin_has {X : Type} {U : Family X} (hU : U zero) (h : Table X) :
    Adjoin U h h := Or.inr ⟨zero, hU, (zero_add h).symm⟩

/-- A growing gate span. Affine XOR combinations of earlier wires are free
when U is a linear space containing the constant-one table. -/
inductive Chain {X : Type} (U : Family X) : Family X → Prop where
  | start : Chain U U
  | gate {V : Family X} (prev : Chain U V) {a b : Table X}
      (left : V a) (right : V b) : Chain U (Adjoin V (mul a b))

/-- Least family closed under XOR, with AND allowed only for products that
belong to the indicated ambient family. -/
inductive Reach {X : Type} (U W : Family X) : Family X where
  | base {v} (h : U v) : Reach U W v
  | plus {a b} (left : Reach U W a) (right : Reach U W b) : Reach U W (add a b)
  | prod {a b} (left : Reach U W a) (right : Reach U W b)
      (legal : W (mul a b)) : Reach U W (mul a b)

theorem reach_inside {X : Type} {U W : Family X} (input : Le U W)
    (space : Space W) : Le (Reach U W) W := by
  intro v hv
  induction hv with
  | base h => exact input h
  | plus _ _ a b => exact space.plus a b
  | prod _ _ legal _ _ => exact legal

private theorem chain_zero {X : Type} {U V : Family X} (c : Chain U V)
    (hz : U zero) : V zero := by
  induction c with
  | start => exact hz
  | gate _ _ _ ih => exact Or.inl ih

/-- If a completed chain goes outside W, there is a gate OUTSIDE W whose
operands are both reachable while staying INSIDE W. Otherwise every completed
wire is already in the restricted closure. -/
theorem first_escape {X : Type} {U V W : Family X} (c : Chain U V)
    (hz : U zero) :
    Le V (Reach U W) ∨ ∃ a b, Reach U W a ∧ Reach U W b ∧
                              V (mul a b) ∧ ¬ W (mul a b) := by
  induction c with
  | start => exact Or.inl (fun {_} h => .base h)
  | @gate S prev a b left right ih =>
    rcases ih with old | ⟨f,g,hf,hg,hprod,hout⟩
    · by_cases hin : W (mul a b)
      · apply Or.inl
        intro z hz'
        rcases hz' with h | ⟨w, hw, rfl⟩
        · exact old h
        · exact .plus (old hw) (.prod (old left) (old right) hin)
      · exact Or.inr ⟨a, b, old left, old right, adjoin_has (chain_zero prev hz) _, hin⟩
    · exact Or.inr ⟨f, g, hf, hg, Or.inl hprod, hout⟩

/-- Over F₂ a vector in the unique exterior coset can replace any other
representative of that coset. -/
theorem exchange {X : Type} {V W : Family X} (space : Space W) {r h : Table X}
    (one : Le V (Adjoin W r)) (hh : V h) (outside : ¬W h) : Le V (Adjoin W h) := by
  rcases one hh with hw | ⟨a, ha, eq⟩
  · exact (outside hw).elim
  intro v hv
  rcases one hv with hw | ⟨b, hb, hv⟩
  · exact Or.inl hw
  · refine Or.inr ⟨add b a, space.plus hb ha, ?_⟩
    rw [hv, eq]
    funext x
    cases b x <;> cases ha : a x <;> cases hr : r x <;> simp [add, ha, hr]

def restrict {X Y : Type} (e : Y → X) (t : Table X) : Table Y := fun y => t (e y)

def Image {X Y : Type} (e : Y → X) (W : Family X) : Family Y :=
  fun v => ∃ w, W w ∧ restrict e w = v

private theorem image_plus {X Y : Type} {W : Family X} (space : Space W)
    {e : Y → X} {a b : Table Y} (ha : Image e W a) (hb : Image e W b) :
    Image e W (add a b) := by
  obtain ⟨f,hf,rfl⟩ := ha
  obtain ⟨g,hg,rfl⟩ := hb
  exact ⟨add f g, space.plus hf hg, rfl⟩

/-- Restricting all gates of an arbitrary chain is sound whenever its free
inputs are supplied and every restricted gate lies in the new ambient
space. The restriction can be any map on input points, including a fiber. -/
theorem restrict_chain {X Y : Type} {U V : Family X} {P T : Family Y}
    (c : Chain U V) (hz : U zero) (e : Y → X)
    (base : ∀ ⦃f⦄, U f → P (restrict e f))
    (ambient : ∀ ⦃f⦄, V f → T (restrict e f)) :
    ∀ ⦃f⦄, V f → Reach P T (restrict e f) := by
  induction c with
  | start => exact fun {_} h => .base (base h)
  | @gate S prev a b left right ih =>
    have old : ∀ ⦃f⦄, S f → Reach P T (restrict e f) := ih (fun {_} h => ambient (Or.inl h))
    have product : Reach P T (restrict e (mul a b)) :=
      .prod (old left) (old right) (ambient (adjoin_has (chain_zero prev hz) _))
    intro f hf
    rcases hf with h | ⟨w,hw,rfl⟩
    · exact old h
    · exact .plus (old hw) product

/-- The exterior product collapses on a restriction when it becomes an
image of any W-vector. In that case the restricted closure already reaches
every target. The entire restricted prefix is granted for free. -/
theorem collapse {X Y : Type} {U V W : Family X} (c : Chain U V)
    (hz : U zero) (space : Space W) (cover : Le W V)
    {h : Table X} (one : Le V (Adjoin W h)) (e : Y → X)
    (lost : Image e W (restrict e h)) :
    ∀ ⦃f⦄, W f → Reach (Image e (Reach U W)) (Image e W) (restrict e f) := by
  apply fun f hf => restrict_chain c hz e (fun {g} hg => ⟨g, .base hg, rfl⟩) ?_ (cover hf)
  intro f hf
  rcases one hf with hw | ⟨w,hw,rfl⟩
  · exact ⟨f, hw, rfl⟩
  · exact image_plus space ⟨w, hw, rfl⟩ lost

def fiber {X : Type} (a : Table X) (c : Bool) := {x : X // a x = c}

def Pass {X : Type} (U W : Family X) (a : Table X) : Prop :=
  ∀ c : Bool, ∀ ⦃f⦄, W f →
    Reach (Image (Subtype.val : fiber a c → X) (Reach U W))
      (Image (Subtype.val : fiber a c → X) W) (restrict Subtype.val f)

/-- Fiber sieve before choosing the first exterior AND. A qualifying factor,
the second factor, and their XOR must pass on BOTH fibers. -/
theorem three_factors_pass {X : Type} {U V W : Family X} (chain : Chain U V)
    (hz : U zero) (space : Space W) (cover : Le W V) {a b : Table X}
    (ha : W a) (hb : W b) (one : Le V (Adjoin W (mul a b))) :
    Pass U W a ∧ Pass U W b ∧ Pass U W (add a b) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro c
  · apply collapse chain hz space cover one Subtype.val
    cases c
    · refine ⟨zero, space.hasZero, ?_⟩
      funext x
      simp [restrict, zero, mul, x.property]
    · refine ⟨b, hb, ?_⟩
      funext x
      simp [restrict, mul, x.property]
  · apply collapse chain hz space cover one Subtype.val
    cases c
    · refine ⟨zero, space.hasZero, ?_⟩
      funext x
      simp [restrict, zero, mul, x.property]
    · refine ⟨a, ha, ?_⟩
      funext x
      simp [restrict, mul, x.property]
  · apply collapse chain hz space cover one Subtype.val
    cases c
    · refine ⟨a, ha, ?_⟩
      funext x
      have h := x.property
      cases h₁ : a x.val <;> cases h₂ : b x.val <;> simp_all [add, restrict, mul]
    · refine ⟨zero, space.hasZero, ?_⟩
      funext x
      have h := x.property
      cases h₁ : a x.val <;> cases h₂ : b x.val <;> simp_all [add, restrict, zero, mul]

/-- End-to-end candidate necessity, with the one-exterior-coset hypothesis
explicit. If an actual successful chain uses that budget but cannot attain
its targets inside W, the first-escape search plus its fiber sieve must
retain some product. Consequently failure of every candidate is a sound
lower-bound certificate. No numerical ranks or enumeration outcomes are
assumed by this theorem. -/
theorem candidate_necessary {X : Type} {U W V : Family X} (chain : Chain U V)
    (hz : U zero) (initial : Le U W) (space : Space W) (cover : Le W V)
    (insufficient : ¬ Le W (Reach U W)) (budget : ∃ r, Le V (Adjoin W r)) :
    ∃ a b, Reach U W a ∧ Reach U W b ∧ ¬W (mul a b) ∧
      Pass U W a ∧ Pass U W b ∧ Pass U W (add a b) ∧
      Le W (Reach U (Adjoin W (mul a b))) := by
  obtain ⟨r, hr⟩ := budget
  rcases first_escape chain hz with old | ⟨a,b,ha,hb,hprod,outside⟩
  · exact (insufficient (fun {_} h => old (cover h))).elim
  · let H := Adjoin W (mul a b)
    have ambient : Le V H := exchange space hr hprod outside
    obtain ⟨sa,sb,sab⟩ := three_factors_pass chain hz space cover
      (reach_inside initial space ha) (reach_inside initial space hb) ambient
    refine ⟨a, b, ha, hb, outside, sa, sb, sab, ?_⟩
    intro f hf
    exact restrict_chain (P := U) (T := H) chain hz id (fun {_} h => h)
      (fun {_} h => ambient h) (cover hf)

/-! Finite gate budgets imply the one-coset hypothesis used above. The free
and target spaces may be given by exact lists of truth tables. -/

private theorem plus_shift {X : Type} (a b c : Table X) :
    add a (add b c) = add (add a b) c := by
  funext x
  cases ha : a x <;> cases hb : b x <;> cases hc : c x <;> simp [add, ha, hb, hc]

private theorem shift_plus {X : Type} (a b c : Table X) :
    add (add a c) b = add (add a b) c := by
  funext x
  cases ha : a x <;> cases hb : b x <;> cases hc : c x <;> simp [add, ha, hb, hc]

private theorem shifts_cancel {X : Type} (a b c : Table X) :
    add (add a c) (add b c) = add a b := by
  funext x
  cases ha : a x <;> cases hb : b x <;> cases hc : c x <;> simp [add, ha, hb, hc]

private theorem unshift {X : Type} (a r : Table X) : add a (add a r) = r := by
  funext x
  cases ha : a x <;> cases hr : r x <;> simp [add, ha, hr]

private theorem shift_inj {X : Type} (r : Table X) {a b : Table X}
    (h : add a r = add b r) : a = b := by
  funext x
  have hx := congrFun h x
  cases ha : a x <;> cases hb : b x <;> cases hr : r x <;> simp_all [add]

private theorem adjoin_space {X : Type} {V : Family X} (space : Space V) (r : Table X) :
    Space (Adjoin V r) := by
  refine ⟨Or.inl space.hasZero, ?_⟩
  intro a b ha hb
  rcases ha with ha | ⟨a,ha,rfl⟩ <;> rcases hb with hb | ⟨b,hb,rfl⟩
  · exact Or.inl (space.plus ha hb)
  · exact Or.inr ⟨_, space.plus ha hb, plus_shift ..⟩
  · exact Or.inr ⟨_, space.plus ha hb, shift_plus ..⟩
  · apply Or.inl
    rw [shifts_cancel]
    exact space.plus ha hb

theorem chain_space {X : Type} {U V : Family X} (c : Chain U V)
    (free : Space U) : Space V := by
  induction c with
  | start => exact free
  | gate _ _ _ ih => exact adjoin_space ih _

def Doubled {X : Type} (l : List (Table X)) (r : Table X) : List (Table X) :=
  l ++ l.map (fun b => add b r)

private theorem doubled_enum {X : Type} {W : Family X} {l : List (Table X)}
    (enum : ∀ x, x ∈ l ↔ W x) (r x : Table X) : x ∈ Doubled l r ↔ Adjoin W r x := by
  simp only [Doubled, List.mem_append, List.mem_map, Adjoin, enum]
  constructor
  · rintro (h | ⟨a,ha,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a,ha,h.symm⟩
  · rintro (h | ⟨a,ha,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a,ha,h.symm⟩

private theorem shifted_nodup {X : Type} {l : List (Table X)} (nd : l.Nodup) (r : Table X) :
    (l.map (fun a => add a r)).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp nd
    apply List.nodup_cons.mpr
    refine ⟨?_, ih tail⟩
    intro h
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp h
    exact fresh ((shift_inj r eq) ▸ hb)

private theorem doubled_nodup {X : Type} {W : Family X} (space : Space W)
    {l : List (Table X)} (enum : ∀ x, x ∈ l ↔ W x) (nd : l.Nodup)
    {r : Table X} (outside : ¬W r) : (Doubled l r).Nodup := by
  apply List.pairwise_append.mpr
  refine ⟨nd, shifted_nodup nd r, ?_⟩
  intro a ha b hb eq
  obtain ⟨v,hv,shift⟩ := List.mem_map.mp hb
  have back : W (add v (add v r)) := space.plus ((enum v).mp hv)
    ((shift.trans eq.symm).symm ▸ ((enum a).mp ha))
  exact outside ((unshift v r) ▸ back)

private theorem length_of_subset {A : Type} (l t : List A) (nd : l.Nodup)
    (inside : ∀ x ∈ l, x ∈ t) : l.length ≤ t.length := by
  classical
  induction l generalizing t with
  | nil => simp
  | cons x l ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp nd
    have xt : x ∈ t := inside x (by simp)
    have pos := List.length_pos_of_mem xt
    have bound := ih (t.erase x) tail (by
      intro y hy
      have ne : y ≠ x := fun eq => fresh (eq ▸ hy)
      exact (List.mem_erase_of_ne ne).mpr (inside y (by simp [hy])))
    rw [List.length_erase_of_mem xt] at bound
    simp
    omega

/-- If a finite space V covers W and has at most twice as many members,
then V is contained in W plus a single coset. An over-enumeration of V,
including repetitions, suffices for the upper bound. -/
theorem one_coset_of_size {X : Type} {W V : Family X} (wsp : Space W) (vsp : Space V)
    (cover : Le W V) (ws vs : List (Table X)) (enum : ∀ x, x ∈ ws ↔ W x)
    (distinct : ws.Nodup) (complete : ∀ ⦃x⦄, V x → x ∈ vs)
    (budget : vs.length ≤ 2 * ws.length) : ∃ r, Le V (Adjoin W r) := by
  by_cases included : Le V W
  · exact ⟨zero, fun {_} h => Or.inl (included h)⟩
  · have ex : ∃ r, V r ∧ ¬W r := by
      apply Classical.byContradiction
      intro no
      exact included (fun {r} hr => Classical.byContradiction (fun absent => no ⟨r,hr,absent⟩))
    obtain ⟨r,hr,outside⟩ := ex
    refine ⟨r, ?_⟩
    intro x hx
    apply Classical.byContradiction
    intro miss
    have notIn : x ∉ Doubled ws r := fun hi => miss ((doubled_enum enum r x).mp hi)
    have ds := List.nodup_cons.mpr ⟨notIn, doubled_nodup wsp enum distinct outside⟩
    have bound := length_of_subset (x :: Doubled ws r) vs ds (by
      intro w hw
      apply complete
      rcases List.mem_cons.mp hw with same | inD
      · exact same ▸ hx
      · rcases (doubled_enum enum r w).mp inD with h | ⟨p,hp,rfl⟩
        · exact cover h
        · exact vsp.plus (cover hp) hr)
    simp only [Doubled, List.length_cons, List.length_append, List.length_map] at bound
    omega

/-- The number of AND gates is now recorded on the span chain. -/
inductive Counted {X : Type} (U : Family X) : Nat → Family X → Prop where
  | start : Counted U 0 U
  | gate {k : Nat} {V : Family X} (prev : Counted U k V) {a b : Table X}
      (left : V a) (right : V b) : Counted U (k + 1) (Adjoin V (mul a b))

private theorem forget_count {X : Type} {U V : Family X} {k : Nat} (c : Counted U k V) :
    Chain U V := by
  induction c with
  | start => exact .start
  | gate _ left right ih => exact .gate ih left right

private theorem enumerate_chain {X : Type} {U V : Family X} {k : Nat} (c : Counted U k V)
    (us : List (Table X)) (free : ∀ x, x ∈ us ↔ U x) :
    ∃ vs : List (Table X), vs.length = 2^k * us.length ∧ ∀ x, x ∈ vs ↔ V x := by
  induction c with
  | start => exact ⟨us, by simp, free⟩
  | @gate k V prev a b left right ih =>
    obtain ⟨t, size, enum⟩ := ih
    refine ⟨Doubled t (mul a b), ?_, doubled_enum enum _⟩
    simp only [Doubled, List.length_append, List.length_map, size, Nat.pow_succ]
    rw [Nat.mul_right_comm, Nat.mul_two]

/-- A complete finite certificate principle, requiring only free/target
enumerations and the actual k-gate chain. The numerical gate budget guarantees
the one-coset hypothesis: 2^k |U| ≤ 2 |W|. -/
theorem candidate_of_gate_count {X : Type} {U W V : Family X} {k : Nat} (c : Counted U k V)
    (usp : Space U) (initial : Le U W) (wsp : Space W) (cover : Le W V)
    (insufficient : ¬ Le W (Reach U W)) (us ws : List (Table X))
    (free : ∀ x, x ∈ us ↔ U x) (target : ∀ x, x ∈ ws ↔ W x) (distinct : ws.Nodup)
    (budget : 2^k * us.length ≤ 2 * ws.length) :
    ∃ a b, Reach U W a ∧ Reach U W b ∧ ¬W (mul a b) ∧
      Pass U W a ∧ Pass U W b ∧ Pass U W (add a b) ∧
      Le W (Reach U (Adjoin W (mul a b))) := by
  obtain ⟨vs,size,enum⟩ := enumerate_chain c us free
  have chain := forget_count c
  apply candidate_necessary chain usp.hasZero initial wsp cover insufficient
  exact one_coset_of_size wsp (chain_space chain usp) cover ws vs target distinct
    (fun {x} hx => (enum x).mpr hx) (size ▸ budget)

end OneExtraGateClosure
