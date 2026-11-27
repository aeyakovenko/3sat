import Std

/-! Restricting a scalar parity of selected carry bits costs at most one
affine equation per two carry positions. Rows are written most significant
first. The domain may already impose correlations on the operands. -/

namespace OneAdditionParity

def next (x y c : Bool) := if x ^^ y then c else x

theorem addition_carry (x y c : Bool) :
    next x y c = ((x && y) || (x && c) || (y && c)) := by decide +revert

/-- On the preferred branch the coefficient of the preceding carry vanishes. -/
theorem cancel_two (x y c b : Bool) (h : (x ^^ y) = b) :
    (next x y c ^^ (b && c)) = ((!b) && x) := by decide +revert

/-- On the other branch the coefficient of the preceding carry is one. -/
theorem keep_previous (x y c b : Bool) (h : (x ^^ y) ≠ b) :
    (next x y c ^^ (b && c)) = ((b && x) ^^ c) := by decide +revert

theorem xor_reassociate (a b c : Bool) : (a ^^ (b ^^ c)) = ((a ^^ b) ^^ c) := by decide +revert

structure Row (E : Type) where
  selected : Bool
  x : E → Bool
  y : E → Bool

def carry {E} : List (Row E) → E → Bool
  | [], _ => false
  | a :: rest, e => next (a.x e) (a.y e) (carry rest e)

def selectedParity {E} : List (Row E) → E → Bool
  | [], _ => false
  | a :: rest, e => (a.selected && carry (a :: rest) e) ^^ selectedParity rest e

def obeys {E : Type} : List ((E → Bool) × Bool) → E → Prop
  | [], _ => True
  | (f,b) :: cs, e => f e = b ∧ obeys cs e

structure Chart {E : Type} (A : (E → Bool) → Prop) (D : E → Prop) (rows : List (Row E)) where
  constraints : List ((E → Bool) × Bool)
  value : E → Bool
  cost : constraints.length ≤ (rows.length + 1) / 2
  valid : ∀ p ∈ constraints, A p.1
  affineValue : A value
  live : ∃ e, D e ∧ obeys constraints e
  correct : ∀ e, D e → obeys constraints e → selectedParity rows e = value e

/-- Choose A to be affine Boolean observables. Its use here only needs zero
and XOR closure. Each returned constraint and the resulting scalar value is
an observable. The common domain satisfying all equations is inhabited. -/
theorem live_chart {E : Type} (A : (E → Bool) → Prop)
    (zero : A (fun _ => false))
    (add : ∀ f g, A f → A g → A (fun e => f e ^^ g e))
    (D : E → Prop) (live : ∃ e, D e) (rows : List (Row E))
    (valid : ∀ a ∈ rows, A a.x ∧ A a.y) : Nonempty (Chart A D rows) := by
  classical
  have scalar (b : Bool) (f : E → Bool) (hf : A f) : A (fun e => b && f e) := by
    cases b <;> simp_all
  cases erows : rows with
  | nil =>
    exact ⟨⟨[], fun _ => false, by simp, by simp, zero,
       by obtain ⟨e, he⟩ := live; exact ⟨e,he,True.intro⟩, by intros; rfl⟩⟩
  | cons a rest =>
    have ha := valid a (by simp [erows])
    have tailValid : ∀ b ∈ rest, A b.x ∧ A b.y := fun b hb => valid b (by simp [erows,hb])
    cases top : a.selected with
    | false =>
      obtain ⟨c⟩ := live_chart A zero add D live rest tailValid
      refine ⟨⟨c.constraints, c.value, ?_, c.valid, c.affineValue, c.live, ?_⟩⟩
      · have := c.cost; simp; omega
      · intro e he hc; simpa [selectedParity,top] using c.correct e he hc
    | true =>
      let p := fun e => a.x e ^^ a.y e
      have hp : A p := add _ _ ha.1 ha.2
      cases erest : rest with
      | nil =>
        obtain ⟨u,hu⟩ := live
        refine ⟨⟨[(p,p u)], fun e => (!(p u)) && a.x e, by simp,
                  by simp [hp], scalar _ _ ha.1, ⟨u,hu,rfl,True.intro⟩, ?_⟩⟩
        intro e _ h
        have h' : (a.x e ^^ a.y e) = p u := h.1
        simp only [selectedParity, carry, top, Bool.true_and, Bool.xor_false]
        simpa using cancel_two (a.x e) (a.y e) false (p u) h'
      | cons b tail =>
        have vb := tailValid b (by simp [erest])
        have vt : ∀ d ∈ tail, A d.x ∧ A d.y := fun d hd => tailValid d (by simp [erest,hd])
        by_cases branch : ∃ e, D e ∧ p e = b.selected
        · obtain ⟨c⟩ := live_chart A zero add (fun e => D e ∧ p e = b.selected) branch tail vt
          refine ⟨⟨(p,b.selected) :: c.constraints,
                   fun e => ((!b.selected) && a.x e) ^^ c.value e, ?_, ?_,
                   add _ _ (scalar _ _ ha.1) c.affineValue, ?_, ?_⟩⟩
          · have := c.cost; simp; omega
          · intro pair hmem
            rcases List.mem_cons.mp hmem with h | h
            · subst pair; exact hp
            · exact c.valid pair h
          · obtain ⟨u,⟨hu,hs⟩,hh⟩ := c.live; exact ⟨u,hu,hs,hh⟩
          · intro e he held
            have eq := cancel_two (a.x e) (a.y e) (carry (b :: tail) e) b.selected held.1
            have out := c.correct e ⟨he,held.1⟩ held.2
            simp only [selectedParity, carry, top, Bool.true_and] at eq ⊢
            rw [xor_reassociate, eq, out]
        · let forced : Row E := { b with selected := true }
          have vf : ∀ d ∈ forced :: tail, A d.x ∧ A d.y := by
            intro d hd
            rcases List.mem_cons.mp hd with h | h
            · subst d; exact vb
            · exact vt _ h
          obtain ⟨c⟩ := live_chart A zero add D live (forced :: tail) vf
          refine ⟨⟨c.constraints, fun e => (b.selected && a.x e) ^^ c.value e, ?_,
                   c.valid, add _ _ (scalar _ _ ha.1) c.affineValue, c.live, ?_⟩⟩
          · have h := c.cost; simp at h ⊢; omega
          · intro e he held
            have neq : p e ≠ b.selected := fun eq => branch ⟨e,he,eq⟩
            have eq := keep_previous (a.x e) (a.y e) (carry (b :: tail) e) b.selected neq
            have out := c.correct e he held
            simp only [selectedParity, carry, top, forced, Bool.true_and] at eq out ⊢
            rw [xor_reassociate, eq, ← xor_reassociate, out]
termination_by rows.length
decreasing_by all_goals simp_wf; simp_all <;> omega


/-- The actual output parity of the indicated sum bits. The input at this
row is x XOR y XOR the carry from the less significant rows. -/
def sumParity {E} : List (Row E) → E → Bool
  | [], _ => false
  | a :: tail, e =>
      (a.selected && ((a.x e ^^ a.y e) ^^ carry tail e)) ^^ sumParity tail e

def inputPart {E} : List (Row E) → E → Bool
  | [], _ => false
  | a :: tail, e => (a.selected && (a.x e ^^ a.y e)) ^^ inputPart tail e

def carryPart {E} : List (Row E) → E → Bool
  | [], _ => false
  | a :: tail, e => (a.selected && carry tail e) ^^ carryPart tail e

def reflag {E} (hi : Bool) : List (Row E) → List (Row E)
  | [] => []
  | a :: tail => {a with selected := hi} :: reflag a.selected tail

theorem reflag_length {E} (hi) (rows : List (Row E)) : (reflag hi rows).length = rows.length := by
  induction rows generalizing hi with
  | nil => rfl
  | cons a tail ih => simp [reflag, ih]

theorem reflag_carry {E} (hi) (rows : List (Row E)) (e) : carry (reflag hi rows) e = carry rows e := by
  induction rows generalizing hi with
  | nil => rfl
  | cons a tail ih => simp [reflag,carry,ih]

theorem reflag_parity {E} (hi) (rows : List (Row E)) (e) :
    selectedParity (reflag hi rows) e = ((hi && carry rows e) ^^ carryPart rows e) := by
  induction rows generalizing hi with
  | nil => simp [reflag,selectedParity,carry,carryPart]
  | cons a tail ih => simp [reflag,selectedParity,carryPart,carry,reflag_carry,ih]

private theorem distribute (b p c h t : Bool) :
    ((b && (p ^^ c)) ^^ (h ^^ t)) = (((b && p) ^^ h) ^^ ((b && c) ^^ t)) := by
  decide +revert

theorem parts {E} (rows : List (Row E)) (e) :
    sumParity rows e = (inputPart rows e ^^ carryPart rows e) := by
  induction rows with
  | nil => rfl
  | cons a tail ih => simp only [sumParity,inputPart,carryPart,ih]; apply distribute

/-- Every scalar parity of the actual w-bit modular sum, plus any affine
offset, is affine on an inhabited restriction using at most floor(w/2)
equations in affine observables of the original domain. -/
theorem live_word_parity {E : Type} (A : (E → Bool) → Prop)
    (zero : A (fun _ => false))
    (add : ∀ f g, A f → A g → A (fun e => f e ^^ g e))
    (D : E → Prop) (live : ∃ e, D e) (rows : List (Row E))
    (valid : ∀ a ∈ rows, A a.x ∧ A a.y) (offset : E → Bool) (hoff : A offset) :
    ∃ (cs : List ((E → Bool) × Bool)) (f : E → Bool),
      cs.length ≤ rows.length / 2 ∧ (∀ p ∈ cs, A p.1) ∧ A f ∧
      (∃ e, D e ∧ obeys cs e) ∧
      (∀ e, D e → obeys cs e → (offset e ^^ sumParity rows e) = f e) := by
  have scalar (b : Bool) (f : E → Bool) (hf : A f) : A (fun e => b && f e) := by
    cases b <;> simp_all
  have linearPart (rs : List (Row E)) (hv : ∀ a ∈ rs, A a.x ∧ A a.y) : A (inputPart rs) := by
    induction rs with
    | nil => exact zero
    | cons a tail ih =>
      have ha := hv a (by simp)
      exact add _ _ (scalar a.selected _ (add _ _ ha.1 ha.2))
        (ih fun t ht => hv t (by simp [ht]))
  have reflagValid (hi) (rs : List (Row E)) (hv : ∀ a ∈ rs, A a.x ∧ A a.y) :
      ∀ a ∈ reflag hi rs, A a.x ∧ A a.y := by
    induction rs generalizing hi with
    | nil => simp [reflag]
    | cons a tail ih =>
      intro b hb
      rcases List.mem_cons.mp hb with hh | hh
      · subst b; exact hv a (by simp)
      · exact ih a.selected (fun t ht => hv t (by simp [ht])) b hh
  cases rows with
  | nil =>
    refine ⟨[],offset,by simp,by simp,hoff,?_,?_⟩
    · obtain ⟨e,h⟩ := live; exact ⟨e,h,True.intro⟩
    · simp [sumParity]
  | cons a tail =>
    let rs := reflag a.selected tail
    have hv := reflagValid a.selected tail (fun b hb => valid b (by simp [hb]))
    obtain ⟨ch⟩ := live_chart A zero add D live rs hv
    refine ⟨ch.constraints,fun e => offset e ^^ (inputPart (a :: tail) e ^^ ch.value e),
            ?_,ch.valid,add _ _ hoff (add _ _ (linearPart _ valid) ch.affineValue),ch.live,?_⟩
    · simpa [rs,reflag_length] using ch.cost
    · intro e he hc
      have eq := ch.correct e he hc
      rw [parts]
      change (offset e ^^ (inputPart (a :: tail) e ^^
        ((a.selected && carry tail e) ^^ carryPart tail e))) = _
      rw [← reflag_parity, eq]


/-- Interleave a product's two input bits with an all-zero row. Selecting
the latter output reads the product carry and the same row resets it. -/
def packed {E : Type} : List ((E → Bool) × (E → Bool)) → List (Row E)
  | [] => []
  | (x,y) :: tail => ⟨true,fun _ => false,fun _ => false⟩ :: ⟨false,x,y⟩ :: packed tail

def innerProduct {E : Type} : List ((E → Bool) × (E → Bool)) → E → Bool
  | [], _ => false
  | (x,y) :: tail, e => ((x e && y e) ^^ innerProduct tail e)

theorem packed_width {E} (pairs : List ((E → Bool) × (E → Bool))) :
    (packed pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair tail ih => rcases pair with ⟨x,y⟩; simp [packed,ih]; omega

theorem packed_reset {E} (pairs : List ((E → Bool) × (E → Bool))) (e) :
    carry (packed pairs) e = false := by
  cases pairs with
  | nil => rfl
  | cons pair tail => rcases pair with ⟨x,y⟩; rfl

theorem packed_exact {E} (pairs : List ((E → Bool) × (E → Bool))) (e) :
    sumParity (packed pairs) e = innerProduct pairs e := by
  induction pairs with
  | nil => rfl
  | cons pair tail ih =>
    rcases pair with ⟨x,y⟩
    have product_carry (u v : Bool) : next u v false = (u && v) := by decide +revert
    simp [packed,sumParity,carry,packed_reset,product_carry,ih,innerProduct]

#print axioms packed_exact

#print axioms live_word_parity
end OneAdditionParity
