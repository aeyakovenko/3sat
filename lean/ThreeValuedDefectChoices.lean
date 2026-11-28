import Std

namespace ThreeValuedDefectChoices

def twoOf (p q r : Prop) : Prop := (p ∧ q) ∨ (p ∧ r) ∨ (q ∧ r)

/-- For majority-closed solutions, realizing every pair of requested literal
values suffices to realize them all. Empty requests need a nonempty base. -/
theorem extend_pairs {A L : Type} (allowed : A → Prop) (holds : L → A → Prop)
    (merge : A → A → A → A)
    (closed : ∀ a b c, allowed a → allowed b → allowed c → allowed (merge a b c))
    (preserve : ∀ p a b c, twoOf (holds p a) (holds p b) (holds p c) →
      holds p (merge a b c))
    (requests : List L) (base : ∃ a, allowed a)
    (pairs : ∀ p ∈ requests, ∀ q ∈ requests,
      ∃ a, allowed a ∧ holds p a ∧ holds q a) :
    ∃ a, allowed a ∧ ∀ p ∈ requests, holds p a := by
  have grow (t : List L) (sub : ∀ p ∈ t, p ∈ requests) :
      ∀ q ∈ requests, ∃ a, allowed a ∧ holds q a ∧ ∀ p ∈ t, holds p a := by
    induction t with
    | nil =>
      intro q hq
      obtain ⟨a, ha, h, _⟩ := pairs q hq q hq
      exact ⟨a, ha, h, by simp⟩
    | cons p t ih =>
      have hp : p ∈ requests := sub p (by simp)
      have st : ∀ j ∈ t, j ∈ requests := fun j hj => sub j (List.mem_cons_of_mem _ hj)
      intro q hq
      obtain ⟨a, ha, pa, ta⟩ := ih st p hp
      obtain ⟨b, hb, qb, tb⟩ := ih st q hq
      obtain ⟨c, hc, pc, qc⟩ := pairs p hp q hq
      refine ⟨merge a b c, closed _ _ _ ha hb hc, preserve _ _ _ _ (Or.inr (Or.inr ⟨qb,qc⟩)), ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | h
      · exact preserve _ _ _ _ (Or.inr (Or.inl ⟨pa,pc⟩))
      · exact preserve _ _ _ _ (Or.inl ⟨ta j h,tb j h⟩)
  cases requests with
  | nil =>
    obtain ⟨a, ha⟩ := base
    exact ⟨a,ha,by simp⟩
  | cons q t =>
    obtain ⟨a,ha,_,rest⟩ := grow (q::t) (fun _ h => h) q (by simp)
    exact ⟨a,ha,rest⟩

def majority (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem literal_majority : ∀ sign a b c : Bool,
    twoOf (a = sign) (b = sign) (c = sign) → majority a b c = sign := by
  unfold twoOf
  decide

/-- Each disjunction of two literals is majority closed, including repeated
literals. The two columns below are the literal values on three assignments. -/
theorem binary_majority : ∀ a b c d e f : Bool,
    (a || d) = true → (b || e) = true → (c || f) = true →
    (majority a b c || majority d e f) = true := by decide

theorem signed_majority : ∀ sign a b c : Bool,
    (majority a b c == sign) = majority (a == sign) (b == sign) (c == sign) := by decide

abbrev Lit (V : Type) := V × Bool

def eval {V : Type} (z : V → Bool) (p : Lit V) : Bool := z p.1 == p.2

def models {V : Type} (base : List (Lit V × Lit V)) (z : V → Bool) : Prop :=
  ∀ cl ∈ base, (eval z cl.1 || eval z cl.2) = true

/-- A satisfiable 2-CNF extends jointly requested literals precisely when
each (possibly equal) pair of them extends to a model. -/
theorem binary_extension {V : Type} (base : List (Lit V × Lit V))
    (nonempty : ∃ z, models base z) (req : List (Lit V)) :
    (∃ z, models base z ∧ ∀ l ∈ req, z l.1 = l.2) ↔
    (∀ p ∈ req, ∀ q ∈ req, ∃ z, models base z ∧ z p.1 = p.2 ∧ z q.1 = q.2) := by
  constructor
  · rintro ⟨z,h,all⟩ p hp q hq
    exact ⟨z,h,all p hp,all q hq⟩
  · intro pairs
    apply extend_pairs (models base) (fun (p : Lit V) (z : V → Bool) => z p.1 = p.2)
      (fun a b c i => majority (a i) (b i) (c i)) _ _ req nonempty pairs
    · intro a b c ha hb hc cl hcl
      simpa only [eval,signed_majority] using
        (binary_majority _ _ _ _ _ _ (ha cl hcl) (hb cl hcl) (hc cl hcl))
    · intro p a b c h
      exact literal_majority _ _ _ _ h

/-- The reverse reduction has three complemented values for each choice.
At least one of the bits is zero and binary conflicts prohibit two
incompatible zeros. Any such partial choice restricts to one value per group. -/
theorem choose_zeros {I : Type} (bad : I → Fin 3 → I → Fin 3 → Prop) :
    (∃ z : I → Fin 3 → Bool, (∀ i, ∃ a, z i a = false) ∧
      ∀ i a j b, bad i a j b → z i a = true ∨ z j b = true) ↔
    (∃ f : I → Fin 3, ∀ i j, ¬bad i (f i) j (f j)) := by
  classical
  constructor
  · rintro ⟨z,existsZero,legal⟩
    let f i := Classical.choose (existsZero i)
    have hf i : z i (f i) = false := Classical.choose_spec (existsZero i)
    refine ⟨f,fun i j hbad => ?_⟩
    have h := legal i (f i) j (f j) hbad
    simp [hf] at h
  · rintro ⟨f,hf⟩
    refine ⟨fun i a => decide (a ≠ f i), ?_, ?_⟩
    · exact fun i => ⟨f i, by simp⟩
    · intro i a j b hb
      by_cases hi : a = f i
      · subst a
        by_cases hj : b = f j
        · subst b
          exact False.elim (hf i j hb)
        · exact Or.inr (by simp [hj])
      · exact Or.inl (by simp [hi])

end ThreeValuedDefectChoices
