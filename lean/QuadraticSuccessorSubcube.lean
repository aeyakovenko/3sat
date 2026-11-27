import Std

namespace QuadraticSuccessorSubcube

/-- The full evaluation table of a Boolean function, split on its first input. -/
inductive Table : Nat → Type where
  | leaf (value : Bool) : Table 0
  | split {n : Nat} (lo hi : Table n) : Table (n + 1)
deriving DecidableEq

def weight : {n : Nat} → Table n → Nat
  | 0, .leaf b => if b then 1 else 0
  | _ + 1, .split l r => weight l + weight r

def plus : {n : Nat} → Table n → Table n → Table n
  | 0, .leaf a, .leaf b => .leaf (a ^^ b)
  | _ + 1, .split a b, .split c d => .split (plus a c) (plus b d)

theorem plus_weight_le {n : Nat} (f g : Table n) :
    weight (plus f g) ≤ weight f + weight g := by
  induction f with
  | leaf a =>
    cases g with | leaf b => cases a <;> cases b <;> decide
  | split a b ia ib =>
    cases g with
    | split c d =>
      have ha := ia c
      have hb := ib d
      simp only [plus, weight]
      omega

theorem plus_weight_zero {n : Nat} (f g : Table n) (z : weight (plus f g) = 0) :
    f = g := by
  induction f with
  | leaf a =>
    cases g with | leaf b => cases a <;> cases b <;> simp_all [plus, weight]
  | split a b ia ib =>
    cases g with
    | split c d =>
      simp only [plus, weight] at z
      have za : weight (plus a c) = 0 := by omega
      have zb : weight (plus b d) = 0 := by omega
      rw [ia c za, ib d zb]

/-- In the multilinear representation f = lo + x (lo + hi). -/
def degreeLE : {n : Nat} → Nat → Table n → Prop
  | 0, _, .leaf _ => True
  | _ + 1, 0, .split l r => degreeLE 0 l ∧ l = r
  | _ + 1, d + 1, .split l r => degreeLE (d + 1) l ∧ degreeLE d (plus l r)

def constant : (n : Nat) → Bool → Table n
  | 0, b => .leaf b
  | n+1, b => .split (constant n b) (constant n b)

def both : {n : Nat} → Table n → Table n → Table n
  | 0, .leaf a, .leaf b => .leaf (a && b)
  | _ + 1, .split l r, .split u v => .split (both l u) (both r v)

private theorem congrTwo {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β}
    (ha : a = a') (hb : b = b') : f a b = f a' b' := by cases ha; cases hb; rfl

private theorem plus_self {n : Nat} (f : Table n) : plus f f = constant n false := by
  induction f with
  | leaf a => cases a <;> rfl
  | split l r il ir => simp only [plus, constant, il, ir]

private theorem plus_cancel {n : Nat} (f g : Table n) : plus f (plus f g) = g := by
  induction f with
  | leaf a => cases g with | leaf b => cases a <;> cases b <;> rfl
  | split l r il ir => cases g with | split u v => simp only [plus, il, ir]

private theorem plus_shuffle {n : Nat} (a b c e : Table n) :
    plus (plus a b) (plus c e) = plus (plus a c) (plus b e) := by
  induction a with
  | leaf a => cases b with | leaf b => cases c with | leaf c => cases e with
              | leaf e => cases a <;> cases b <;> cases c <;> cases e <;> rfl
  | split l r il ir =>
    cases b with | split u v => cases c with | split x y => cases e with
      | split z t => exact congrTwo Table.split (il u x z) (ir v y t)

theorem degree_constant (n d : Nat) (b : Bool) : degreeLE d (constant n b) := by
  induction n generalizing d b with
  | zero => trivial
  | succ n ih =>
    cases d with
    | zero => exact ⟨ih 0 b, rfl⟩
    | succ d =>
      refine ⟨ih _ b, ?_⟩
      change degreeLE d (plus (constant n b) (constant n b))
      rw [plus_self]
      exact ih d false

theorem degree_step {n d : Nat} (f : Table n) (hf : degreeLE d f) :
    degreeLE (d+1) f := by
  induction n generalizing d with
  | zero => cases f; trivial
  | succ n ih =>
    cases f with
    | split l r =>
      cases d with
      | zero =>
        obtain ⟨hl, hr⟩ := hf
        subst r
        exact ⟨ih l hl, by rw [plus_self]; exact degree_constant n 0 false⟩
      | succ d => exact ⟨ih l hf.1, ih (plus l r) hf.2⟩

theorem degree_sum {n d : Nat} (f g : Table n) (hf : degreeLE d f) (hg : degreeLE d g) :
    degreeLE d (plus f g) := by
  induction n generalizing d with
  | zero => cases f; cases g; trivial
  | succ n ih =>
    cases f with | split l r => cases g with
      | split u v =>
        cases d with
        | zero => exact ⟨ih l u hf.1 hg.1, congrTwo plus hf.2 hg.2⟩
        | succ d =>
          refine ⟨ih l u hf.1 hg.1, ?_⟩
          change degreeLE d (plus (plus l u) (plus r v))
          rw [plus_shuffle]
          exact ih (plus l r) (plus u v) hf.2 hg.2

private theorem degree_right {n d : Nat} (l r : Table n) (hf : degreeLE d (.split l r)) :
    degreeLE d r := by
  cases d with
  | zero => rw [← hf.2]; exact hf.1
  | succ d =>
    rw [← plus_cancel l r]
    exact degree_sum l (plus l r) hf.1 (degree_step (plus l r) hf.2)

private theorem both_left_distrib {n : Nat} (a b c : Table n) :
    plus (both a b) (both a c) = both a (plus b c) := by
  induction a with
  | leaf a => cases b with | leaf b => cases c with | leaf c => cases a <;> cases b <;> cases c <;> rfl
  | split l r il ir => cases b with | split x y => cases c with
      | split u v => exact congrTwo Table.split (il x u) (ir y v)

private theorem both_right_distrib {n : Nat} (a b c : Table n) :
    plus (both a c) (both b c) = both (plus a b) c := by
  induction a with
  | leaf a => cases b with | leaf b => cases c with | leaf c => cases a <;> cases b <;> cases c <;> rfl
  | split l r il ir => cases b with | split x y => cases c with
      | split u v => exact congrTwo Table.split (il x u) (ir y v)

private theorem both_derivative {n : Nat} (l r u v : Table n) :
    plus (both l u) (both r v) = plus (both l (plus u v)) (both (plus l r) v) := by
  induction l with
  | leaf a => cases r with | leaf b => cases u with | leaf c => cases v with
              | leaf e => cases a <;> cases b <;> cases c <;> cases e <;> rfl
  | split f g il ir =>
    cases r with | split a b => cases u with | split x y => cases v with
      | split z t => exact congrTwo Table.split (il a x z) (ir b y t)

theorem degree_product {n a b : Nat} (f g : Table n) (hf : degreeLE a f) (hg : degreeLE b g) :
    degreeLE (a+b) (both f g) := by
  induction n generalizing a b with
  | zero => cases f; cases g; trivial
  | succ n ih =>
    cases f with | split l r => cases g with
      | split u v =>
        cases a with
        | zero =>
          obtain ⟨hl, eq⟩ := hf
          subst r
          cases b with
          | zero =>
            obtain ⟨hu, eq⟩ := hg
            subst v
            exact ⟨ih l u hl hu, rfl⟩
          | succ b =>
            refine ⟨ih (a:=0) (b:=b+1) l u hl hg.1, ?_⟩
            change degreeLE (0+b) (plus (both l u) (both l v))
            rw [both_left_distrib]
            exact ih l (plus u v) hl hg.2
        | succ a =>
          cases b with
          | zero =>
            obtain ⟨hu, eq⟩ := hg
            subst v
            refine ⟨ih (a:=a+1) (b:=0) l u hf.1 hu, ?_⟩
            change degreeLE (a+0) (plus (both l u) (both r u))
            rw [both_right_distrib]
            exact ih (plus l r) u hf.2 hu
          | succ b =>
            refine ⟨ih (a:=a+1) (b:=b+1) l u hf.1 hg.1, ?_⟩
            change degreeLE (a+1+b) (plus (both l u) (both r v))
            rw [both_derivative]
            apply degree_sum
            · exact ih l (plus u v) hf.1 hg.2
            · have h := ih (plus l r) v hf.2 (degree_right u v hg)
              rwa [show a+(b+1) = a+1+b by omega] at h

/-- Every listed equality has an acceptance-table degree bound.
    Multiplying all of them adds their degree budgets. -/
def conjunction {n : Nat} : List (Table n × Nat) → Table n
  | [] => constant n true
  | (p, _) :: rest => both p (conjunction rest)

theorem degree_conjunction {n : Nat} (tests : List (Table n × Nat))
    (valid : ∀ t ∈ tests, degreeLE t.2 t.1) :
    degreeLE ((tests.map Prod.snd).sum) (conjunction tests) := by
  induction tests with
  | nil => exact degree_constant n 0 true
  | cons t rest ih =>
    rcases t with ⟨p,d⟩
    apply degree_product
    · exact valid (p, d) (by simp)
    · exact ih (fun t ht => valid t (by simp [ht]))

/-- The binary Reed–Muller weight bound including constant functions and d > n. -/
theorem minimum_weight {n d : Nat} (f : Table n) (deg : degreeLE d f)
    (nonzero : 0 < weight f) : 2 ^ n ≤ 2 ^ d * weight f := by
  induction n generalizing d with
  | zero =>
    cases f with
    | leaf b =>
      cases b <;> simp_all [weight, Nat.one_le_two_pow]
  | succ n ih =>
    cases f with
    | split l r =>
      simp only [weight] at nonzero ⊢
      cases d with
      | zero =>
        obtain ⟨hl, eq⟩ := deg
        subst r
        have h := ih l hl (by omega : 0 < weight l)
        simp only [Nat.pow_zero, Nat.one_mul] at h ⊢
        rw [Nat.pow_succ]
        omega
      | succ d =>
        obtain ⟨hl, hd⟩ := deg
        cases hz : weight (plus l r) with
        | zero =>
          have he := plus_weight_zero l r hz
          subst r
          have h := ih l hl (by omega : 0 < weight l)
          rw [Nat.mul_add, Nat.pow_succ 2 n]
          omega
        | succ k =>
          have h := ih (plus l r) hd (by omega : 0 < weight (plus l r))
          have bound := Nat.mul_le_mul_left (2 ^ d) (plus_weight_le l r)
          have scaled := Nat.mul_le_mul_right 2 (Nat.le_trans h bound)
          simpa only [Nat.pow_succ, Nat.mul_right_comm] using scaled

/-- Two simultaneous affine equalities can be represented by one quadratic bit. -/
theorem paired_equality (a b : Bool) : (!( (!a) && (!b) ) = false) ↔
    (a = false ∧ b = false) := by
  cases a <;> cases b <;> decide

/-- The exceptional-set budget is counted inside the chosen coordinate subcube. -/
theorem survivor_beyond_exception_count {n d : Nat} (f : Table n)
    (deg : degreeLE d f) (nonzero : 0 < weight f) (bad : Nat)
    (budget : 2 ^ d * bad < 2 ^ n) : bad < weight f := by
  have h := minimum_weight f deg nonzero
  exact Nat.lt_of_not_ge (fun smaller =>
    Nat.not_lt_of_ge (Nat.le_trans h (Nat.mul_le_mul_left _ smaller)) budget)

/-- Select arbitrary raw coordinates to keep free and fix the other bits. -/
inductive Face : Nat → Nat → Type where
  | empty : Face 0 0
  | fixL {n t : Nat} (f : Face n t) : Face (n+1) t
  | fixR {n t : Nat} (f : Face n t) : Face (n+1) t
  | keep {n t : Nat} (f : Face n t) : Face (n+1) (t+1)

def restrictFace : {n t : Nat} → Face n t → Table n → Table t
  | _, _, .empty, .leaf b => .leaf b
  | _, _, .fixL f, .split l _ => restrictFace f l
  | _, _, .fixR f, .split _ r => restrictFace f r
  | _, _, .keep f, .split l r => .split (restrictFace f l) (restrictFace f r)

private theorem face_sum {n t : Nat} (face : Face n t) (f g : Table n) :
    plus (restrictFace face f) (restrictFace face g) = restrictFace face (plus f g) := by
  induction face with
  | empty => cases f; cases g; rfl
  | fixL _ ih => cases f with | split l _ => cases g with | split u _ => exact ih l u
  | fixR _ ih => cases f with | split _ r => cases g with | split _ v => exact ih r v
  | keep _ ih => cases f with | split l r => cases g with
                  | split u v => exact congrTwo Table.split (ih l u) (ih r v)

theorem degree_face {n t d : Nat} (face : Face n t) (f : Table n) (valid : degreeLE d f) :
    degreeLE d (restrictFace face f) := by
  induction face generalizing d with
  | empty => cases f; trivial
  | fixL _ ih => cases f with
    | split l r =>
      cases d with
      | zero => exact ih l valid.1
      | succ d => exact ih l valid.1
  | fixR _ ih => cases f with | split l r => exact ih r (degree_right l r valid)
  | keep face ih =>
    cases f with
    | split l r =>
      cases d with
      | zero => exact ⟨ih l valid.1, congrArg (restrictFace face) valid.2⟩
      | succ d =>
        refine ⟨ih l valid.1, ?_⟩
        change degreeLE d (plus (restrictFace face l) (restrictFace face r))
        rw [face_sum]
        exact ih (plus l r) valid.2

/-- Local successor after excluding at most bad fillings on the specified raw subcube.
    A linear test costs one unit of the budget and a quadratic test costs two. -/
theorem local_successor_count {n t : Nat} (face : Face n t) (tests : List (Table n × Nat))
    (valid : ∀ v ∈ tests, degreeLE v.2 v.1) (bad : Nat)
    (seed : 0 < weight (restrictFace face (conjunction tests)))
    (budget : 2 ^ ((tests.map Prod.snd).sum) * bad < 2 ^ t) :
    bad < weight (restrictFace face (conjunction tests)) :=
  survivor_beyond_exception_count _ (degree_face face _ (degree_conjunction tests valid))
    seed bad budget

end QuadraticSuccessorSubcube
