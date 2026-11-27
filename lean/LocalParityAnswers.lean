import Std

namespace LocalParityAnswers

abbrev Partial (Var : Type) := Var → Option Bool

def Extends (p r : Partial Var) : Prop :=
  ∀ v b, p v = some b → r v = some b

def Matches (p : Partial Var) (x : Var → Bool) : Prop :=
  ∀ v b, p v = some b → x v = b

def Covered (p : Partial Var) (scope : List Var) : Prop :=
  ∀ v, v ∈ scope → ∃ b, p v = some b

def complete (p : Partial Var) (v : Var) : Bool := (p v).getD false

theorem matchesComplete (p : Partial Var) : Matches p (complete p) := by
  intro v b hv
  simp [complete, hv]

/-- The step index counts queries (a repeated query may leave the partial
assignment unchanged). A defended partial state need not extend to a
global satisfying assignment. -/
structure Defense (scope : Clause → List Var) (holds : Clause → (Var → Bool) → Prop)
    (budget : Nat) where
  admitted : Nat → Partial Var → Prop
  start : admitted 0 (fun _ => none)
  respond : ∀ n p, n < budget → admitted n p → ∀ v,
    ∃ b r, admitted (n+1) r ∧ Extends p r ∧ r v = some b
  entireScope : ∀ n p c x, admitted n p → Covered p (scope c) → Matches p x → holds c x

variable {Var Clause : Type} {scope : Clause → List Var}
  {holds : Clause → (Var → Bool) → Prop} {budget q : Nat}

theorem expose (d : Defense scope holds budget) (vars : List Var)
    (n : Nat) (p : Partial Var) (allowed : d.admitted n p) (room : n+vars.length ≤ budget) :
    ∃ r, d.admitted (n+vars.length) r ∧ Extends p r ∧ Covered r vars := by
  induction vars generalizing n p with
  | nil => exact ⟨p, allowed, fun _ _ h => h, fun _ h => by cases h⟩
  | cons v vs ih =>
    simp only [List.length_cons] at room ⊢
    obtain ⟨b, q, hq, pq, answered⟩ := d.respond n p (by omega) allowed v
    obtain ⟨r, hr, qr, covered⟩ := ih (n+1) q hq (by omega)
    rw [show n + (vs.length+1) = (n+1) + vs.length by omega]
    refine ⟨r, hr, fun a z h => qr a z (pq a z h), ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with same | tail
    · subst a
      exact ⟨b, qr v b answered⟩
    · exact covered a tail

inductive Selector (Var Clause : Type) where
  | answer (clause : Clause)
  | ask (v : Var) (ifFalse ifTrue : Selector Var Clause)

def run (x : Var → Bool) : Selector Var Clause → Clause
  | .answer c => c
  | .ask v left right => if x v then run x right else run x left

def depth : Selector Var Clause → Nat
  | .answer _ => 0
  | .ask _ left right => max (depth left) (depth right) + 1

/-- Defend an adaptive tree from an arbitrary admitted restriction. At the
leaf, expose every variable of the *selected* output clause before filling
unqueried coordinates. No uniform or computable adversary is required. -/
theorem surviveFrom (d : Defense scope holds budget) (tree : Selector Var Clause)
    (width : Nat) (scopeBound : ∀ c, (scope c).length ≤ width)
    (n : Nat) (p : Partial Var) (allowed : d.admitted n p)
    (room : n + depth tree + width ≤ budget) :
    ∃ x, Matches p x ∧ holds (run x tree) x := by
  induction tree generalizing n p with
  | answer c =>
    simp only [depth, Nat.add_zero] at room
    obtain ⟨r, hr, pr, covered⟩ := expose d (scope c) n p allowed (by have := scopeBound c; omega)
    exact ⟨complete r, fun a b h => matchesComplete r a b (pr a b h),
      d.entireScope _ _ _ _ hr covered (matchesComplete r)⟩
  | ask v left right ihL ihR =>
    simp only [depth] at room
    obtain ⟨b, q, hq, pq, ans⟩ := d.respond n p (by omega) allowed v
    cases b with
    | false =>
      have hl := Nat.le_max_left (depth left) (depth right)
      obtain ⟨x, mx, good⟩ := ihL (n+1) q hq (by omega)
      exact ⟨x, fun a z h => mx a z (pq a z h), by simpa [run, mx v false ans] using good⟩
    | true =>
      have hr := Nat.le_max_right (depth left) (depth right)
      obtain ⟨x, mx, good⟩ := ihR (n+1) q hq (by omega)
      exact ⟨x, fun a z h => mx a z (pq a z h), by simpa [run, mx v true ans] using good⟩

theorem threeMoreQueries (d : Defense scope holds (q+3)) (tree : Selector Var Clause)
    (time : depth tree ≤ q) (arity : ∀ c, (scope c).length ≤ 3) :
    ∃ x, holds (run x tree) x := by
  obtain ⟨x, _, result⟩ := surviveFrom d tree 3 arity 0 _ d.start (by omega)
  exact ⟨x, result⟩

abbrev Vector (ι : Type) := ι → Bool

def plus (x y : Vector ι) : Vector ι := fun i => x i ^^ y i

def zeroVec : Vector ι := fun _ => false

private theorem plusComm (x y : Vector ι) : plus x y = plus y x := by
  funext i
  exact Bool.xor_comm _ _

private theorem plusAssoc (x y z : Vector ι) : plus (plus x y) z = plus x (plus y z) := by
  funext i
  exact Bool.xor_assoc _ _ _

private theorem leftCancel (x y : Vector ι) : plus x (plus x y) = y := by
  funext i
  change (x i ^^ (x i ^^ y i)) = y i
  rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

private theorem shiftCancel (x y v : Vector ι) : plus (plus x v) (plus y v) = plus x y := by
  funext i
  change ((x i ^^ v i) ^^ (y i ^^ v i)) = (x i ^^ y i)
  cases x i <;> cases y i <;> cases v i <;> rfl

/-- The span after adjoining v is the union of the old subspace and
its translate by v. -/
def oneSpan (S : Vector ι → Prop) (v x : Vector ι) : Prop := S x ∨ S (plus x v)

/-- For an independent direction v, either prescribed parity answer admits
a linear extension on the enlarged span. Values outside that span are free.
The old map is supplied as a total function whose laws are only required
on S. -/
theorem extendIndependent {ι : Type} (S : Vector ι → Prop) (φ : Vector ι → Bool)
    (v : Vector ι) (answer : Bool) (independent : ¬ S v)
    (sumClosed : ∀ x y, S x → S y → S (plus x y))
    (atZero : φ zeroVec = false)
    (linear : ∀ x y, S x → S y → φ (plus x y) = (φ x ^^ φ y)) :
    ∃ ψ : Vector ι → Bool,
      (∀ x, S x → ψ x = φ x) ∧ ψ v = answer ∧
      ∀ x y, oneSpan S v x → oneSpan S v y → ψ (plus x y) = (ψ x ^^ ψ y) := by
  classical
  let ψ (x : Vector ι) := if S x then φ x else φ (plus x v) ^^ answer
  have self : plus v v = zeroVec := by funext i; exact Bool.xor_self _
  refine ⟨ψ, fun x hx => by simp [ψ, hx], by simp [ψ, independent, self, atZero], ?_⟩
  have mixed (x y : Vector ι) (hx : S x) (ny : ¬ S y) (hy : S (plus y v)) :
      ψ (plus x y) = (ψ x ^^ ψ y) := by
    have nxy : ¬ S (plus x y) := by
      intro hxy
      have hh := sumClosed x (plus x y) hx hxy
      rw [leftCancel] at hh
      exact ny hh
    simp only [ψ, if_pos hx, if_neg ny, if_neg nxy]
    rw [plusAssoc, linear x (plus y v) hx hy, Bool.xor_assoc]
  intro x y xs ys
  by_cases hx : S x
  · by_cases hy : S y
    · simp [ψ, hx, hy, sumClosed x y hx hy, linear x y hx hy]
    · exact mixed x y hx hy (ys.resolve_left hy)
  · by_cases hy : S y
    · rw [plusComm x y, Bool.xor_comm (ψ x) (ψ y)]
      exact mixed y x hy hx (xs.resolve_left hx)
    · have xshift := xs.resolve_left hx
      have yshift := ys.resolve_left hy
      have hxy : S (plus x y) := by
        rw [← shiftCancel x y v]
        exact sumClosed _ _ xshift yshift
      simp only [ψ, if_neg hx, if_neg hy, if_pos hxy]
      rw [← shiftCancel x y v, linear _ _ xshift yshift]
      cases φ (plus x v) <;> cases φ (plus y v) <;> cases answer <;> rfl

end LocalParityAnswers
