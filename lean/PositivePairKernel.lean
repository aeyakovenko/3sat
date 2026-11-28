import Std

namespace PositivePairKernel

variable {V I A : Type}

inductive Path (edge : V → V → Prop) (u : V) : V → Prop
  | refl : Path edge u u
  | step {x y : V} : Path edge u x → edge x y → Path edge u y

def endpoint (left right : I → V) (choice : I → Bool) (i : I) : V :=
  if choice i then left i else right i

def seeds (unit : V → Prop) (left right : I → V) (choice : I → Bool) (x : V) : Prop :=
  unit x ∨ ∃ i, endpoint left right choice i = x

def closure (edge : V → V → Prop) (root : V → Prop) (x : V) : Prop :=
  ∃ u, root u ∧ Path edge u x

def safe (forbid : V → V → V → Prop) (hit : V → Prop) : Prop :=
  ∀ x y z, forbid x y z → ¬ (hit x ∧ hit y ∧ hit z)

def model (edge : V → V → Prop) (unit : V → Prop) (left right : I → V)
    (forbid : V → V → V → Prop) (chosen : V → Prop) : Prop :=
  (∀ v, unit v → chosen v) ∧ (∀ i, chosen (left i) ∨ chosen (right i)) ∧
  (∀ v w, edge v w → chosen v → chosen w) ∧ safe forbid chosen

private theorem path_closed {edge : V → V → Prop} {chosen : V → Prop}
    (closed : ∀ v w, edge v w → chosen v → chosen w)
    {u v : V} (p : Path edge u v) (initial : chosen u) : chosen v := by
  induction p with
  | refl => exact initial
  | step _ edgeHere ih => exact closed _ _ edgeHere ih

/-- Choose one endpoint per positive pair and test the least set closed under all arcs. -/
theorem equivalent (edge : V → V → Prop) (unit : V → Prop) (left right : I → V)
    (forbid : V → V → V → Prop) :
    (∃ chosen, model edge unit left right forbid chosen) ↔
    ∃ c, safe forbid (closure edge (seeds unit left right c)) := by
  classical
  constructor
  · rintro ⟨chosen, units, pairs, closed, avoids⟩
    let c := fun i => decide (chosen (left i))
    have subset : ∀ x, closure edge (seeds unit left right c) x → chosen x := by
      rintro x ⟨u, seed, path⟩
      apply path_closed closed path
      rcases seed with pinned | ⟨i, rfl⟩
      · exact units _ pinned
      · by_cases h : chosen (left i)
        · simp [c, endpoint, h]
        · simpa [c, endpoint, h] using (pairs i).resolve_left h
    refine ⟨c, fun x y z clause h => ?_⟩
    exact avoids x y z clause ⟨subset _ h.1, subset _ h.2.1, subset _ h.2.2⟩
  · rintro ⟨c, avoids⟩
    let r := seeds unit left right c
    have init : ∀ x, r x → closure edge r x := fun x h => ⟨x, h, .refl⟩
    refine ⟨closure edge r, fun x h => init x (.inl h), ?_, ?_, avoids⟩
    · intro i
      have h := init _ (Or.inr ⟨i, rfl⟩ : r (endpoint left right c i))
      cases e : c i
      · right; simpa [endpoint, e] using h
      · left; simpa [endpoint, e] using h
    · rintro v w arc ⟨u, seed, path⟩
      exact ⟨u, seed, .step path arc⟩

/-- Expanding three reachable supports gives a conjunction of choice-literal clauses. -/
theorem support_product (support : V → A → Prop) (live : A → Prop)
    (forbid : V → V → V → Prop) :
    safe forbid (fun x => ∃ a, support x a ∧ live a) ↔
    ∀ x y z, forbid x y z → ∀ a b c, support x a → support y b → support z c →
      ¬ (live a ∧ live b ∧ live c) := by
  constructor
  · intro h x y z clause a b c ha hb hc actual
    exact h x y z clause ⟨⟨a, ha, actual.1⟩, ⟨b, hb, actual.2.1⟩, ⟨c, hc, actual.2.2⟩⟩
  · rintro h x y z clause ⟨⟨a, ha, va⟩, ⟨b, hb, vb⟩, ⟨c, hc, vc⟩⟩
    exact h x y z clause a b c ha hb hc ⟨va, vb, vc⟩

/-- Labels can be propagated through the graph independently of their truth values. -/
theorem labels_commute (edge : V → V → Prop) (starts : A → V → Prop) (live : A → Prop)
    (x : V) :
    closure edge (fun u => ∃ a, starts a u ∧ live a) x ↔
      ∃ a, closure edge (starts a) x ∧ live a := by
  constructor
  · rintro ⟨u, ⟨a, start, active⟩, path⟩
    exact ⟨a, ⟨u, start, path⟩, active⟩
  · rintro ⟨a, ⟨u, start, path⟩, active⟩
    exact ⟨u, ⟨a, start, active⟩, path⟩

/-- Pinning endpoint choices leaves an intersection-closed family, including hidden variables. -/
def fixedBranch (root : V → Prop) (edge : V → V → Prop)
    (forbid : V → V → V → Prop) (hit : V → Prop) : Prop :=
  (∀ x, root x → hit x) ∧ (∀ x y, edge x y → hit x → hit y) ∧ safe forbid hit

theorem branch_intersection {root : V → Prop} {edge : V → V → Prop}
    {forbid : V → V → V → Prop} {u v : V → Prop}
    (hu : fixedBranch root edge forbid u) (hv : fixedBranch root edge forbid v) :
    fixedBranch root edge forbid (fun x => u x ∧ v x) := by
  refine ⟨fun x r => ⟨hu.1 x r, hv.1 x r⟩, ?_, ?_⟩
  · exact fun x y e h => ⟨hu.2.1 x y e h.1, hv.2.1 x y e h.2⟩
  · intro x y z clause h
    exact hu.2.2 x y z clause ⟨h.1.1, h.2.1.1, h.2.2.1⟩

/-- Odd parity has three singletons, even parity has their three complements. -/
private def triple (odd : Bool) (i : Fin 3) : Nat :=
  if odd then 1 <<< i.val else 7 ^^^ (1 <<< i.val)

private def parity (x : Nat) : Bool := (x.testBit 0 ^^ x.testBit 1) ^^ x.testBit 2

theorem triple_feasible : ∀ odd : Bool, ∀ i : Fin 3, parity (triple odd i) = odd := by
  decide +kernel

theorem triple_meet_fails : ∀ odd : Bool, ∀ i j : Fin 3, i ≠ j →
    parity ((triple odd i) &&& (triple odd j)) ≠ odd := by decide +kernel

/-- This holds for an arbitrary index type of blocks and independent parity conventions. -/
theorem product_one_per_branch {B : Type} (odd : B → Bool) (f g : B → Fin 3)
    (different : f ≠ g)
    (branch : (B → Nat) → Prop)
    (sound_ : ∀ x, branch x → ∀ j, parity (x j) = odd j)
    (meet : ∀ x y, branch x → branch y → branch (fun j => x j &&& y j)) :
    ¬ (branch (fun j => triple (odd j) (f j)) ∧ branch (fun j => triple (odd j) (g j))) := by
  intro ⟨hf, hg⟩
  apply different
  funext j
  apply Classical.byContradiction
  intro h
  exact triple_meet_fails (odd j) (f j) (g j) h
    (sound_ _ (meet _ _ hf hg) j)

end PositivePairKernel
