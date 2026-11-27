import Std

namespace SparseCompilerPresentation

/-- Replace all unqueried pad entries by a fixed default. -/
def sparsePad {I A : Type} [DecidableEq I] (queries : List I) (pad : I → A)
    (default : A) (i : I) : A := if i ∈ queries then pad i else default

inductive QueryTree (I A R : Type) where
  | done (r : R)
  | ask (i : I) (next : A → QueryTree I A R)

def QueryTree.output {I A R : Type} : QueryTree I A R → (I → A) → R
  | .done r, _ => r
  | .ask i next, pad => (next (pad i)).output pad

def QueryTree.path {I A R : Type} : QueryTree I A R → (I → A) → List I
  | .done _, _ => []
  | .ask i next, pad => i :: (next (pad i)).path pad

theorem QueryTree.path_determines {I A R : Type} (t : QueryTree I A R)
    (pad other : I → A) (agree : ∀ i ∈ t.path pad, other i = pad i) :
    t.output other = t.output pad := by
  induction t with
  | done => rfl
  | ask i next ih =>
    have hi := agree i (by simp [path])
    simp only [output, hi]
    exact ih (pad i) (fun j hj => agree j (by simp [path, hj]))

theorem QueryTree.sparse_replay {I A R : Type} [DecidableEq I] (t : QueryTree I A R)
    (pad : I → A) (default : A) :
    t.output (sparsePad (t.path pad) pad default) = t.output pad := by
  apply path_determines
  intro i hi
  simp [sparsePad, hi]

structure Perm (I : Type) where
  f : I → I
  g : I → I
  gf : ∀ x, g (f x) = x
  fg : ∀ x, f (g x) = x

theorem Perm.inj {I : Type} (p : Perm I) {x y : I} (h : p.f x = p.f y) : x = y := by
  simpa [p.gf] using congrArg p.g h

def exchange {I : Type} [DecidableEq I] (a b x : I) :=
  if x = a then b else if x = b then a else x

theorem exchange_twice {I : Type} [DecidableEq I] (a b x : I) :
    exchange a b (exchange a b x) = x := by
  by_cases ha : x = a
  · subst x
    by_cases h : a = b <;> simp_all [exchange]
  · by_cases hb : x = b
    · subst x
      simp_all [exchange]
    · simp [exchange, ha, hb]

def Perm.swapOutputs {I : Type} [DecidableEq I] (p : Perm I) (a b : I) : Perm I where
  f x := exchange a b (p.f x)
  g y := p.g (exchange a b y)
  gf x := by simp only [exchange_twice, p.gf]
  fg y := by simp only [p.fg, exchange_twice]

/-- Every list of observed forward pairs of a permutation can be extended
    using only the at most twice-as-many endpoints as possible moved points. -/
theorem partial_permutation {I : Type} [DecidableEq I] (p : Perm I) (xs : List I) :
    ∃ q : Perm I, (∀ x ∈ xs, q.f x = p.f x) ∧
      (∀ z, z ∉ xs → z ∉ xs.map p.f → q.f z = z) := by
  induction xs with
  | nil =>
    exact ⟨⟨id, id, fun _ => rfl, fun _ => rfl⟩, by simp, fun _ _ _ => rfl⟩
  | cons x xs ih =>
    obtain ⟨q, agrees, fixed⟩ := ih
    refine ⟨q.swapOutputs (q.f x) (p.f x), ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with h | h
      · subst y
        simp [Perm.swapOutputs, exchange]
      · by_cases same : y = x
        · subst y
          simp [Perm.swapOutputs, exchange]
        · have h₁ : q.f y ≠ q.f x := fun e => same (q.inj e)
          have h₂ : q.f y ≠ p.f x := fun e => same (p.inj ((agrees y h).symm.trans e))
          simp only [Perm.swapOutputs, exchange, if_neg h₁, if_neg h₂]
          exact agrees y h
    · intro z raw images
      have zx : z ≠ x := fun e => raw (List.mem_cons.mpr (Or.inl e))
      have zxs : z ∉ xs := fun e => raw (List.mem_cons.mpr (Or.inr e))
      have stripped : z ∉ p.f x :: xs.map p.f := images
      have zpx : z ≠ p.f x := fun e => stripped (List.mem_cons.mpr (Or.inl e))
      have zimages : z ∉ xs.map p.f := fun e => stripped (List.mem_cons.mpr (Or.inr e))
      have hz := fixed z zxs zimages
      have avoid : z ≠ q.f x := fun e => zx (q.inj (hz.trans e))
      simp [Perm.swapOutputs, exchange, hz, avoid, zpx]

theorem inverse_observation {I : Type} {p q : Perm I} {y : I}
    (agree : q.f (p.g y) = p.f (p.g y)) : q.g y = p.g y := by
  rw [p.fg] at agree
  calc
    q.g y = q.g (q.f (p.g y)) := congrArg q.g agree.symm
    _ = p.g y := q.gf _

#print axioms QueryTree.sparse_replay
#print axioms partial_permutation
#print axioms inverse_observation

end SparseCompilerPresentation
