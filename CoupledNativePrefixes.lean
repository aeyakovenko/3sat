/- Rows with compatible actions up to a binary branch give one program
   and one output map that execute all the rows. The physical instruction
   evaluator is arbitrary. -/
namespace CoupledNativePrefixes

variable {I S A : Type}

def trace (step : I → S → A → Bool × S) (init : I → S)
    (action : I → Nat → List Bool → A) (i : I) : Nat → List Bool × S
  | 0 => ([], init i)
  | n+1 =>
    let p := trace step init action i n
    let q := step i p.2 (action i n p.1)
    (p.1 ++ [q.1], q.2)

theorem trace_length (step : I → S → A → Bool × S) (init : I → S)
    (action : I → Nat → List Bool → A) (i : I) (n : Nat) :
    (trace step init action i n).1.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [trace, ih]

noncomputable def onFibre {K V : Type} (key : I → K) (value : I → V)
    (fallback : V) (k : K) : V := by
  classical
  exact if h : ∃ j, key j = k then value (Classical.choose h) else fallback

theorem onFibre_eq {K V : Type} (key : I → K) (value : I → V)
    (fallback : V) (i : I)
    (agree : ∀ j, key j = key i → value j = value i) :
    onFibre key value fallback (key i) = value i := by
  classical
  have hex : ∃ j, key j = key i := ⟨i, rfl⟩
  unfold onFibre
  rw [dif_pos hex]
  exact agree _ (Classical.choose_spec hex)

theorem shared_tree (step : I → S → A → Bool × S) (init : I → S)
    (localAct : I → Nat → A) (fallback : A) (label : I → Bool) (D : Nat)
    (hits : ∀ i j n, n < D →
      (trace step init (fun x t _ => localAct x t) i n).1 =
      (trace step init (fun x t _ => localAct x t) j n).1 →
      localAct i n = localAct j n)
    (ends : ∀ i j,
      (trace step init (fun x t _ => localAct x t) i D).1 =
      (trace step init (fun x t _ => localAct x t) j D).1 →
      label i = label j) :
    ∃ (next : List Bool → A) (output : List Bool → Bool),
      (∀ i n, n ≤ D →
        trace step init (fun _ _ h => next h) i n =
        trace step init (fun x t _ => localAct x t) i n) ∧
      (∀ i, output (trace step init (fun _ _ h => next h) i D).1 = label i) := by
  let hist (i : I) (n : Nat) := (trace step init (fun x t _ => localAct x t) i n).1
  let next (h : List Bool) :=
    onFibre (fun i => hist i h.length) (fun i => localAct i h.length) fallback h
  let output := onFibre (fun i => hist i D) label false
  have local_match (i : I) (n : Nat) (hn : n < D) :
      next (hist i n) = localAct i n := by
    have length_eq : (hist i n).length = n := trace_length _ _ _ _ _
    simp only [next, length_eq]
    exact onFibre_eq _ _ _ _ (fun j h => hits j i n hn h)
  have replay (i : I) (n : Nat) (hn : n ≤ D) :
      trace step init (fun _ _ h => next h) i n =
      trace step init (fun x t _ => localAct x t) i n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have small : n < D := hn
      simp only [trace, ih (Nat.le_of_lt small)]
      rw [show next (trace step init (fun x t _ => localAct x t) i n).1 =
        localAct i n from local_match i n small]
  refine ⟨next, output, replay, ?_⟩
  intro i
  rw [replay i D (Nat.le_refl _)]
  exact onFibre_eq _ _ _ _ (fun j h => ends j i h)

#print axioms shared_tree
end CoupledNativePrefixes
