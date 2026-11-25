import Std

namespace TableProbeContexts

/-- Public computation against one fixed table is deterministic. Only
    `probe` transitions inspect the private string. -/
inductive Op (ι σ : Type) where
  | result (answer : Bool)
  | step (next : σ)
  | probe (index : ι) (next : Bool → σ)

variable {ι σ : Type} (program : σ → Op ι σ)

/-- A finite stretch of public execution up to and including the instruction
    that either halts or is about to consult the private string. -/
inductive First : σ → Op ι σ → Prop where
  | result (h : program s = .result b) : First s (.result b)
  | probe (h : program s = .probe i k) : First s (.probe i k)
  | step (h : program s = .step r) (tail : First r event) : First s event

theorem first_unique {s e f} (h : First program s e) (j : First program s f) :
    e = f := by
  induction h generalizing f with
  | result hr => cases j <;> simp_all
  | probe hp => cases j <;> simp_all
  | step hs _ ih =>
    cases j with
    | result hr => simp_all
    | probe hp => simp_all
    | step ht rest =>
      rw [hs] at ht
      cases ht
      exact ih rest

variable (bits : ι → Bool)

inductive Halts : σ → Bool → Prop where
  | result (h : program s = .result b) : Halts s b
  | step (h : program s = .step r) (tail : Halts r b) : Halts s b
  | probe (h : program s = .probe i k) (tail : Halts (k (bits i)) b) : Halts s b

/-- Each step of the contracted execution either reaches a verdict via a
    public stretch or queries one private bit and follows its chosen edge. -/
inductive Contracted : σ → Bool → Prop where
  | result (front : First program s (.result b)) : Contracted s b
  | probe (front : First program s (.probe i k))
      (tail : Contracted (k (bits i)) b) : Contracted s b

private theorem contract {s b} (h : Halts program bits s b) :
    Contracted program bits s b := by
  induction h with
  | result hr => exact .result (.result hr)
  | probe hp _ ih => exact .probe (.probe hp) ih
  | step hs _ ih =>
    cases ih with
    | result front => exact .result (.step hs front)
    | probe front tail => exact .probe (.step hs front) tail

private def resume (satisfies : σ → Bool → Prop) : Op ι σ → Bool → Prop
  | .result v, b => v = b
  | .step r, b => satisfies r b
  | .probe i k, b => satisfies (k (bits i)) b

private theorem restore_span {s event b} (front : First program s event) :
    resume bits (Halts program bits) event b → Halts program bits s b := by
  induction front with
  | result hr =>
    intro hv
    cases hv
    exact .result hr
  | probe hp => exact fun tail => .probe hp tail
  | step hs _ ih => exact fun tail => .step hs (ih tail)

/-- Private-probe contraction preserves both finite verdicts without any
    clock assumption. A public cycle with no later private probe or verdict
    has no `First` derivation, and consequently contributes no verdict. -/
theorem contraction_iff {s b} :
    Halts program bits s b ↔ Contracted program bits s b := by
  constructor
  · exact contract program bits
  · intro h
    induction h with
    | result front => exact restore_span program bits front rfl
    | probe front _ ih => exact restore_span program bits front ih

/-- Remove one unused codeword and renumber its larger neighbors. -/
private def skipIndex {n : Nat} (avoid x : Fin (n+1)) (hne : x ≠ avoid) : Fin n :=
  ⟨if x.val < avoid.val then x.val else x.val - 1, by
    have ha := avoid.isLt
    have hx := x.isLt
    have hval : x.val ≠ avoid.val := fun h => hne (Fin.ext h)
    split <;> omega⟩

private theorem skipIndex_injective {n : Nat} {avoid a b : Fin (n+1)}
    (ha : a ≠ avoid) (hb : b ≠ avoid)
    (he : skipIndex avoid a ha = skipIndex avoid b hb) : a = b := by
  have h₁ : a.val ≠ avoid.val := fun h => ha (Fin.ext h)
  have h₂ : b.val ≠ avoid.val := fun h => hb (Fin.ext h)
  have hv := congrArg Fin.val he
  simp only [skipIndex] at hv
  apply Fin.ext
  split at hv <;> split at hv <;> omega

private theorem injection_bound {m n : Nat} (f : Fin m → Fin n)
    (inj : ∀ a b, f a = f b → a = b) : m ≤ n := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => exact Nat.le_refl 0
    | succ m => exact Fin.elim0 (f 0)
  | succ n ih =>
    cases m with
    | zero => exact Nat.zero_le _
    | succ m =>
      let finalIndex : Fin (m+1) := ⟨m, Nat.lt_succ_self _⟩
      have fresh (a : Fin m) : f a.castSucc ≠ f finalIndex := by
        intro he
        have hv := congrArg Fin.val (inj _ _ he)
        have := a.isLt
        change a.val = m at hv
        omega
      let g (a : Fin m) : Fin n := skipIndex (f finalIndex) (f a.castSucc) (fresh a)
      have smaller := ih g (by
        intro a b he
        have hf := skipIndex_injective (fresh a) (fresh b) he
        have hv := congrArg (fun u : Fin (m+1) => u.val) (inj _ _ hf)
        exact Fin.ext hv)
      exact Nat.succ_le_succ smaller

/-- Number the truth tables and the available start/edge codes. If a code
    specifies at most one total truth table, there must be at least as many
    possible codes as truth tables. -/
theorem table_count_bound (t nodes : Nat)
    (encode : Fin (2^(2^t)) → Fin ((nodes+3)^(2*nodes+1)))
    (faithful : ∀ a b, encode a = encode b → a = b) :
    2^(2^t) ≤ (nodes+3)^(2*nodes+1) := injection_bound encode faithful

end TableProbeContexts
