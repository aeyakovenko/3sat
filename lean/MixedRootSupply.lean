import Std

namespace MixedRootSupply

/-- The first two clauses implement a binary implication. All later clauses
    force the next entry whenever its two predecessors take the active value. -/
theorem broadcast (v : Nat → Bool) (active : Bool)
    (seed : v 0 = active) (start : v 0 = active → v 1 = active)
    (next : ∀ i, v i = active → v (i+1) = active → v (i+2) = active) :
    ∀ i, v i = active := by
  have pair (i : Nat) : v i = active ∧ v (i+1) = active := by
    induction i with
    | zero => exact ⟨seed, start seed⟩
    | succ i ih => exact ⟨ih.2, next i ih.1 ih.2⟩
  exact fun i => (pair i).1

/-- Six terminal chains feed two groups of three. Their four intermediate
    pads have bounded fanout, and the surviving group forces the final pad. -/
theorem force_pad (active : Bool) (value : Bool)
    (chain : Fin 3 → Bool → Nat → Bool)
    (group : Fin 3 → Bool → Bool)
    (mid : Bool → Bool → Bool)
    (one : ∃ r branch, ∀ i, chain r branch i = active)
    (supply : ∀ r branch, (∀ i, chain r branch i = active) →
      ∀ b, mid (group r branch) b = active)
    (finish : ∀ g, mid g false = active → mid g true = active → value = active) :
    value = active := by
  obtain ⟨r, branch, on⟩ := one
  exact finish (group r branch) (supply r branch on false) (supply r branch on true)

/-- This is the pair of mixed clauses attached to one root bit. When its
    value is active at least one of its two candidate supply chains starts. -/
theorem active_chain (root : Fin 3 → Bool) (active : Bool)
    (v : Fin 3 → Bool → Nat → Bool)
    (live : ∃ r, root r = active)
    (fork : ∀ r, root r = active → v r false 0 = active ∨ v r true 0 = active)
    (first : ∀ r b, v r b 0 = active → v r b 1 = active)
    (step : ∀ r b i, v r b i = active → v r b (i+1) = active →
      v r b (i+2) = active) :
    ∃ r b, ∀ i, v r b i = active := by
  obtain ⟨r, hr⟩ := live
  rcases fork r hr with left | right
  · exact ⟨r,false,broadcast _ _ left (first r false) (step r false)⟩
  · exact ⟨r,true,broadcast _ _ right (first r true) (step r true)⟩

/-- A source clause after its spare positive pad has been forced false and
    its spare negative pad has been forced true. No auxiliary is pinned. -/
theorem gated_clause (a b c f t : Bool) (hf : f = false) (ht : t = true) :
    (∃ u v : Bool, (f || a || !u) = true ∧ (u || b || !v) = true ∧
      (v || c || !t) = true) ↔ (a || b || c) = true := by
  subst f
  subst t
  cases a <;> cases b <;> cases c <;> decide

/-- The sharp twelve-variable example uses Y=1..4, Z=5..8 and W=9..12. -/
def sharpHalf (a b c d : Int) : List (List Int) :=
  [[-a,-b,c], [-a,-c,d], [-a,-d,b], [-b,-c,a],
   [-b,-d,9], [-c,-d,10], [-9,-11,12], [-10,-12,11]]

def sharpRows : List (List Int) :=
  sharpHalf 1 2 3 4 ++ (sharpHalf 5 6 7 8).map (fun row => row.map (- ·))

/-- In a proper clause a face about a uniform vector satisfies every filling
    precisely when it fixes at least one literal of the correct sign. -/
def centeredFace (rows : List (List Int)) (one : Bool) (free : Nat) : Bool :=
  rows.all (fun row => row.any (fun x =>
    decide (x > 0) == one && !free.testBit (x.natAbs - 1)))

/-- All valid masks are listed exactly, at both uniform centers. -/
theorem exact_sharp_masks :
    (List.range 4096).filter (centeredFace sharpRows false) = [0,1,2,4,8] ∧
    (List.range 4096).filter (centeredFace sharpRows true) = [0,16,32,64,128] := by
  native_decide

end MixedRootSupply
