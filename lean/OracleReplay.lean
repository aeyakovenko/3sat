import Std

namespace OracleReplay

/-- After expanding the wrapper gates, a finite computation consists of raw
    queries; later queries may depend on earlier answers. -/
inductive TraceTree (K : Type) where
  | done (out : Bool)
  | ask (key : K) (ifFalse ifTrue : TraceTree K)

def eval (R : K → Bool) : TraceTree K → Bool
  | .done out => out
  | .ask key lo hi => if R key then eval R hi else eval R lo

def probes (R : K → Bool) : TraceTree K → List K
  | .done _ => []
  | .ask key lo hi => key :: (if R key then probes R hi else probes R lo)

/-- Agreement only on the queries of the first run suffices. -/
theorem replay (t : TraceTree K) (R S : K → Bool)
    (hc : ∀ x ∈ probes R t, S x = R x) : eval S t = eval R t := by
  induction t with
  | done => rfl
  | ask key lo hi il ih =>
    have hkey := hc key (by simp [probes])
    cases hr : R key with
    | false =>
      simp only [eval, hkey, hr, Bool.false_eq_true, ↓reduceIte]
      exact il (fun x hx => hc x (by simp [probes, hr, hx]))
    | true =>
      simp only [eval, hkey, hr, ↓reduceIte]
      exact ih (fun x hx => hc x (by simp [probes, hr, hx]))

/-- If a slice was empty and has an unprobed key, the evaluated tree
    cannot distinguish setting exactly that one new raw bit. -/
theorem fresh_bit [DecidableEq K] (t : TraceTree K) (R : K → Bool)
    (slice : K → Prop) (empty : ∀ k, slice k → R k = false)
    (y : K) (inSlice : slice y) (fresh : y ∉ probes R t) :
    ∃ S : K → Bool, eval S t = eval R t ∧ (∃ k, slice k ∧ S k = true) ∧
      (∀ k, slice k → R k = false) := by
  let S : K → Bool := fun k => if k = y then true else R k
  refine ⟨S, replay t R S ?_, ⟨y, inSlice, by simp [S]⟩, empty⟩
  intro x hx
  have different : x ≠ y := fun eq => fresh (eq ▸ hx)
  simp [S, different]

end OracleReplay
