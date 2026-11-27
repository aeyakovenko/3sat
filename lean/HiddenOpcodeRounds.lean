/-! Two deterministic steps of the hidden-opcode argument, independent of
the probabilistic estimate and the existence of a depth-robust graph. -/
namespace HiddenOpcodeRounds

inductive Path {α : Type} (edge : α → α → Prop) (reused : α → Prop) : α → Nat → Prop
  | single (v : α) (safe : ¬reused v) : Path edge reused v 1
  | extend {v w : α} {n : Nat} (earlier : Path edge reused v n)
      (step : edge v w) (safe : ¬reused w) : Path edge reused w (n+1)

theorem round_bound {α : Type} {edge : α → α → Prop} {reused : α → Prop}
    (stamp : α → Nat) (start : ∀ v, 0 < stamp v)
    (depends : ∀ u v, edge u v → ¬reused u → ¬reused v → stamp u < stamp v)
    {v : α} {n : Nat} (walk : Path edge reused v n) : n ≤ stamp v ∧ ¬reused v := by
  induction walk with
  | single v safe => exact ⟨start v, safe⟩
  | @extend u v n earlier step safe ih =>
    have order := depends u v step ih.2 safe
    exact ⟨by have size := ih.1; omega, safe⟩

inductive OracleTree (Key Word Value : Type) : Type
  | done (value : Value)
  | query (key : Key) (next : Word → OracleTree Key Word Value)

def answer {K W A : Type} (table : K → W) : OracleTree K W A → A
  | .done value => value
  | .query key next => answer table (next (table key))

def misses {K W A : Type} (table : K → W) (changed : K) : OracleTree K W A → Prop
  | .done _ => True
  | .query key next => key ≠ changed ∧ misses table changed (next (table key))

theorem unchanged_transcript {K W A : Type} (old new : K → W) (changed : K)
    (agree : ∀ k, k ≠ changed → old k = new k) (tree : OracleTree K W A)
    (skip : misses old changed tree) : answer old tree = answer new tree := by
  induction tree with
  | done v => rfl
  | query k next ih =>
    obtain ⟨other, tail⟩ := skip
    have reply := agree k other
    simpa only [answer, ← reply] using (ih (old k) tail)

end HiddenOpcodeRounds
