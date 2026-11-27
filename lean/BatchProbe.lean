import Std

/-! Transcript invariance for a single fixed proof header and challenge. -/
namespace BatchProbe

inductive Test where
  | leaf (result : Bool)
  | ask (index : Nat) (next : Bool → Test)

def verdict : Test → (Nat → Bool) → Bool
  | .leaf result, _ => result
  | .ask i next, x => verdict (next (x i)) x

def path : Test → (Nat → Bool) → List Nat
  | .leaf _, _ => []
  | .ask i next, x => i :: path (next (x i)) x

def flip (x : Nat → Bool) (i j : Nat) : Bool :=
  if j = i then !(x j) else x j

theorem flip_unseen (t : Test) (x : Nat → Bool) (m : Nat)
    (h : m ∉ path t x) : verdict t (flip x m) = verdict t x := by
  induction t with
  | leaf => rfl
  | ask i next ih =>
    simp only [path, List.mem_cons, not_or] at h
    have same : flip x m i = x i := by
      simp [flip, Ne.symm h.1]
    simp only [verdict, same]
    exact ih (x i) h.2

/-- A rejected single-bit change stays rejected after the partner bit changes,
provided the latter was absent from the original rejecting path. -/
theorem reject_swap (t : Test) (x : Nat → Bool) (i mate : Nat)
    (unseen : mate ∉ path t (flip x i)) (bad : verdict t (flip x i) = false) :
    verdict t (flip (flip x i) mate) = false := by
  exact (flip_unseen t (flip x i) mate unseen).trans bad

#print axioms reject_swap
end BatchProbe
