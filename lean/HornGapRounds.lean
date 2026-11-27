import Std

namespace HornGapRounds

structure Rule (Atom : Type) where
  premises : List Atom
  head : Atom
  weight : Nat

def active {A : Type} (s : A → Bool) (r : Rule A) :=
  r.premises.all s && !s r.head

def charge {A : Type} (s : A → Bool) (rs : List (Rule A)) :=
  (rs.map (fun r => if active s r then r.weight else 0)).sum

def remaining {A : Type} (s : A → Bool) (rs : List (Rule A)) :=
  (rs.map (fun r => if s r.head then 0 else r.weight)).sum

/-- A simultaneous forward step permanently removes the weight of each
currently violated rule from the potential attached to unproved heads. -/
theorem oneStep {A : Type} (s t : A → Bool) (rs : List (Rule A))
    (keep : ∀ a, s a = true → t a = true)
    (fire : ∀ r ∈ rs, active s r = true → t r.head = true) :
    charge s rs + remaining t rs ≤ remaining s rs := by
  induction rs with
  | nil => simp [charge, remaining]
  | cons r rs ih =>
    have tail := ih (fun q hq => fire q (List.mem_cons_of_mem _ hq))
    have head := fire r (List.mem_cons_self)
    have stable := keep r.head
    change ((if active s r then r.weight else 0) + charge s rs) +
      ((if t r.head then 0 else r.weight) + remaining t rs) ≤
      ((if s r.head then 0 else r.weight) + remaining s rs)
    have localBound : (if active s r then r.weight else 0) +
        (if t r.head then 0 else r.weight) ≤ (if s r.head then 0 else r.weight) := by
      unfold active at head ⊢
      cases hs : s r.head <;> cases ht : t r.head <;> cases hb : r.premises.all s <;>
        simp_all
    omega

/-- With gap `g` at each of the first `h` snapshots, the total
initial weight of rules with unproved heads covers all `h*g` charges.
An atom reserved for contradiction may first be proved in the last step. -/
theorem cumulative {A : Type} (s : Nat → A → Bool) (rs : List (Rule A)) (h g : Nat)
    (keep : ∀ i a, s i a = true → s (i+1) a = true)
    (fire : ∀ i, ∀ r ∈ rs, active (s i) r = true → s (i+1) r.head = true)
    (gap : ∀ i < h, g ≤ charge (s i) rs) :
    h * g + remaining (s h) rs ≤ remaining (s 0) rs := by
  induction h with
  | zero => simp
  | succ h ih =>
    have prev := ih (fun i hi => gap i (by omega))
    have last := oneStep (s h) (s (h+1)) rs (keep h) (fire h)
    have hgap := gap h (by omega)
    rw [Nat.succ_mul]
    omega

/-- If terminal constraints contribute too little to the optimum at all
snapshots, head-rule charges exhaust their budget. Here `best i` is the
minimum violated weight of the activated binary clauses at snapshot i. -/
theorem terminalGap {A : Type} (s : Nat → A → Bool) (rs : List (Rule A))
    (h threshold : Nat) (best : Nat → Nat)
    (keep : ∀ i a, s i a = true → s (i+1) a = true)
    (fire : ∀ i, ∀ r ∈ rs, active (s i) r = true → s (i+1) r.head = true)
    (gap : ∀ i ≤ h, 2 * threshold ≤ charge (s i) rs + best i)
    (budget : remaining (s 0) rs < (h+1) * threshold) :
    ∃ i ≤ h, threshold ≤ best i := by
  apply Classical.byContradiction
  intro absent
  have every : ∀ i < h+1, threshold ≤ charge (s i) rs := by
    intro i hi
    have within : i ≤ h := by omega
    have small : ¬threshold ≤ best i := fun hit => absent ⟨i, within, hit⟩
    have total := gap i within
    omega
  have used := cumulative s rs (h+1) threshold keep fire every
  omega

end HornGapRounds
