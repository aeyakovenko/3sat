import Std

namespace PriorityFloodWindow

/-- Time plus a nonincreasing count rises by at most one per step. -/
theorem crossing (f : Nat → Nat) (start target : Nat) (le : start ≤ target)
    (initial : start + f start ≤ target)
    (nonincrease : ∀ t, start ≤ t → t < target → f (t+1) ≤ f t) :
    ∃ t, start ≤ t ∧ t ≤ target ∧ t + f t = target := by
  apply Classical.byContradiction
  intro absent
  have strict : ∀ n, start + n ≤ target → start + n + f (start + n) < target := by
    intro n
    induction n with
    | zero =>
      intro _
      have different : start + f start ≠ target := fun eq => absent ⟨start, by omega, le, eq⟩
      simp only [Nat.add_zero]
      omega
    | succ n ih =>
      intro ht
      have prior := ih (by omega)
      have drop := nonincrease (start+n) (by omega) (by omega)
      have different : start + (n+1) + f (start+(n+1)) ≠ target :=
        fun eq => absent ⟨_, by omega, ht, eq⟩
      rw [Nat.add_assoc] at drop
      omega
  have final := strict (target-start) (by omega)
  rw [show start + (target-start) = target by omega] at final
  omega

/-- With all pulses set, the first active unretired rank wins. The list is
    supplied in priority order and includes ranks not yet active. -/
def choose (active : Nat → Nat → Bool) (t : Nat) : List Nat → Option Nat
  | [] => none
  | x :: xs => if active t x then some x else choose active t xs

def flood (active : Nat → Nat → Bool) (t : Nat) (pending : List Nat) :
    Nat → List (Option Nat)
  | 0 => []
  | n+1 =>
    match choose active t pending with
    | none => none :: flood active (t+1) pending n
    | some x => some x :: flood active (t+1) (pending.erase x) n

/-- All lower ranks go first. The target only needs to be active on its
    election day. No activation condition is imposed on the ranks above it. -/
theorem countdown (active : Nat → Nat → Bool) (t e : Nat) (lower higher : List Nat)
    (low : ∀ s, t ≤ s → s < t + lower.length → ∀ x ∈ lower, active s x = true)
    (target : active (t + lower.length) e = true) :
    flood active t (lower ++ e :: higher) (lower.length + 1) =
      lower.map some ++ [some e] := by
  induction lower generalizing t with
  | nil =>
    simp only [List.length_nil, Nat.add_zero] at target
    simp [flood, choose, target]
  | cons x xs ih =>
    have first := low t (by omega) (by simp) x (by simp)
    have rest : ∀ s, t+1 ≤ s → s < t+1+xs.length → ∀ y ∈ xs, active s y = true := by
      intro s tLe sLt y hy
      exact low s (by omega) (by simp; omega) y (List.mem_cons_of_mem x hy)
    have last : active (t+1+xs.length) e = true := by
      rw [show t+1+xs.length = t+(x::xs).length by simp only [List.length_cons]; omega]
      exact target
    simpa [List.cons_append, List.length_cons, flood, choose, first] using
      congrArg (List.cons (some x)) (ih (t+1) rest last)

/-- `lower t ++ e :: higher t` is the true unretired list before a candidate
    start time. The flood can use one suffix of the last e+1 stages. -/
theorem winning_window (active : Nat → Nat → Bool) (j e : Nat) (enough : e ≤ j)
    (lower higher : Nat → List Nat) (initial : (lower (j-e)).length ≤ e)
    (shrink : ∀ t, j-e ≤ t → t < j → (lower (t+1)).length ≤ (lower t).length)
    (below : ∀ t, ∀ x ∈ lower t, x < e)
    (available : ∀ s, j-e ≤ s → s < j → ∀ x, x < e → active s x = true)
    (target : active j e = true) :
    ∃ t, j-e ≤ t ∧ t ≤ j ∧ t + (lower t).length = j ∧
      flood active t (lower t ++ e :: higher t) (j-t+1) = (lower t).map some ++ [some e] := by
  obtain ⟨t, start, finish, hits⟩ :=
    crossing (fun s => (lower s).length) (j-e) j (by omega) (by dsimp; omega) shrink
  refine ⟨t, start, finish, hits, ?_⟩
  have low : ∀ s, t ≤ s → s < t+(lower t).length → ∀ x ∈ lower t, active s x = true := by
    intro s ts sj x hx
    exact available s (by omega) (by omega) x (below t x hx)
  have target' : active (t+(lower t).length) e = true := by simpa [hits] using target
  rw [show j-t = (lower t).length by omega]
  exact countdown active t e (lower t) (higher t) low target'

/-- The input to the priority selector can include arbitrary pulses outside
    the one named rank on each day. The caller combines activity and pulse. -/
def scheduled (enabled : Nat → Nat → Bool) (t : Nat) : List Nat → Prop
  | [] => True
  | x :: xs => enabled t x = true ∧ scheduled enabled (t+1) xs

theorem sparse_countdown (enabled : Nat → Nat → Bool) (t : Nat) (ordered higher : List Nat)
    (on : scheduled enabled t ordered) :
    flood enabled t (ordered ++ higher) ordered.length = ordered.map some := by
  induction ordered generalizing t with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨now, later⟩ := on
    simpa [List.cons_append, List.length_cons, flood, choose, now] using
      congrArg (List.cons (some x)) (ih (t+1) later)

private theorem rank_room (x e : Nat) (rest : List Nat)
    (order : (x :: (rest ++ [e])).Pairwise (· < ·)) : x + rest.length + 1 ≤ e := by
  induction rest generalizing x with
  | nil =>
    have lt := (List.pairwise_cons.mp order).1 e (by simp)
    simp only [List.length_nil]
    omega
  | cons y ys ih =>
    have lt := (List.pairwise_cons.mp order).1 y (by simp)
    have room := ih y (List.pairwise_cons.mp order).2
    simp only [List.length_cons]
    omega

/-- At day s=t+prefix.length the scheduled lower rank x satisfies
    s-x ≥ j-e, where j is the election day of the target e. -/
theorem scheduled_rank_budget (t x e : Nat) (prefixPart rest : List Nat)
    (order : (x :: (rest ++ [e])).Pairwise (· < ·)) :
    (t + (prefixPart ++ x :: rest).length) - e ≤ (t + prefixPart.length) - x := by
  have room := rank_room x e rest order
  simp only [List.length_append, List.length_cons]
  omega

end PriorityFloodWindow
