import Std

namespace ClauseParityDefect

def sign (b : Bool) : Int := if b then -1 else 1

def oddParity (x y z : Bool) := (x ^^ y) ^^ z

/-- Sum of the three singleton and three pair characters of a satisfied clause. -/
theorem six_characters (x y z : Bool) (sat : (x || y || z) = true) :
    sign x + sign y + sign z + sign x * sign y + sign y * sign z + sign z * sign x =
      (if oddParity x y z then 0 else -2) := by
  cases x <;> cases y <;> cases z <;> first | contradiction | decide

/-- If the bond bit is false the state must stay fixed. -/
def Walk (start stop : Bool) : List Bool → Prop
  | [] => start = stop
  | p :: ps => ∃ next : Bool, (p = true ∨ start = next) ∧ Walk next stop ps

theorem endpoints (ps : List Bool) (a b : Bool) :
    Walk a b ps ↔ a = b ∨ true ∈ ps := by
  induction ps generalizing a b with
  | nil => simp [Walk]
  | cons p ps ih =>
    constructor
    · rintro ⟨next, hp, htail⟩
      rcases hp with hp | hsame
      · subst p
        simp
      · subst next
        rcases (ih a b).mp htail with heq | hmem
        · exact Or.inl heq
        · exact Or.inr (List.mem_cons_of_mem _ hmem)
    · intro h
      rcases h with heq | hmem
      · exact ⟨a, Or.inr rfl, (ih a b).mpr (Or.inl heq)⟩
      · rcases List.mem_cons.mp hmem with hp | htail
        · exact ⟨b, Or.inl hp.symm, (ih b b).mpr (Or.inl rfl)⟩
        · exact ⟨a, Or.inr rfl, (ih a b).mpr (Or.inr htail)⟩

theorem twisted_cycle (ps : List Bool) (a : Bool) :
    Walk a (!a) ps ↔ true ∈ ps := by
  rw [endpoints]
  cases a <;> simp

theorem sign_link (l a b : Bool) :
    ((l || !a || b) && (l || a || !b) = true) ↔ (l = true ∨ a = b) := by
  cases l <;> cases a <;> cases b <;> decide

/-- With equal-mass samples, a strict upper bound on the average produces a good sample. -/
theorem low_sample (counts : List Nat) (k : Nat)
    (h : counts.sum < (k + 1) * counts.length) :
    ∃ n ∈ counts, n ≤ k := by
  induction counts with
  | nil => simp at h
  | cons n ns ih =>
    by_cases small : n ≤ k
    · exact ⟨n, by simp, small⟩
    · simp only [List.sum_cons, List.length_cons, Nat.mul_succ] at h
      have htail : ns.sum < (k + 1) * ns.length := by omega
      obtain ⟨v, hv, hk⟩ := ih htail
      exact ⟨v, List.mem_cons_of_mem _ hv, hk⟩

/-- The interval between two distinct stored states in a three-layer cycle
cannot contain all or none of every share group. -/
theorem interval_splits_group (groups lo hi : Nat) (g : 0 < groups)
    (order : lo < hi) (bound : hi < 3 * groups) :
    ¬ (∀ i, i + groups < 3 * groups →
      ((lo ≤ i ∧ i < hi) ↔ (lo ≤ i + groups ∧ i + groups < hi))) := by
  intro periodic
  by_cases first : groups ≤ lo
  · have prev := periodic (lo - groups) (by omega)
    have inside := prev.mpr (by omega)
    omega
  · have mid := (periodic lo (by omega)).mp (by omega)
    have last := (periodic (lo + groups) (by omega)).mp (by omega)
    have edge := (periodic (hi - groups) (by omega)).mp (by omega)
    omega

end ClauseParityDefect
