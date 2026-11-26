import Std

namespace TokenCopyAndReachability

/-- An address choice followed by an unchanged payload copy into the next buffer. -/
def copyStep (old : Bool → Payload) (p j : Bool) : Payload := old (j ^^ p)

def runCopies : List Bool → (Bool → Payload) → Bool → Payload
  | [], old => old
  | bit :: rest, old => runCopies rest (copyStep old bit)

def parity : List Bool → Bool
  | [] => false
  | bit :: rest => bit ^^ parity rest

/-- Valid for any payload type, even one on which no operation is supplied. -/
theorem payload_after (bits : List Bool) (initial : Bool → Payload) (j : Bool) :
    runCopies bits initial j = initial (j ^^ parity bits) := by
  induction bits generalizing initial with
  | nil => simp [runCopies, parity]
  | cons bit rest ih =>
    rw [runCopies, ih, copyStep, parity]
    cases j <;> cases bit <;> cases parity rest <;> rfl

theorem boolean_bank_invariant (bits : List Bool) (j : Bool) :
    runCopies bits id j = (j ^^ parity bits) := payload_after bits id j

theorem final_bank_zero (bits : List Bool) : runCopies bits id false = parity bits := by
  simp [boolean_bank_invariant]

/-- One synchronous round reads only the preceding buffer: the old value
    survives, or an incoming neighbor had been reached one round earlier. -/
def reached (edge : V → V → Prop) (roots : V → Prop) : Nat → V → Prop
  | 0, v => roots v
  | n + 1, v => reached edge roots n v ∨ ∃ u, edge u v ∧ reached edge roots n u

inductive Walk (edge : V → V → Prop) (roots : V → Prop) : Nat → V → Prop where
  | root {v} : roots v → Walk edge roots 0 v
  | step {n u v} : Walk edge roots n u → edge u v → Walk edge roots (n+1) v

/-- An arbitrary intermediate buffer field has intrinsic bounded-distance
    semantics, independent of the order in which fresh destinations were written. -/
theorem reached_iff_walk (edge : V → V → Prop) (roots : V → Prop) (n : Nat) (v : V) :
    reached edge roots n v ↔ ∃ m ≤ n, Walk edge roots m v := by
  constructor
  · induction n generalizing v with
    | zero => exact fun hv => ⟨0, Nat.le_refl _, Walk.root hv⟩
    | succ n ih =>
      intro hv
      rcases hv with old | ⟨u, huv, prev⟩
      · obtain ⟨m, hm, walk⟩ := ih v old
        exact ⟨m, Nat.le_trans hm (Nat.le_succ _), walk⟩
      · obtain ⟨m, hm, walk⟩ := ih u prev
        exact ⟨m+1, Nat.succ_le_succ hm, walk.step huv⟩
  · rintro ⟨m, hm, walk⟩
    have onTime : reached edge roots m v := by
      clear hm
      induction walk with
      | root h => exact h
      | step prev huv ih => exact Or.inr ⟨_, huv, ih⟩
    induction hm with
    | refl => exact onTime
    | step _ ih => exact Or.inl ih

/-- Transport both the graph and the selected roots through any surjective
    relation-preserving and relation-reflecting map. In particular it holds for
    a permutation without fixing the names of any interior vertices. -/
theorem reached_under_relabel (edge : V → V → Prop) (edge' : W → W → Prop)
    (roots : V → Prop) (roots' : W → Prop) (f : V → W) (onto : ∀ z, ∃ u, f u = z)
    (sameEdge : ∀ u v, edge u v ↔ edge' (f u) (f v))
    (sameRoot : ∀ u, roots u ↔ roots' (f u)) (n : Nat) (v : V) :
    reached edge roots n v ↔ reached edge' roots' n (f v) := by
  induction n generalizing v with
  | zero => exact sameRoot v
  | succ n ih =>
    constructor
    · intro hv
      rcases hv with old | ⟨u, huv, prev⟩
      · exact Or.inl ((ih v).mp old)
      · exact Or.inr ⟨f u, (sameEdge u v).mp huv, (ih u).mp prev⟩
    · intro hv
      rcases hv with old | ⟨z, hz, prev⟩
      · exact Or.inl ((ih v).mpr old)
      · obtain ⟨u, rfl⟩ := onto z
        exact Or.inr ⟨u, (sameEdge u v).mpr hz, (ih u).mpr prev⟩

/-- For a single named root and a named target, fixing those two labels leaves
    the target's reachability field unchanged at every round. -/
theorem fixed_endpoint_field (edge edge' : V → V → Prop) (f : V → V)
    (onto : ∀ z, ∃ u, f u = z) (injective : ∀ u v, f u = f v → u = v)
    (sameEdge : ∀ u v, edge u v ↔ edge' (f u) (f v))
    (root target : V) (hr : f root = root) (ht : f target = target) (n : Nat) :
    reached edge (· = root) n target ↔ reached edge' (· = root) n target := by
  have rootTest (v : V) : v = root ↔ f v = root := by
    constructor
    · rintro rfl; exact hr
    · intro eq; exact injective v root (eq.trans hr.symm)
  simpa only [ht] using reached_under_relabel edge edge' _ _ f onto sameEdge rootTest n target

#print axioms payload_after
#print axioms reached_iff_walk
#print axioms fixed_endpoint_field

end TokenCopyAndReachability
