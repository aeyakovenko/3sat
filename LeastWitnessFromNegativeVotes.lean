import Std

namespace LeastWitnessFromNegativeVotes

/-- The candidate's NO vote on the comparison "there is a smaller witness"
becomes part of an ordinary existential formula with distinguished input x. -/
def Slice (P voteNo : Nat → Prop) (x : Nat) : Prop := P x ∧ voteNo x

theorem slice_unique (P voteNo : Nat → Prop) (z : Nat) (witness : P z)
    (least : ∀ x, P x → z ≤ x) (rejects : voteNo z)
    (honest : ∀ x, voteNo x → ¬∃ y, P y ∧ y < x) :
    ∀ x, Slice P voteNo x ↔ x = z := by
  intro x
  constructor
  · rintro ⟨px,no⟩
    have lo := least _ px
    apply Classical.byContradiction
    intro h
    have lt : z < x := by omega
    exact honest x no ⟨z,witness,lt⟩
  · rintro rfl
    exact ⟨witness,rejects⟩

/-- Exact semantics of an outer comparison on a unique projection.
The right field symbol is the only symbol whose disequality query is UNSAT. -/
theorem disequality_query {X A V : Type} (S : X → Prop) (z : X)
    (single : ∀ x, S x ↔ x = z) (code : X → A → V) (a : A) (u : V) :
    (∃ x, S x ∧ code x a ≠ u) ↔ code z a ≠ u := by
  constructor
  · rintro ⟨x,mem,ne⟩
    rw [(single x).mp mem] at ne
    exact ne
  · intro ne
    exact ⟨z,(single z).mpr rfl,ne⟩

/-- A finite collection of lists, covering q distinct coordinates, has a
member with d or more coordinates if the other possible capacities sum to
less than q. Separate instances of this theorem allow separate inner and
outer rosters. -/
private theorem sum_cap {ss : List (List α)} {c : Nat} (bound : ∀ s ∈ ss, s.length ≤ c) :
    (ss.map List.length).sum ≤ ss.length*c := by
  induction ss with
  | nil => simp
  | cons a l ih =>
    have h := bound a (by simp)
    have tail := ih (fun s hs => bound s (by simp [hs]))
    simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Nat.add_le_add h tail

theorem covered_row {coordinates : List α} {rows : List (List α)} {d : Nat}
    (covered : coordinates.length ≤ (rows.map List.length).sum)
    (enough : rows.length*(d-1) < coordinates.length) :
    ∃ row ∈ rows, d ≤ row.length := by
  classical
  apply Classical.byContradiction
  intro bad
  have cap : ∀ s ∈ rows, s.length ≤ d-1 := by
    intro s hs
    apply Classical.byContradiction
    intro exceed
    exact bad ⟨s,hs,by omega⟩
  have beyond := sum_cap cap
  omega

/-- On an ordered code with d-coordinate interpolation, a negative-sound
voter who returns at least d symbols can only decode to the true word. -/
theorem recovered_word {X A V : Type} {S : X → Prop} {z : X}
    (single : ∀ x, S x ↔ x = z) {code : X → A → V} {no : A → V → Prop}
    (sound : ∀ a u, no a u → ¬∃ x, S x ∧ code x a ≠ u)
    {points : List A} {candidate : X}
    (fits : ∀ a ∈ points, no a (code candidate a))
    (uniqueCode : ∀ y, (∀ a ∈ points, code y a = code z a) → y = z) :
    candidate = z := by
  apply uniqueCode
  intro a ha
  have h := sound a (code candidate a) (fits a ha)
  apply Classical.byContradiction
  intro differ
  exact h ⟨z,(single z).mpr rfl,Ne.symm differ⟩

end LeastWitnessFromNegativeVotes
