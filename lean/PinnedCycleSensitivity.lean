import Std

namespace PinnedCycleSensitivity

/-- The first clause repeats the negated source, the second repeats the positive
    source. The two destination occurrences can refer to different values after
    a single name edit. A true edge sign asks for unequal endpoint bits. -/
def clausePair (source first second sign : Bool) : Bool :=
  ((!source || (first ^^ sign)) || !source) &&
  ((source || !(second ^^ sign)) || source)

theorem pair_encodes_xor (source target sign : Bool) :
    clausePair source target target sign = true ↔ (source ^^ target) = sign := by
  cases source <;> cases target <;> cases sign <;> decide

def editCritical (source old new sign : Bool) : Bool :=
  if source then clausePair source new old sign else clausePair source old new sign

theorem critical_name_edit (source old new sign : Bool) :
    editCritical source old new sign ≠ clausePair source old old sign ↔ old ≠ new := by
  cases source <;> cases old <;> cases new <;> cases sign <;> decide

theorem other_occurrence_inert (source old new sign : Bool) :
    (if source then clausePair source old new sign else clausePair source new old sign) =
    clausePair source old old sign := by
  cases source <;> cases old <;> cases new <;> cases sign <;> decide

private theorem same_discrepancy (u v p q : Bool) :
    (u ^^ v) = (p ^^ q) ↔ (u ^^ p) = (v ^^ q) := by
  cases u <;> cases v <;> cases p <;> cases q <;> decide

private theorem recover (x p d : Bool) (eq : (x ^^ p) = d) : x = (p ^^ d) := by
  revert eq
  cases x <;> cases p <;> cases d <;> decide

private theorem chain_eq (f : Nat → Bool) {a b : Nat} (ab : a ≤ b)
    (step : ∀ i, a ≤ i → i < b → f i = f (i+1)) : f a = f b := by
  induction b with
  | zero => have eq : a = 0 := by omega
            simp [eq]
  | succ b ih =>
    by_cases h : a ≤ b
    · exact (ih h (fun i lo hi => step i lo (by omega))).trans (step b h (by omega))
    · have eq : a = b+1 := by omega
      simp [eq]

/-- Vertices 0 and last are the pinned endpoints. Delete the edge from j to
    j+1. Every intact edge preserves its endpoints' Boolean discrepancy from
    the reference pattern p. The left endpoint has discrepancy d and the
    right endpoint has discrepancy zero. -/
def cutAssignment (p : Nat → Bool) (j : Nat) (d : Bool) (i : Nat) : Bool :=
  p i ^^ (d && decide (i ≤ j))

theorem pins_and_edges (p : Nat → Bool) (d : Bool) {j last : Nat} (inside : j < last) :
    cutAssignment p j d 0 = (p 0 ^^ d) ∧
    cutAssignment p j d last = p last ∧
    ∀ i, i < last → i ≠ j →
      (cutAssignment p j d i ^^ cutAssignment p j d (i+1)) = (p i ^^ p (i+1)) := by
  refine ⟨by simp [cutAssignment], by simp [cutAssignment, Nat.not_le_of_lt inside], ?_⟩
  intro i _ skip
  have cut : (i ≤ j) = (i+1 ≤ j) := propext (by omega)
  rw [same_discrepancy]
  simp only [cutAssignment, cut]
  cases p i <;> cases p (i+1) <;> cases (d && decide (i+1 ≤ j)) <;> decide

theorem unique_with_edge_removed (p q : Nat → Bool) (d : Bool) {j last : Nat}
    (inside : j < last) (left : q 0 = (p 0 ^^ d)) (right : q last = p last)
    (adj : ∀ i, i < last → i ≠ j → (q i ^^ q (i+1)) = (p i ^^ p (i+1)))
    (i : Nat) (atVertex : i ≤ last) : q i = cutAssignment p j d i := by
  let discrepancy := fun h => q h ^^ p h
  have edge (h : Nat) (before : h < last) (skip : h ≠ j) :
      discrepancy h = discrepancy (h+1) := (same_discrepancy ..).mp (adj h before skip)
  by_cases onLeft : i ≤ j
  · have eq := chain_eq discrepancy (a := 0) (b := i) (by omega)
        (fun h _ hi => edge h (by omega) (by omega))
    have initial : discrepancy 0 = d := by
      simp only [discrepancy, left]
      cases p 0 <;> cases d <;> decide
    simpa [cutAssignment, onLeft] using recover (q i) (p i) d (eq.symm.trans initial)
  · have eq := chain_eq discrepancy (a := i) (b := last) atVertex
        (fun h lo hi => edge h hi (by omega))
    have terminal : discrepancy last = false := by simp [discrepancy, right]
    simpa [cutAssignment, onLeft] using recover (q i) (p i) false (eq.trans terminal)

/-- Putting the missing pair back agrees with the two endpoint pins exactly
    when their discrepancy is zero. -/
theorem removed_pair_value (p : Nat → Bool) (d : Bool) (j : Nat) :
    clausePair (cutAssignment p j d j) (cutAssignment p j d (j+1))
      (cutAssignment p j d (j+1)) (p j ^^ p (j+1)) = !d := by
  have step : ¬ j+1 ≤ j := by omega
  simp only [cutAssignment, Nat.le_refl, decide_true, Bool.and_true, step, decide_false,
    Bool.and_false, Bool.xor_false]
  cases p j <;> cases p (j+1) <;> cases d <;> decide

/-- Logical vertex of rank r is path vertex r+1. -/
def negativeValue (parity : Bool) (r cut : Nat) : Bool := parity ^^ decide (r < cut)

theorem negative_rank_value (p : Nat → Bool) (r j : Nat) :
    cutAssignment p j true (r+1) = negativeValue (p (r+1)) r j := by
  have order : (r+1 ≤ j) = (r < j) := propext (by omega)
  simp [cutAssignment, negativeValue, order]

theorem sensitive_toward_later {j r : Nat} (distinct : j ≠ r) (y z : Bool)
    (neighbors : y ≠ z) :
    negativeValue y j j ≠ negativeValue z r j ↔ j < r := by
  by_cases before : r < j
  · have notAfter : ¬ j < r := by omega
    cases y <;> cases z <;> simp_all [negativeValue]
  · have after : j < r := by omega
    cases y <;> cases z <;> simp_all [negativeValue]

structure Vertex where
  rank : Nat
  parity : Bool

def sensitive (u v : Vertex) : Bool :=
  decide (negativeValue u.parity u.rank u.rank ≠ negativeValue v.parity v.rank u.rank)

/-- Each listed unordered opposite-parity neighbor pair has exactly one
    sensitive orientation, whichever orientation was used to list the edge. -/
theorem count_orientations (edges : List (Vertex × Vertex))
    (neighbors : ∀ e ∈ edges, e.1.rank ≠ e.2.rank ∧ e.1.parity ≠ e.2.parity) :
    edges.countP (fun e => sensitive e.1 e.2) +
    edges.countP (fun e => sensitive e.2 e.1) = edges.length := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
    have ⟨distinct, differ⟩ := neighbors e (by simp)
    have rest := ih (fun p hp => neighbors p (by simp [hp]))
    have forward := sensitive_toward_later distinct _ _ differ
    have backward := sensitive_toward_later (Ne.symm distinct) _ _ (Ne.symm differ)
    by_cases order : e.1.rank < e.2.rank
    · have noReverse : ¬ e.2.rank < e.1.rank := by omega
      simp [List.countP_cons, sensitive, forward, backward, order, noReverse] at *
      omega
    · have reverse : e.2.rank < e.1.rank := by omega
      simp [List.countP_cons, sensitive, forward, backward, order, reverse] at *
      omega

end PinnedCycleSensitivity
