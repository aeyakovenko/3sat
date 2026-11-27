import Std

namespace DenseProjectionBothClocks

/-- A state includes all ordinary work memory. An original-file probe asks
    only for the initial word at its address. -/
inductive Action (State Addr Word : Type) where
  | halt (b : Bool)
  | next (s : State)
  | read (a : Addr) (resume : Word → State)

variable {State Addr Word Edit : Type} [DecidableEq Word]
variable (step : State → Action State Addr Word)

def atClock (input : Addr → Word) : Nat → State → Option Bool
  | 0, _ => none
  | t+1, s =>
    match step s with
    | .halt b => some b
    | .next s' => atClock input t s'
    | .read a resume => atClock input t (resume (input a))

private theorem lengths_split (f : Edit → Bool) (xs : List Edit) :
    (xs.filter f).length + (xs.filter (fun z => !(f z))).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : f x <;> simp [List.filter_cons, h] at * <;> omega

/-- After any deadline t at which b*t is below the number of edits,
    some edited oracle has exactly the base verdict or timeout at that deadline.
    The multiplicity premise is required only on subsets of the supplied list. -/
theorem some_edit_same_clock (base : Addr → Word) (alt : Edit → Addr → Word)
    (b : Nat) (candidates : List Edit)
    (hitBound : ∀ (xs : List Edit), xs.Sublist candidates → ∀ a,
      (xs.filter (fun z => decide (alt z a ≠ base a))).length ≤ b)
    (t : Nat) (s : State) (enough : b*t < candidates.length) :
    ∃ z ∈ candidates, atClock step (alt z) t s = atClock step base t s := by
  induction t generalizing s candidates with
  | zero =>
    cases candidates with
    | nil => simp at enough
    | cons z xs => exact ⟨z, by simp, rfl⟩
  | succ t ih =>
    cases op : step s with
    | halt result =>
      cases candidates with
      | nil => simp at enough
      | cons z xs => exact ⟨z, by simp, by simp [atClock, op]⟩
    | next s' =>
      obtain ⟨z,hz,heq⟩ := ih candidates hitBound s' (by rw [Nat.mul_succ] at enough; omega)
      exact ⟨z,hz,by simpa [atClock, op] using heq⟩
    | read a resume =>
      let survives := fun z => decide (alt z a = base a)
      let ys := candidates.filter survives
      have sub : ys.Sublist candidates := List.filter_sublist
      have drop := hitBound candidates (List.Sublist.refl _) a
      have split := lengths_split survives candidates
      have remaining : b*t < ys.length := by
        have neg : (fun z => !(survives z)) = (fun z => decide (alt z a ≠ base a)) := by
          funext z
          by_cases e : alt z a = base a <;> simp [survives, e]
        rw [neg] at split
        change ys.length + (candidates.filter (fun z => decide (alt z a ≠ base a))).length = candidates.length at split
        rw [Nat.mul_succ] at enough
        omega
      obtain ⟨z,hz,heq⟩ := ih ys (fun xs h => hitBound xs (h.trans sub))
        (resume (base a)) remaining
      obtain ⟨belongs,agrees⟩ := List.mem_filter.mp hz
      have same : alt z a = base a := of_decide_eq_true agrees
      exact ⟨z,belongs,by simpa [atClock, op, same] using heq⟩

/-- A sound base rejection and sound affirmative edits must both have a
    timeout at every such small clock if each has a different valid verdict. -/
theorem two_timeouts (base : Addr → Word) (alt : Edit → Addr → Word)
    (b : Nat) (edits : List Edit) (t : Nat) (s : State)
    (hitBound : ∀ (xs : List Edit), xs.Sublist edits → ∀ a,
      (xs.filter (fun z => decide (alt z a ≠ base a))).length ≤ b)
    (enough : b*t < edits.length)
    (baseSound : atClock step base t s ≠ some true)
    (editSound : ∀ z ∈ edits, atClock step (alt z) t s ≠ some false) :
    atClock step base t s = none ∧ ∃ z ∈ edits, atClock step (alt z) t s = none := by
  obtain ⟨z,hz,same⟩ := some_edit_same_clock step base alt b edits hitBound t s enough
  cases out : atClock step base t s with
  | none => exact ⟨rfl, z, hz, same.trans out⟩
  | some v =>
    cases v with
    | false => exact False.elim (editSound z hz (same.trans out))
    | true => exact False.elim (baseSound out)

end DenseProjectionBothClocks
