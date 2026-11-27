import Std

/-! The history for a read is the strict prefix, newest entry first.
An event identity includes its native time and its within-step slot. -/

namespace DisclosedWriterMatching

structure Write (Addr Word : Type) where
  time : Nat
  slot : Nat
  address : Addr
  value : Word

variable {Addr Word : Type} [DecidableEq Addr]

def latest (address : Addr) (disclosed : Write Addr Word → Bool) :
    List (Write Addr Word) → Option (Write Addr Word)
  | [] => none
  | p :: rest =>
    if p.address = address then
      if disclosed p then some p else latest address disclosed rest
    else latest address disclosed rest

/-- Restricting the public directory preserves initialized reads and
preserves the most recent writer whenever that particular event was disclosed. -/
theorem latestWhenDisclosed (a : Addr) (known : Write Addr Word → Bool)
    (history : List (Write Addr Word)) :
    match latest a (fun _ => true) history with
    | none => latest a known history = none
    | some p => known p = true → latest a known history = some p := by
  induction history with
  | nil => rfl
  | cons head rest ih =>
    by_cases atAddress : head.address = a
    · simp only [latest, if_pos atAddress, ↓reduceIte]
      intro disclosed
      simp [disclosed]
    · simpa only [latest, if_neg atAddress] using ih

private theorem latestAddress (a : Addr) (known : Write Addr Word → Bool)
    (history : List (Write Addr Word)) (p : Write Addr Word)
    (hit : latest a known history = some p) : p.address = a ∧ p ∈ history := by
  induction history with
  | nil => simp [latest] at hit
  | cons head rest ih =>
    by_cases atAddress : head.address = a
    · by_cases disclosed : known head = true
      · simp [latest, atAddress, disclosed] at hit
        subst p
        exact ⟨atAddress, List.mem_cons_self⟩
      · simp [latest, atAddress, disclosed] at hit
        obtain ⟨addr, member⟩ := ih hit
        exact ⟨addr, List.mem_cons_of_mem head member⟩
    · simp [latest, atAddress] at hit
      obtain ⟨addr, member⟩ := ih hit
      exact ⟨addr, List.mem_cons_of_mem head member⟩

def observedBit (initial : Word) (bit : Word → Bool) :
    Option (Write Addr Word) → Bool
  | none => bit initial
  | some p => bit p.value

/-- A bit disagreement certifies a genuine, previously undisclosed
producer at the requested address, even when the initialized bit is one. -/
theorem mismatchHasFreshWriter (a : Addr) (known : Write Addr Word → Bool)
    (history : List (Write Addr Word)) (initial : Word) (bit : Word → Bool)
    (wrong : observedBit initial bit (latest a known history) ≠
      observedBit initial bit (latest a (fun _ => true) history)) :
    ∃ p, latest a (fun _ => true) history = some p ∧
      p.address = a ∧ p ∈ history ∧ known p = false := by
  have preserved := latestWhenDisclosed a known history
  cases genuine : latest a (fun _ => true) history with
  | none =>
    rw [genuine] at preserved wrong
    exact False.elim (wrong (congrArg (observedBit initial bit) preserved))
  | some p =>
    rw [genuine] at preserved wrong
    obtain ⟨addr, member⟩ := latestAddress a (fun _ => true) history p genuine
    refine ⟨p, rfl, addr, member, ?_⟩
    cases disclosed : known p with
    | false => rfl
    | true =>
      exact False.elim (wrong (congrArg (observedBit initial bit) (preserved disclosed)))

omit [DecidableEq Addr] in
/-- Within a selected slice, error queries have distinct addresses. After
each round its true writers are disclosed to every later round. Consequently
the assigned writers are pairwise distinct over the whole collection. -/
theorem differentReadsHaveDifferentWriters {Read : Type}
    (round : Read → Nat) (address : Read → Addr) (writer : Read → Write Addr Word)
    (known : Nat → Write Addr Word → Bool)
    (atAddress : ∀ r, (writer r).address = address r)
    (fresh : ∀ r, known (round r) (writer r) = false)
    (later : ∀ r i, round r < i → known i (writer r) = true)
    (unique : ∀ r s, round r = round s → address r = address s → r = s)
    (r s : Read) (same : writer r = writer s) : r = s := by
  have excludeEarlier (x y : Read) (eqWriter : writer x = writer y) :
      ¬ round x < round y := by
    intro lt
    have yes := later x (round y) lt
    rw [eqWriter, fresh] at yes
    cases yes
  have ha := excludeEarlier r s same
  have hb := excludeEarlier s r same.symm
  apply unique r s (by omega)
  exact (atAddress r).symm.trans ((congrArg Write.address same).trans (atAddress s))

/-- A window of w hard starts avoids the expanded region of already
covered starts [u-2w,u+3w). Thus the two windows' whole forward ranges
[u,u+3w) and [v,v+3w) are disjoint. The first inequality below expresses
the left endpoint without truncated subtraction. -/
theorem disjointForwardRanges (u v w : Nat) (hw : 0 < w)
    (avoids : ∀ s, v ≤ s → s < v+w → s+2*w < u ∨ u+3*w ≤ s) :
    v+3*w ≤ u ∨ u+3*w ≤ v := by
  by_cases right : u+3*w ≤ v
  · exact Or.inr right
  · left
    apply Classical.byContradiction
    intro overlap
    let s := max v (u-2*w)
    have hs := avoids s (Nat.le_max_left _ _) (by simp [s] <;> omega)
    simp [s] at hs
    omega

end DisclosedWriterMatching
