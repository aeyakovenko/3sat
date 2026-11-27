import SupportedWordTransition

namespace AlternatingLastWrite

/-- A read at a fixed address sees the preload at stamp 0.
    A store at native slot i has stamp i+1. -/
structure History (Addr Word : Type) where
  initial : Addr → Word
  store : Nat → Option (Addr × Word)

def cellStore {Addr Word : Type} [DecidableEq Addr] (H : History Addr Word)
    (a : Addr) (i : Nat) : Option Word :=
  match H.store i with
  | none => none
  | some (b, w) => if b = a then some w else none

def record {Addr Word : Type} [DecidableEq Addr] (H : History Addr Word)
    (a : Addr) : Nat → Option Word
  | 0 => some (H.initial a)
  | i+1 => cellStore H a i

/-- The latest stamp and the delivered word after the first t native store slots. -/
def last {Addr Word : Type} [DecidableEq Addr] (H : History Addr Word) (a : Addr) :
    Nat → Nat × Word
  | 0 => (0, H.initial a)
  | i+1 =>
    match cellStore H a i with
    | some value => (i+1, value)
    | none => last H a i

theorem last_spec {Addr Word : Type} [DecidableEq Addr] (H : History Addr Word)
    (a : Addr) (t : Nat) :
    (last H a t).1 ≤ t ∧ record H a (last H a t).1 = some (last H a t).2 := by
  induction t with
  | zero => simp [last, record]
  | succ t ih =>
    cases h : cellStore H a t with
    | none => simpa [last, h] using And.intro (Nat.le_succ_of_le ih.1) ih.2
    | some w => simp [last, record, h]

theorem stamp_ge_of_record {Addr Word : Type} [DecidableEq Addr] (H : History Addr Word)
    (a : Addr) {s t : Nat} {w : Word} (st : s ≤ t) (hit : record H a s = some w) :
    s ≤ (last H a t).1 := by
  induction t with
  | zero => simp [show s = 0 by omega, last]
  | succ t ih =>
    cases he : cellStore H a t with
    | some z => simpa [last, he] using st
    | none =>
      have earlier : s ≤ t := by
        apply Classical.byContradiction
        intro hn
        have eq : s = t + 1 := by omega
        simp [eq, record, he] at hit
      simpa [last, he] using ih earlier

/-- A matching write (or preload) followed by a different return must have been overwritten. -/
theorem stamp_lt_of_different_read {Addr Word : Type} [DecidableEq Addr] (H : History Addr Word)
    (a : Addr) {s t : Nat} {w : Word} (st : s ≤ t) (hit : record H a s = some w)
    (different : w ≠ (last H a t).2) : s < (last H a t).1 := by
  have weak := stamp_ge_of_record H a st hit
  have neq : s ≠ (last H a t).1 := by
    intro eq
    rw [eq, (last_spec H a t).2] at hit
    exact different (Option.some.inj hit).symm
  omega

/-- Configurations describe a pair of current labeled histories. A transfer may
    replace BOTH histories, keeping their individual delivered values and reproducing
    one selected earlier write on the opposite side at the same numerical stamp.
    It need not preserve either history beyond that stamp. -/
theorem read_agree_of_alternating_transfer {State Addr Word : Type} [DecidableEq Addr]
    (history : State → Bool → History Addr Word) (a : Addr) (t : Nat)
    (transfer : ∀ x side s w, s ≤ t → record (history x side) a s = some w →
      ∃ y, (∀ b, (last (history y b) a t).2 = (last (history x b) a t).2) ∧
        record (history y (!side)) a s = some w) (x : State) :
    (last (history x false) a t).2 = (last (history x true) a t).2 := by
  have clash (r : Nat) : ∀ (z : State) (side : Bool),
      t - (last (history z side) a t).1 = r →
      (last (history z side) a t).2 ≠ (last (history z (!side)) a t).2 → False := by
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro z side rank bad
      obtain ⟨le, hit⟩ := last_spec (history z side) a t
      obtain ⟨z', keep, copied⟩ := transfer z side _ _ le hit
      have unequal : (last (history z side) a t).2 ≠ (last (history z' (!side)) a t).2 := by
        rw [keep (!side)]
        exact bad
      have later := stamp_lt_of_different_read (history z' (!side)) a le copied unequal
      have bound := (last_spec (history z' (!side)) a t).1
      apply ih (t - (last (history z' (!side)) a t).1) (by omega) z' (!side) rfl
      simpa [keep, Bool.not_not] using Ne.symm bad
  exact Classical.byContradiction fun bad => clash _ x false rfl bad

#print axioms stamp_lt_of_different_read
#print axioms read_agree_of_alternating_transfer

end AlternatingLastWrite

namespace AlternatingLastWrite

open SupportedWordTransition

private theorem agree_trans {A : Type} {s : Finset A} {p q r : Equiv.Perm A}
    (a : Agree s p q) (b : Agree s q r) : Agree s p r :=
  fun i hi => (a i hi).trans (b i hi)

/-- Align one earlier event and keep the *numerical labels* already pinned on u.
    Its support on the opposite side is chosen after the first relabeling. -/
theorem align_earlier_record {A : Type} [DecidableEq A] {k h : Nat} (G : PartialGame A k)
    {u : Finset A} (room : u.card + h + h ≤ k)
    (X Y : Equiv.Perm A → Prop)
    (sX : ∀ p, ∃ l : Finset A, l.card ≤ h ∧ LocallySupports X p l)
    (sY : ∀ q, ∃ r : Finset A, r.card ≤ h ∧ LocallySupports Y q r)
    (ih : ∀ p q l r, l.card ≤ h → r.card ≤ h → LocallySupports X p l →
      LocallySupports Y q r → G.aligned (l ∪ r) p q → X p → Y q)
    {p q : Equiv.Perm A} (aligned : G.aligned u p q) (hit : X p) :
    ∃ p' q', Agree u p p' ∧ Agree u q q' ∧ G.aligned u p' q' ∧ X p' ∧ Y q' := by
  obtain ⟨l, lc, ls⟩ := sX p
  have cu := Finset.card_union_le u l
  obtain ⟨q', aq, wq⟩ := G.alignForth (t := u ∪ l) Finset.subset_union_left (by omega) aligned
  obtain ⟨r, rc, rs⟩ := sY q'
  have cz := Finset.card_union_le (u ∪ l) r
  obtain ⟨p', ap, win⟩ := G.alignBack (t := (u ∪ l) ∪ r) Finset.subset_union_left (by omega) wq
  have al : Agree l p p' := fun i hi => ap i (Finset.mem_union_right _ hi)
  have ls' : LocallySupports X p' l := fun v hv =>
    (ls p' al).symm.trans (ls v (agree_trans al hv))
  have keep : X p' := (ls p' al).mp hit
  have support_subset : l ∪ r ⊆ (u ∪ l) ∪ r :=
    Finset.union_subset_union Finset.subset_union_right (Finset.Subset.refl _)
  have pins_subset : u ⊆ (u ∪ l) ∪ r := Finset.subset_union_left.trans Finset.subset_union_left
  have we := G.forget support_subset (naming _ p') (naming _ q') win
  have wu := G.forget pins_subset (naming _ p') (naming _ q') win
  exact ⟨p', q', fun i hi => ap i (Finset.mem_union_left _ hi), aq, wu, keep,
    ih p' q' l r lc rc ls' rs we keep⟩

/-- Induction hypotheses for earlier real store records and the virtual initial
    value are enough for the new read. The address and read stage are fixed.
    The two read supports may equivalently be pinned together in one set u. -/
theorem read_agree_in_partial_game {A Addr Word : Type} [DecidableEq A] [DecidableEq Addr]
    {k h : Nat} (G : PartialGame A k) (X Y : Equiv.Perm A → History Addr Word)
    (a : Addr) (t : Nat) (u : Finset A) (room : u.card + h + h ≤ k)
    (p q : Equiv.Perm A) (start : G.aligned u p q)
    (pinX : ∀ p', Agree u p p' → (last (X p') a t).2 = (last (X p) a t).2)
    (pinY : ∀ q', Agree u q q' → (last (Y q') a t).2 = (last (Y q) a t).2)
    (locX : ∀ s, s ≤ t → ∀ d p', ∃ l : Finset A, l.card ≤ h ∧
      LocallySupports (fun i => record (X i) a s = some d) p' l)
    (locY : ∀ s, s ≤ t → ∀ d q', ∃ r : Finset A, r.card ≤ h ∧
      LocallySupports (fun i => record (Y i) a s = some d) q' r)
    (earlier : ∀ s, s ≤ t → ∀ d p' q' l r, l.card ≤ h → r.card ≤ h →
      LocallySupports (fun i => record (X i) a s = some d) p' l →
      LocallySupports (fun i => record (Y i) a s = some d) q' r →
      G.aligned (l ∪ r) p' q' → (record (X p') a s = some d ↔ record (Y q') a s = some d)) :
    (last (X p) a t).2 = (last (Y q) a t).2 := by
  let State := {z : Equiv.Perm A × Equiv.Perm A //
    Agree u p z.1 ∧ Agree u q z.2 ∧ G.aligned u z.1 z.2}
  let hist (z : State) (side : Bool) := if side then Y z.val.2 else X z.val.1
  have pins (z z' : State) : ∀ b,
      (last (hist z' b) a t).2 = (last (hist z b) a t).2 := by
    intro b
    cases b with
    | false => exact (pinX _ z'.property.1).trans (pinX _ z.property.1).symm
    | true => exact (pinY _ z'.property.2.1).trans (pinY _ z.property.2.1).symm
  let init : State := ⟨(p,q), fun _ _ => rfl, fun _ _ => rfl, start⟩
  apply read_agree_of_alternating_transfer hist a t _ init
  intro z side s d st hit
  cases side with
  | false =>
    obtain ⟨p', q', ap, aq, win, _, yes⟩ := align_earlier_record G room _ _
      (locX s st d) (locY s st d)
      (fun i j l r lc rc ls rs w => (earlier s st d i j l r lc rc ls rs w).mp)
      z.property.2.2 hit
    let z' : State := ⟨(p',q'), agree_trans z.property.1 ap,
      agree_trans z.property.2.1 aq, win⟩
    exact ⟨z', pins z z', yes⟩
  | true =>
    obtain ⟨q', p', aq, ap, win, _, yes⟩ := align_earlier_record G.flip room _ _
      (locY s st d) (locX s st d)
      (fun j i r l rc lc rs ls w => (earlier s st d i j l r lc rc ls rs (by
        rw [Finset.union_comm]
        exact w)).mpr)
      z.property.2.2 hit
    let z' : State := ⟨(p',q'), agree_trans z.property.1 ap,
      agree_trans z.property.2.1 aq, win⟩
    exact ⟨z', pins z z', yes⟩

#print axioms align_earlier_record
#print axioms read_agree_in_partial_game

end AlternatingLastWrite
