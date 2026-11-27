import Std

namespace TranscriptFiberWeights

/-- A verifier with one visible challenge and a hidden tape. -/
theorem hidden_tape_last {Tape Message Reply : Type}
    (visible : Tape → Message) (accept : Tape → Reply → Prop) :
    (∀ m, ∃ reply, ∀ tape, visible tape = m → accept tape reply) ↔
      ∃ strategy : Message → Reply, ∀ tape, accept tape (strategy (visible tape)) := by
  constructor
  · intro h
    exact ⟨fun m => Classical.choose (h m), fun tape =>
      Classical.choose_spec (h (visible tape)) tape rfl⟩
  · rintro ⟨strategy, wins⟩ m
    refine ⟨strategy m, ?_⟩
    intro tape sameMessage
    simpa [← sameMessage] using wins tape

/-- Count the positive indices at most the cap accepted by a total comparator. -/
def acceptedUpTo (test : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => acceptedUpTo test n + (if test (n+1) then 1 else 0)

theorem threshold_count (test : Nat → Bool) (low high cap : Nat)
    (yes : ∀ j, 0 < j → j ≤ low → test j = true)
    (no : ∀ j, high < j → test j = false) :
    min low cap ≤ acceptedUpTo test cap ∧ acceptedUpTo test cap ≤ min high cap := by
  induction cap with
  | zero => simp [acceptedUpTo]
  | succ n ih =>
    simp only [acceptedUpTo]
    cases ht : test (n+1) with
    | false =>
      have hl : low < n+1 := by
        apply Nat.lt_of_not_ge
        intro bad
        have := yes (n+1) (by omega) bad
        simp [ht] at this
      simp
      omega
    | true =>
      have hh : n+1 ≤ high := by
        apply Nat.le_of_not_lt
        intro bad
        have := no (n+1) bad
        simp [ht] at this
      simp
      omega

/-- Verifier messages partition the compatible tapes. Multiplicative bounds
    survive the sum over all children, represented without rounding by p/q. -/
theorem sum_children {H : Type} (children : List H) (exactCount estimated : H → Nat)
    (p q : Nat)
    (lo : ∀ h ∈ children, exactCount h ≤ estimated h)
    (hi : ∀ h ∈ children, q * estimated h ≤ p * exactCount h) :
    (children.map exactCount).sum ≤ (children.map estimated).sum ∧
    q * (children.map estimated).sum ≤ p * (children.map exactCount).sum := by
  induction children with
  | nil => simp
  | cons h tail ih =>
    obtain ⟨lower, upper⟩ := ih
      (fun x hx => lo x (List.mem_cons_of_mem h hx))
      (fun x hx => hi x (List.mem_cons_of_mem h hx))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    exact ⟨Nat.add_le_add (lo h (by simp)) lower, Nat.add_le_add (hi h (by simp)) upper⟩

/-- At a prover node, a child witnessing the threshold can always be chosen
    consistently from the public history. -/
theorem max_children {H : Type} (weight : H → Nat) (test : H → Nat → Prop)
    (j p q : Nat) (lo : ∀ h, j ≤ weight h → test h j)
    (hi : ∀ h, test h j → j * q ≤ p * weight h) :
    ((∃ h, j ≤ weight h) → ∃ h, test h j) ∧
    ((∃ h, test h j) → ∃ h, j*q ≤ p*weight h) := by
  constructor
  · rintro ⟨h, hj⟩
    exact ⟨h, lo h hj⟩
  · rintro ⟨h, hj⟩
    exact ⟨h, hi h hj⟩

end TranscriptFiberWeights
