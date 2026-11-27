import Std

/-! For one memory address, block i contributes its last local write, or
none if the block made no write to that address. A reader's history ends
immediately before its own block. -/

namespace CrossBlockProducers

def carry (initial : Word) : List (Option Word) → Word
  | [] => initial
  | value :: tail => carry (value.getD initial) tail

def wrote : List (Option Word) → Nat → Word → Prop
  | [], _, _ => False
  | value :: _, 0, word => value = some word
  | _ :: tail, i+1, word => wrote tail i word

def noWrites (blocks : List (Option Word)) : Prop :=
  ∀ i word, ¬ wrote blocks i word

/-- None denotes initialized memory; some j names the last prior writing
block. A strictly later block invalidates j even if it wrote the same word. -/
def validProducer (initial : Word) (blocks : List (Option Word))
    (producer : Option Nat) (value : Word) : Prop :=
  match producer with
  | none => value = initial ∧ noWrites blocks
  | some j => wrote blocks j value ∧ ∀ i word, j < i → ¬ wrote blocks i word

theorem wroteWithin {blocks : List (Option Word)} {i : Nat} {word : Word}
    (hw : wrote blocks i word) : i < blocks.length := by
  induction blocks generalizing i with
  | nil => exact False.elim hw
  | cons head tail ih =>
    cases i with
    | zero => simp
    | succ i =>
      have ht : i < tail.length := ih hw
      simp only [List.length_cons]
      omega

theorem carryUnwritten (initial : Word) (blocks : List (Option Word))
    (hn : noWrites blocks) : carry initial blocks = initial := by
  induction blocks generalizing initial with
  | nil => rfl
  | cons head tail ih =>
    have hnTail : noWrites tail := fun i w => hn (i+1) w
    cases head with
    | none => exact ih initial hnTail
    | some w => exact False.elim (hn 0 w rfl)

theorem carryFromLast (initial : Word) (blocks : List (Option Word)) {j : Nat} {v : Word}
    (hw : wrote blocks j v) (hlast : ∀ i w, j < i → ¬ wrote blocks i w) :
    carry initial blocks = v := by
  induction blocks generalizing initial j with
  | nil => exact False.elim hw
  | cons head tail ih =>
    cases j with
    | zero =>
      have heq : head = some v := hw
      subst head
      exact carryUnwritten v tail (fun i w => hlast (i+1) w (by omega))
    | succ j =>
      exact ih (head.getD initial) hw
        (fun i w hi => hlast (i+1) w (by omega))

theorem producerSound {initial : Word} {blocks : List (Option Word)} {who : Option Nat}
    {v : Word} (h : validProducer initial blocks who v) : carry initial blocks = v := by
  cases who with
  | none => exact (carryUnwritten initial blocks h.2).trans h.1.symm
  | some j => exact carryFromLast initial blocks h.1 h.2

/-- Every genuine carry has a predecessor satisfying both the value check
and every exclusion of a later write. -/
theorem producerComplete (initial : Word) (blocks : List (Option Word)) :
    ∃ who, validProducer initial blocks who (carry initial blocks) := by
  induction blocks generalizing initial with
  | nil => exact ⟨none, rfl, fun _ _ hw => hw⟩
  | cons head tail ih =>
    obtain ⟨who, cert⟩ := ih (head.getD initial)
    cases who with
    | some j =>
      refine ⟨some (j+1), cert.1, ?_⟩
      intro k w hlt
      cases k with
      | zero => omega
      | succ k => exact cert.2 k w (by omega)
    | none =>
      obtain ⟨hcarry, hnone⟩ := cert
      cases head with
      | none =>
        refine ⟨none, hcarry, ?_⟩
        intro i w hw
        cases i with
        | zero => cases hw
        | succ i => exact hnone i w hw
      | some w =>
        refine ⟨some 0, ?_, ?_⟩
        · change some w = some (carry w tail)
          exact congrArg some hcarry.symm
        · intro i v hpos
          cases i with
          | zero => omega
          | succ i => exact hnone i v

/-- The reader sees exactly the unmodified write history of earlier blocks. -/
theorem beforeReadIff (initial : Word) (blocks : List (Option Word)) (reader : Nat)
    (value : Word) :
    (∃ who, validProducer initial (blocks.take reader) who value) ↔
      carry initial (blocks.take reader) = value := by
  constructor
  · rintro ⟨who, h⟩
    exact producerSound h
  · intro h
    rw [← h]
    exact producerComplete initial _

/-- For a value-only observation the challenger may supply the producer.
Its last write must disagree, or memory must still have a different initial
value. Taking the strict prefix prevents writes at the consumer or later
from affecting the test. -/
theorem wrongValueBeforeReadIff (initial observed : Word) (blocks : List (Option Word))
    (reader : Nat) :
    let prior := blocks.take reader
    carry initial prior ≠ observed ↔
      (∃ j v, wrote prior j v ∧ v ≠ observed ∧
        ∀ i w, j < i → ¬ wrote prior i w) ∨
      (initial ≠ observed ∧ noWrites prior) := by
  dsimp only
  let prior := blocks.take reader
  constructor
  · intro wrong
    obtain ⟨producer, cert⟩ := producerComplete initial prior
    cases producer with
    | none =>
      exact Or.inr ⟨fun heq => wrong (cert.1.trans heq), cert.2⟩
    | some j =>
      exact Or.inl ⟨j, carry initial prior, cert.1, wrong, cert.2⟩
  · rintro (⟨j, v, wroteValue, mismatch, last⟩ | ⟨mismatch, untouched⟩)
    · rw [carryFromLast initial prior wroteValue last]
      exact mismatch
    · rw [carryUnwritten initial prior untouched]
      exact mismatch

/-- Exponents relative to the source clock H. The virtual formula has
H L^3 encoded bits. Q counts public producer records of a constant number
of words; the explicit final reduction charges L^(a+2) per public word.
The local replay pays one logarithm and its reduction costs L^(a+3)
per step. The choice P=L^(2a+8) makes both work exponents -1. -/
theorem wordCost (a : Int) :
    3-(a+6)+(a+2) = -1 ∧
    (a+3)-(2*a+8)+1+(a+3) = -1 := by omega

end CrossBlockProducers
